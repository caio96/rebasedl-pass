#include "RebaseDL.h"
#include <algorithm>
#include <llvm/ADT/SetOperations.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/BlockFrequencyInfo.h>
#include <llvm/Analysis/GlobalsModRef.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Scalar/IndVarSimplify.h>
#include <llvm/Transforms/Scalar/LoopRotation.h>
#include <llvm/Transforms/Scalar/LICM.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>

using namespace llvm;

inline uint64_t ceilDiv(uint64_t numerator, uint64_t denominator) {
  return (numerator / denominator + (numerator % denominator != 0));
}

template <class S1Ty, class S2Ty>
static bool hasIntersection(S1Ty S1, S2Ty S2) {
  for (typename S1Ty::iterator I = S1.begin(); I != S1.end(); ++I) {
    if (S2.count(*I) != 0)
      return true;
  }
  return false;
}

template <typename T> SmallVector<T *> getInstructions(Loop *L) {
  SmallVector<T *> instructions;
  for (auto *BB : L->getBlocks()) {
    for (Instruction &I : *BB) {
      if (auto *instWithTypeT = dyn_cast<T>(&I)) {
        instructions.push_back(instWithTypeT);
      }
    }
  }
  return instructions;
}

SmallSet<Value *,4> getPtrsUsedInLoop(Loop *loop) {
  SmallSet<Value *, 4> ptrs;
  for (BasicBlock *BB : loop->getBlocks()) {
    for (Instruction &I : *BB) {
      for (auto &operand : I.operands()) {
        if (operand->getType()->isPointerTy()) {
          ptrs.insert(operand);
        }
      }
    }
  }
  return ptrs;
}

// Based on Value.cpp
//
// Accumulate the constant offset this value has compared to a base pointer.
// Only 'getelementptr' instructions (GEPs) are accumulated but other
// instructions, e.g., casts, are stripped away as well.
// The accumulated constant offset is added to \p Offset and the base
// pointer is returned.
//
// While accumulating the offsets, GEPs are saved in \p geps
//
// If a GEP is not inbounds, return nullptr
//
// If a sequential index is non constant, assume the first element is
// selected (offset is 0).
//
// If this is called on a non-pointer value, it returns nullptr and the
// \p Offset is not modified.
//
const Value* stripAccumulateAndCollectGEPs(const Value* V,
                                           const DataLayout &DL,
                                           SmallVectorImpl<const GEPOperator*> &geps,
                                           APInt &Offset) {
  if (!V->getType()->isPointerTy())
    return nullptr;

  unsigned BitWidth = Offset.getBitWidth();
  assert(BitWidth == DL.getIndexTypeSizeInBits(V->getType()) &&
         "The offset bit width does not match the DL specification.");

  // Offset is zero for non constant sequential indexes
  auto ExternalAnalysis = [](Value &operand, APInt &offset) -> bool {
    offset = 0;
    return true;
  };

  // Even though we don't look through PHI nodes, we could be called on an
  // instruction in an unreachable block, which may be on a cycle.
  SmallPtrSet<const Value *, 4> Visited;
  Visited.insert(V);
  do {
    if (auto *GEP = dyn_cast<GEPOperator>(V)) {

      // Insert found gep to gep list
      geps.push_back(GEP);

      // If in-bounds was requested, we do not strip non-in-bounds GEPs.
      if (!GEP->isInBounds())
        return nullptr;

      // If one of the values we have visited is an addrspacecast, then
      // the pointer type of this GEP may be different from the type
      // of the Ptr parameter which was passed to this function.  This
      // means when we construct GEPOffset, we need to use the size
      // of GEP's pointer type rather than the size of the original
      // pointer type.
      APInt GEPOffset(DL.getIndexTypeSizeInBits(V->getType()), 0);
      if (!GEP->accumulateConstantOffset(DL, GEPOffset, ExternalAnalysis))
        return nullptr;

      // Stop traversal if the pointer offset wouldn't fit in the bit-width
      // provided by the Offset argument. This can happen due to AddrSpaceCast
      // stripping.
      if (GEPOffset.getMinSignedBits() > BitWidth)
        return nullptr;

      APInt GEPOffsetST = GEPOffset.sextOrTrunc(BitWidth);
      Offset += GEPOffsetST;

      V = GEP->getPointerOperand();
    } else if (Operator::getOpcode(V) == Instruction::BitCast ||
               Operator::getOpcode(V) == Instruction::AddrSpaceCast) {
      V = cast<Operator>(V)->getOperand(0);
    } else if (auto *GA = dyn_cast<GlobalAlias>(V)) {
      if (!GA->isInterposable())
        V = GA->getAliasee();
    } else if (const auto *Call = dyn_cast<CallBase>(V)) {
        if (const Value *RV = Call->getReturnedArgOperand())
          V = RV;
    } else if (auto *PHI = dyn_cast<PHINode>(V)) {
      // Look through single-arg phi nodes created by LCSSA.
      if (PHI->getNumIncomingValues() == 1) {
        V = PHI->getIncomingValue(0);
      }
    }
    assert(V->getType()->isPointerTy() && "Unexpected operand type!");
  } while (Visited.insert(V).second);

  return V;
}

// Helper function for stripAccumulateAndCollectGEPs
// Uses an uint64_t instead of APInt and has option parameters
Value* stripAccumulateAndCollectGEPs(Value* V,
                                     const DataLayout &DL,
                                     SmallVectorImpl<const GEPOperator*> *geps = nullptr,
                                     uint64_t *offset = nullptr) {
  const Value *VConst = V;

  SmallVector<const GEPOperator*> geps_unused;
  if (!geps) {
    geps = &geps_unused;
  }

  unsigned AS = V->getType()->getPointerAddressSpace();
  unsigned IntPtrWidth = DL.getIndexSizeInBits(AS);
  APInt Offset = APInt::getZero(IntPtrWidth);

  Value *basePtr = const_cast<Value *>(stripAccumulateAndCollectGEPs(VConst, DL, *geps, Offset));
  if (offset) {
    *offset = Offset.getZExtValue();
  }

  return basePtr;
}

// Visitor to gather the loops of the add recurrences in the SCEV
// and the unknowns
struct SCEVLoopsUnknowns {
  SmallSet<const Loop *, 2> &loops;
  SmallSet<const SCEVUnknown *, 2> &unknowns;

  SCEVLoopsUnknowns(SmallSet<const Loop *, 2> &loops,
                    SmallSet<const SCEVUnknown *, 2> &unknowns)
      : loops{loops}, unknowns{unknowns} {}

  bool follow(const SCEV *S) {
    if (auto addRecSCEV = dyn_cast<SCEVAddRecExpr>(S)) {
      loops.insert(addRecSCEV->getLoop());
    } else if (auto unknownSCEV = dyn_cast<SCEVUnknown>(S)) {
      unknowns.insert(unknownSCEV);
    }
    return true;
  }

  bool isDone() const { return false; }
};

// Collect the step of the add recurrence of \p loop.
struct SCEVCollectStep {
  ScalarEvolution &SE;
  Loop *loop;
  const SCEV *&step;

  SCEVCollectStep(ScalarEvolution &SE, const SCEV *&S, Loop *loop)
      : SE(SE), loop{loop}, step(S) {}

  bool follow(const SCEV *S) {
    if (auto addRecSCEV = dyn_cast<SCEVAddRecExpr>(S)) {
      if (addRecSCEV->getLoop() == this->loop)
        this->step = addRecSCEV->getStepRecurrence(SE);
    }
    return false;
  }

  bool isDone() const { return false; }
};

// Checks if a scev is invariant to a loop
// If it finds a add recurrence whose loop is the \p loop, variant
// If it finds a unknown that is defined inside \p loop, variant
// If it is variant because of unknowns, save the unknowns is \p unks
bool isSCEVInvariantToLoop(Loop *loop, const SCEV *scev, ScalarEvolution &SE,
                           SmallSet<const SCEVUnknown *, 2> &unks) {

  SmallSet<const Loop *, 2> loops;
  SmallSet<const SCEVUnknown *, 2> unknowns;
  SCEVLoopsUnknowns scevVisit(loops, unknowns);
  visitAll(scev, scevVisit);

  // If the target loop is found, not invariant
  if (loops.find(loop) != loops.end()) {
    return false;
  }

  // Check if any unknown is variant to the loop
  bool variantUnk = false;
  for (auto unk : unknowns) {
    if (!SE.isLoopInvariant(unk, loop)) {
      variantUnk = true;
      // save variant unknowns
      unks.insert(unk);
    }
  }

  if (variantUnk) {
    return false;
  }

  // Loop invariant
  return true;
}

// Checks if a scev is invariant to a loop, but inspects unknowns that are
// defined by loads by check if their pointer operands are invariant or not
bool isSCEVReallyInvariantToLoop(Loop *loop, const SCEV *scev, ScalarEvolution &SE) {

  SmallSet<const SCEVUnknown *, 2> unknowns;
  bool isInvariant = isSCEVInvariantToLoop(loop, scev, SE, unknowns);

  // If the loop is invariant or if there are no unknowns
  // return the result
  if (isInvariant || unknowns.empty()) {
    return isInvariant;
  }

  SmallPtrSet<const Value *, 4> Visited;
  SmallVector<const Value *, 5> Worklist;
  for (auto unk : unknowns) {
    Worklist.push_back(unk->getValue());
  }

  do {
    const Value *unkVal = Worklist.pop_back_val();
    if (!unkVal || !Visited.insert(unkVal).second)
      continue;

    // Unknown is defined by a load inside the loop
    // In this case, inspect ptr operand of the load
    if (auto load = dyn_cast<LoadInst>(unkVal)) {
      Value *loadPtr = const_cast<Value *>(load->getPointerOperand());

      const SCEV *scev = SE.getSCEV(loadPtr);
      SmallSet<const SCEVUnknown *, 2> loadUnknowns;
      isInvariant = isSCEVInvariantToLoop(loop, scev, SE, loadUnknowns);

      // If there are no unknowns and it is variant
      // return variant
      if (!isInvariant && loadUnknowns.empty()) {
        return false;
      }

      for (auto unk : loadUnknowns) {
        Worklist.push_back(unk->getValue());
      }
    // If an unknown is not defined by a load just give up
    } else {
      return false;
    }

  } while (!Worklist.empty());

  // Loop invariant
  return true;
}


// Check if pointer is invariant a loop
bool isPtrInvariantToLoop(Loop *loop, Value *ptrVal, ScalarEvolution &SE) {
  const SCEV *scev = SE.getSCEV(ptrVal);
  return isSCEVReallyInvariantToLoop(loop, scev, SE);
}

// Returns the constant trip count of the loop if known.
// Otherwise returns default value.
unsigned estimateLoopTripCount(Loop *loop, ScalarEvolution &SE,
                               unsigned defaultTrip = 10) {
  SmallVector<BasicBlock *> ExitingBlocks;
  loop->getExitingBlocks(ExitingBlocks);
  for (BasicBlock *ExitingBlock : ExitingBlocks) {
    if (unsigned exactCount = SE.getSmallConstantTripCount(loop, ExitingBlock))
      return exactCount;
  }

  return defaultTrip;
}

// Returns the constant trip count of the loop if known.
// If not known, looks at the gep and checks if an operand that varies with the
// loop accesses a vector or array of constant size Otherwise it returns default
// value
unsigned estimateLoopTripCount(Value *ptrVal, Loop *loop, ScalarEvolution &SE,
                               const DataLayout &DL, unsigned defaultTrip = 10) {

  // If there is a exact trip count, return it
  if (unsigned exactCount = estimateLoopTripCount(loop, SE, /*defaulTrip*/ 0))
    return exactCount;

  // get geps that are applied to the ptr
  SmallVector<const GEPOperator*> geps;
  stripAccumulateAndCollectGEPs(ptrVal, DL, &geps);

  // If pointer is not computed by gep, give up
  if (geps.empty()) {
    return defaultTrip;
  }

  unsigned tripCount = 0;

  // TODO: check if the next line works
  // Initialize type as type of the base ptr
  Type *previousTy = geps.back()->getSourceElementType();

  // Look at the gep operands
  for (SmallVector<const GEPOperator*>::reverse_iterator it=geps.rbegin(); it != geps.rend(); ++it) {
    const GEPOperator* gep = *it;

    for (gep_type_iterator GTI = gep_type_begin(gep), GTE = gep_type_end(gep);
         GTI != GTE; ++GTI) {
      Value *operand = GTI.getOperand();
      const SCEV *scev = SE.getSCEV(operand);

      // If the operand indexes an constant size array and it is variant to the
      // loop it is used to estimate the trip count
      if (GTI.isSequential() && !isSCEVReallyInvariantToLoop(loop, scev, SE)) {

        // Check if there is a stride
        int64_t stride = 1;
        const SCEV *strideSCEV = nullptr;
        SCEVCollectStep scevVisitStep(SE, strideSCEV, loop);
        visitAll(scev, scevVisitStep);

        // TODO: what to do if not constant?
        if (strideSCEV) {
          if (auto constantScev = dyn_cast<SCEVConstant>(strideSCEV)) {
            stride = constantScev->getValue()->getSExtValue();
          }
        }

        // Don't use negative strides
        if (stride < 0)
          stride *= -1;

        // Use the previous and not the current type because if the IV accesses a
        // vector its indexed type will be the type of the elements of the vector.
        // The previous indexed type will be a vector of that element type.
        if (auto arrTy = dyn_cast<ArrayType>(previousTy)) {
          unsigned arrTrip = (unsigned)ceilDiv(arrTy->getNumElements(), stride);
          tripCount = std::max(tripCount, arrTrip);
        } else if (auto vecTy = dyn_cast<FixedVectorType>(previousTy)) {
          unsigned vecTrip = (unsigned)ceilDiv(vecTy->getNumElements(), stride);
          tripCount = std::max(tripCount, vecTrip);
        }
      }

      previousTy = GTI.getIndexedType();
    }
  }

  // If still unknown, return default
  if (tripCount == 0)
    return defaultTrip;

  return tripCount;
}

/// Estimates the offset difference of the same GEP between two iterations of
/// loop. Return nullopt if unknown
std::optional<uint64_t> getLoopOffset(SmallVectorImpl<const GEPOperator*> &geps,
                                      Value *basePtr, Loop *loop, ScalarEvolution &SE,
                                      const DataLayout &DL) {
  if (geps.empty()) {
    return 0;
  }

  uint64_t loopOffset = 0;

  // Look at the other gep operands
  for (auto gep : geps) {
    for (gep_type_iterator GTI = gep_type_begin(gep), GTE = gep_type_end(gep);
         GTI != GTE; ++GTI) {

      Value *operand = GTI.getOperand();
      const SCEV *scev = SE.getSCEV(operand);

      // if a sequential index offset if the size of the indexed type
      if (!isSCEVReallyInvariantToLoop(loop, scev, SE)) {
        if (GTI.isSequential()) {

          // Check if there is a stride
          int64_t stride = 1;
          const SCEV *stepSCEV = nullptr;
          SCEVCollectStep scevVisitStrides(SE, stepSCEV, loop);
          visitAll(scev, scevVisitStrides);

          // TODO: what to do if there is more than one stride scev?
          //       or if not constant
          // Try to get constant step
          if (stepSCEV) {
            if (auto constantScev = dyn_cast<SCEVConstant>(stepSCEV)) {
              stride = constantScev->getValue()->getSExtValue();
            }
          }

          // Don't use negative strides
          if (stride < 0)
            stride *= -1;

          loopOffset +=
              DL.getTypeAllocSize(GTI.getIndexedType()).getFixedValue() * stride;
          // give up it is a loop variant structure index
        } else {
          return std::nullopt;
        }
      }
    }
  }

  return loopOffset;
}

// Compute the PIDV value for a list of loads and stores in the context of \p targetLoop
std::optional<uint64_t> getBytesAccessed(SmallVector<Instruction *> &loadStores,
                                         Loop *targetLoop, const DataLayout &DL,
                                         ScalarEvolution &SE, LoopInfo &LI) {
  // dbgs() << "[RebaseDLPass] PIDV ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";

  // Save ptrs counted to avoid double count
  // loads and stores that use the same ptr
  SmallSet<Value *,4> ptrsCounted;

  if (loadStores.empty()) {
    return 0;
  }

  uint64_t bytesAccessed = 0;
  for (auto inst : loadStores) {

    Value *ptrVal = getLoadStorePointerOperand(inst);
    if (!ptrVal) {
      return std::nullopt;
    }

    // If ptr was already counted, skip it
    if (!ptrsCounted.insert(ptrVal).second) {
      continue;
    }

    // dbgs() << "[RebaseDLPass] instruction: " << *inst << "\n";

    // Make sure load is contained in target loop
    if (!targetLoop->contains(inst)) {
      return std::nullopt;
    }

    // Size of field accessed by the load
    Type *ty = getLoadStoreType(inst);
    if (!ty || !ty->isSized()) {
      return std::nullopt;
    }
    TypeSize fieldSize = DL.getTypeAllocSize(ty);
    // dbgs() << "[RebaseDLPass] - type size: " << fieldSize << "\n";

    // Get loop of the load
    Loop *currLoop = LI.getLoopFor(inst->getParent());

    unsigned timesAccessed = 1;
    uint64_t bytesAccessedByLoad = fieldSize;

    // Get combined trip count of the loops to which the load is variant
    // stopping at the targetLoop
    while (currLoop != targetLoop->getParentLoop()) {
      if (!isPtrInvariantToLoop(currLoop, ptrVal, SE)) {
        timesAccessed = estimateLoopTripCount(ptrVal, currLoop, SE, DL);
        bytesAccessedByLoad *= timesAccessed;
        // dbgs() << "[RebaseDLPass] - variant to loop: " <<
        // currLoop->getName()
        //        << " at depth " << currLoop->getLoopDepth() << "\n";
        // dbgs() << "[RebaseDLPass] - trip count: " << timesAccessed <<
        // "\n";
      }
      currLoop = currLoop->getParentLoop();
    }
    bytesAccessed += bytesAccessedByLoad;
  }

  return bytesAccessed;
}

std::optional<uint64_t>
getCacheLinesAccessedInBytes(SmallVector<Instruction *> &loadStores,
                             Loop *targetLoop, const DataLayout &DL,
                             ScalarEvolution &SE, LoopInfo &LI,
                             const int cacheLineSize = 64) {
  // dbgs() << "[RebaseDLPass] AADV ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";

  // Save ptrs counted to avoid double count
  // loads and stores that use the same ptr
  SmallSet<Value *,4> ptrsCounted;

  if (loadStores.empty()) {
    return 0;
  }

  // The bit vector represents cache lines accessed
  // each bit is a cache line, if set, it was accessed
  SmallSet<int, 4> cacheLinesAccessed{};

  // Smallest base offset. Used to avoid simulating that the first field of a
  // structure accessed is at the end of a cache line, thus bringing more cache
  // lines than actually needed
  uint64_t adjustConstOffset;

  // Initialize adjust to the base offset of the first gep
  Value *firstPtr = getLoadStorePointerOperand((*loadStores.begin()));
  if (!firstPtr) {
    return std::nullopt;
  }
  stripAccumulateAndCollectGEPs(firstPtr, DL, nullptr, &adjustConstOffset);

  // Get the minimum base offset of all geps
  for (auto inst : loadStores) {
    Value *ptrVal = getLoadStorePointerOperand(inst);

    uint64_t constOffset;
    stripAccumulateAndCollectGEPs(ptrVal, DL, nullptr, &constOffset);
    adjustConstOffset = std::min(adjustConstOffset, constOffset);
  }

  // For every loop that a scev is variant, but the loop offset is zero
  // because of an unknown, the loop is saved here, as these loop offsets
  // cannot be mapped to cacheLinesAccessed
  DenseMap<Loop *, unsigned> loopsOffsetZero;

  for (auto inst : loadStores) {
    Value *ptrVal = getLoadStorePointerOperand(inst);

    // If ptr was already counted, skip it
    if (!ptrsCounted.insert(ptrVal).second) {
      continue;
    }

    // dbgs() << "[RebaseDLPass] load/store: " << *inst << "\n";

    // compute constantj offset of ptr
    // and save geps that are applied to the ptr
    uint64_t constOffset;
    SmallVector<const GEPOperator*> geps;
    Value *basePtr = stripAccumulateAndCollectGEPs(ptrVal, DL, &geps, &constOffset);
    // dbgs() << "[RebaseDLPass] - const offset: " << constOffset << "\n";

    // Size of field accessed by the load
    Type *ty = getLoadStoreType(inst);
    if (!ty || !ty->isSized()) {
      return std::nullopt;
    }
    TypeSize fieldSize = DL.getTypeAllocSize(ty);

    Loop *currLoop = LI.getLoopFor(inst->getParent());

    // Store trip count and loop offset of loops to which the ptr is variant
    SmallVector<std::pair<unsigned, uint64_t>> tripCountAndLoopOffsets;
    while (currLoop != targetLoop->getParentLoop()) {
      if (isPtrInvariantToLoop(currLoop, ptrVal, SE)) {
        currLoop = currLoop->getParentLoop();
        continue;
      }

      // compute loop offset of the gep
      std::optional<uint64_t> loopOffset = getLoopOffset(geps, basePtr, currLoop, SE, DL);
      if (!loopOffset.has_value()) {
        // dbgs() << "[RebaseDLPass] No loop offset\n";
        return std::nullopt;
      }
      // dbgs() << "[RebaseDLPass]     - loop offset: " << loopOffset.value()
      //        << " on loop " << currLoop->getName() << " at depth "
      //        << currLoop->getLoopDepth() << "\n";

      unsigned tripCount = estimateLoopTripCount(ptrVal, currLoop, SE, DL);
      // dbgs() << "[RebaseDLPass]     - trip count: " << tripCount << "\n";

      if (loopOffset.value() == 0) {
        if (loopsOffsetZero.count(currLoop) == 0) {
          loopsOffsetZero[currLoop] = tripCount;
        } else {
          loopsOffsetZero[currLoop] = std::max(tripCount, loopsOffsetZero[currLoop]);
        }
      }

      tripCountAndLoopOffsets.push_back({tripCount, loopOffset.value()});
      currLoop = currLoop->getParentLoop();
    }

    // Compute total trip count of the loops
    unsigned totalTripCount = 1;
    for (auto tlPair : tripCountAndLoopOffsets) {
      unsigned tripCount = tlPair.first;
      unsigned loopOffset = tlPair.second;
      if (loopOffset == 0) {
        continue;
      }
      totalTripCount *= tripCount;
    }
    // dbgs() << "[RebaseDLPass]     - total trip count: " << totalTripCount
    // << "\n";

    // Consider the accesses to all iterations in all loops
    for (unsigned i = 0; i < totalTripCount; i++) {
      // decompose iteration i in the loops in tripCountAndLoopOffsets
      int loopPart = 0;
      for (auto tlPair : tripCountAndLoopOffsets) {
        unsigned tripCount = tlPair.first;
        unsigned loopOffset = tlPair.second;
        if (loopOffset == 0) {
          continue;
        }
        loopPart += i % tripCount * loopOffset;
      }

      // check at which cache line the bytes in the start, the end, and
      // in the middle of the of the field access fall into
      for (uint64_t j = 0; j < fieldSize; j++) {
        unsigned cacheLine = (loopPart + (constOffset - adjustConstOffset) + j) / cacheLineSize;
        cacheLinesAccessed.insert(cacheLine);
      }
    }
  }

  uint64_t totalCacheLinesAccessed = cacheLinesAccessed.size() * cacheLineSize;
  for (auto loopTrip : loopsOffsetZero) {
    unsigned tripCount = loopTrip.second;
    totalCacheLinesAccessed *= tripCount;
  }

  // dbgs() << "[RebaseDLPass] Total cache lines in bytes: " << totalCacheLinesAccessed
  // << "\n";

  return totalCacheLinesAccessed;
}

class RegionPackingMemReg {
public:
  // List of pointers that may point to the same memory region
  SmallVector<Value *> ptrs;
  SmallSet<const Value *, 2> underlyingObjects;
  bool hasNullUnderlyingObject{false};
  // This set contains information about the pointer operand of loads that
  // define underlying objects of this memreg
  // The elements of the pair are:
  // uint64_t: constant offset of applied to the ptr
  // Value*: basePtr of the load
  SmallSet<std::pair<uint64_t, Value*>, 2> ptrLoads;

  RegionPackingMemReg(){};

  RegionPackingMemReg(Value *ptrVal, const DataLayout &DL) {
    if (ptrVal->getType()->isPointerTy()) {
      this->addPtr(ptrVal, DL);
    }
  };

  // Add ptr to this memory region
  void addPtr(Value *ptrVal, const DataLayout &DL) {
    // Check if it is a pointer
    if (!ptrVal->getType()->isPointerTy())
      return;

    // Check if pointer has only gep users in the loop
    bool onlyGEPUsers = true;
    for (auto user : ptrVal->users()) {
      if (!isa<GEPOperator>(user)) {
        onlyGEPUsers = false;
      }
    }
    // If the pointer has only gep users in the loop
    // do not add it, as it is only an intermediary address
    if (onlyGEPUsers)
      return;

    // Check if it does not already exist
    if (std::find(this->ptrs.begin(), this->ptrs.end(), ptrVal) ==
        this->ptrs.end()) {
      // Add ptr
      this->ptrs.push_back(ptrVal);
    }

    // Get underlying objects of ptr
    SmallVector<const Value *> objs{};
    getUnderlyingObjects(ptrVal, objs);

    // Merge pointer underlying objects to this underlying objects
    // but skip the null value
    for (auto obj : objs) {
      if (auto constant = dyn_cast<Constant>(obj)) {
        if (constant->isNullValue()) {
          this->hasNullUnderlyingObject = true;
          continue;
        }
      }
      this->underlyingObjects.insert(obj);

      // Add info about the loads that define these underlying objects
      if (auto load = dyn_cast<LoadInst>(obj)) {
        Value* ptrOperand = const_cast<Value *>(load->getPointerOperand());
        std::pair<uint64_t, Value*> ptrLoad;
        ptrLoad.second = stripAccumulateAndCollectGEPs(ptrOperand, DL, nullptr, &ptrLoad.first);
        this->ptrLoads.insert(ptrLoad);
      }
    }
  }

  // True if the underlying objects of this memreg
  // have a non empty intersection with the objects of
  // another memreg, or if the objects of a memreg
  // must alias with the objects of another memreg
  bool intersects(RegionPackingMemReg &other, AliasAnalysis &AA) {
    if (hasIntersection(this->underlyingObjects, other.underlyingObjects))
      return true;

    // TODO: what to do in the case of may alias? Runtime check might be needed
    for (auto thisObj : this->underlyingObjects) {
      for (auto otherObj : other.underlyingObjects) {
        if (AA.alias(thisObj, otherObj) == AliasResult::MustAlias)
          return true;
      }
    }

    // TODO: maybe consider multiple levels of pointer loads, not just one
    // If two memregs have an underlying object that is defined by a load
    // that loads from the same base pointer with the same offset, the underlying
    // objects are the same. This check is needed because sometimes
    // the same ptr is loaded multiple times
    for (auto thisPtrLoad : this->ptrLoads) {
      for (auto otherPtrLoad : other.ptrLoads) {
        if (thisPtrLoad == otherPtrLoad)
          return true;
      }
    }

    return false;
  }

  bool empty() { return this->ptrs.empty(); }

  // Merge a memreg to this one
  void merge(RegionPackingMemReg &other) {
    // Add ptrs that do not exist
    for (auto ptrVal : other.ptrs) {
      if (std::find(this->ptrs.begin(), this->ptrs.end(), ptrVal) ==
          this->ptrs.end()) {
        this->ptrs.push_back(ptrVal);
      }
    }
    // Make an union of the underlying objects and ptrloads
    set_union(this->underlyingObjects, other.underlyingObjects);
    set_union(this->ptrLoads, other.ptrLoads);
  }

  // Check if the pointers of the memReg are invariant to a loop
  bool isInvariantToLoop(Loop *loop, ScalarEvolution &SE) {
    for (auto ptrVal : this->ptrs) {
      if (!isPtrInvariantToLoop(loop, ptrVal, SE)) {
        return false;
      }
    }
    return true;
  }

  // Check if one of the pointers to this MemReg are loaded inside a loop
  bool isLoadedInLoop(Loop *loop) {
    for (auto ptrVal : this->ptrs) {
      for (auto user : ptrVal->users()) {
        if (auto loadInst = dyn_cast<LoadInst>(user)) {
          if (loop->contains(loadInst)) {
            return true;
          }
        }
      }
    }

    return false;
  }

  // Returns true if this memReg has a load that
  // is variant to a child loop of \p parentLoop
  bool isVariantToChildLoop(Loop *parentLoop, LoopInfo &LI, ScalarEvolution &SE) {
    auto loopNest = parentLoop->getLoopsInPreorder();

    for (auto ptrVal : this->ptrs) {
      for (auto user : ptrVal->users()) {
        if (auto loadInst = dyn_cast<LoadInst>(user)) {
          for (auto loop : loopNest) {
            if (loop == parentLoop)
              continue;

            if (loop->contains(loadInst) &&
                !isPtrInvariantToLoop(loop, ptrVal, SE)) {
              return true;
            }
          }
        }
      }
    }

    return false;
  }

  bool isStoredInLoop(Loop *loop) {
    for (auto ptrVal : this->ptrs) {
      for (auto user : ptrVal->users()) {
        if (auto storeInst = dyn_cast<StoreInst>(user)) {
          if (loop->contains(storeInst)) {
            return true;
          }
        }
      }
    }

    return false;
  }

  // Get loads and store instructions of this memReg that are
  // in \p loop
  SmallVector<Instruction *> getMemRegLoadStoresInLoop(Loop *loop) {
    SmallVector<Instruction *> loadStores;

    // Get loads and stores for this candidate
    for (auto ptrVal : this->ptrs) {
      for (auto user : ptrVal->users()) {
        // Load uses ptrVal
        if (auto loadInst = dyn_cast<LoadInst>(user)) {
          if (loop->contains(loadInst)) {
            loadStores.push_back(loadInst);
          }
        // Store uses ptrVal as the pointer operand
        } else if (auto storeInst = dyn_cast<StoreInst>(user)) {
          if (loop->contains(storeInst) &&
              ptrVal == storeInst->getPointerOperand()) {
            loadStores.push_back(storeInst);
          }
        }
      }
    }

    return loadStores;
  }

  void dump(const DataLayout &DL, Loop *targetLoop = nullptr) {
    dbgs() << "[RebaseDLPass] Memreg: ------------------\n";

    SmallVector<LoadInst *> loads;
    SmallVector<StoreInst *> stores;

    Value *mainUnderlyingObj = nullptr;
    SmallVector<const GEPOperator *> geps;

    // Get loads and stores for this candidate
    for (auto ptrVal : this->ptrs) {

      // Assumes that this objects is the same for all ptrs
      // This is ensured by the legality check
      if (!mainUnderlyingObj) {
        mainUnderlyingObj = stripAccumulateAndCollectGEPs(ptrVal, DL, &geps);
      }

      for (auto user : ptrVal->users()) {
        // Load uses ptrVal
        if (auto loadInst = dyn_cast<LoadInst>(user)) {
          if (!targetLoop || targetLoop->contains(loadInst)) {
            loads.push_back(loadInst);
          }
        // Store uses ptrVal as the pointer operand
        } else if (auto storeInst = dyn_cast<StoreInst>(user)) {
          if (ptrVal == storeInst->getPointerOperand() &&
              (!targetLoop || targetLoop->contains(storeInst))) {
            stores.push_back(storeInst);
          }
        }
      }
    }

    dbgs() << "[RebaseDLPass] - Loads:\n";
    for (auto load : loads) {
      dbgs() << "[RebaseDLPass]     - " << *load << "\n";
      if (load->getDebugLoc()) {
        dbgs() << "[RebaseDLPass]         - " << *load->getDebugLoc() << "\n";
      }
    }

    if (!stores.empty()) {
      dbgs() << "[RebaseDLPass] - Stores:\n";
      for (auto store : stores) {
        dbgs() << "[RebaseDLPass]     - " << *store << "\n";
        if (store->getDebugLoc()) {
          dbgs() << "[RebaseDLPass]         - " << *store->getDebugLoc() << "\n";
        }
      }
    }

    dbgs() << "[RebaseDLPass] - Main underlying object:\n";
    if (auto inst = dyn_cast<Instruction>(mainUnderlyingObj)) {
      dbgs() << "[RebaseDLPass]     - " << *inst << "\n";
      if (inst->getDebugLoc()) {
        dbgs() << "[RebaseDLPass]         - " << *inst->getDebugLoc() << "\n";
      }
    } else {
      dbgs() << "[RebaseDLPass]     - " << *mainUnderlyingObj << "\n";
    }
    if (!geps.empty()) {
      dbgs() << "[RebaseDLPass]     - Type: " << *geps.back()->getSourceElementType() << "\n";
    }

    dbgs() << "[RebaseDLPass] - Underlying objects:\n";
    for (auto obj : this->underlyingObjects) {
      if (auto inst = dyn_cast<Instruction>(obj)) {
        dbgs() << "[RebaseDLPass]     - " << *inst << "\n";
        if (inst->getDebugLoc()) {
          dbgs() << "[RebaseDLPass]         - " << *inst->getDebugLoc() << "\n";
        }
      } else {
        dbgs() << "[RebaseDLPass]     - " << *obj << "\n";
      }
    }
    if (this->hasNullUnderlyingObject)
      dbgs() << "[RebaseDLPass]     - ptr null\n";

    dbgs() << "[RebaseDLPass] --------------------------\n";
    dbgs() << "[RebaseDLPass] \n";
  }
};

// Helper function that computes the cache lines accessed by a list of
// memregs in a loop
std::optional<uint64_t>
getCacheLinesAccessedInBytes(SmallVector<RegionPackingMemReg> &memRegs,
                             Loop *targetLoop, const DataLayout &DL,
                             ScalarEvolution &SE, LoopInfo &LI,
                             const int cacheLineSize = 64) {

  uint64_t total = 0;

  for (RegionPackingMemReg &memReg : memRegs) {
    auto loadStores = memReg.getMemRegLoadStoresInLoop(targetLoop);
    auto totalCacheLinesAccessed = getCacheLinesAccessedInBytes(loadStores, targetLoop, DL, SE, LI);
    if (totalCacheLinesAccessed.has_value()) {
      total += totalCacheLinesAccessed.value();
    } else {
      return std::nullopt;
    }
  }

  return total;
}

class RegionPackingCandidate {
public:
  RegionPackingMemReg memReg;
  Loop *targetLoop;
  std::optional<float> cacheUtilization;
  std::optional<float> memRegImpact;
  std::optional<float> costBenefitRatio;

  // Create a new memReg that only holds pointers that are used inside the
  // target loop, and that are not intermediary pointers
  RegionPackingCandidate(RegionPackingMemReg *memReg, Loop *loop,
                         const DataLayout &DL)
      : targetLoop{loop} {
    auto ptrsUsedInLoop = getPtrsUsedInLoop(this->targetLoop);

    for (Value *ptrVal : memReg->ptrs) {
      // ptrVal is used in the loop
      if (ptrsUsedInLoop.contains(ptrVal)) {
        this->memReg.addPtr(ptrVal, DL);
      }
    }
  }

  /// Packing candidates are sorted for a greedy selection the best candidates
  bool operator<(const RegionPackingCandidate &other) const {
    // Order is based on cost benefit
    if (this->costBenefitRatio.has_value() && other.costBenefitRatio.has_value()) {
      if (this->costBenefitRatio.value() != other.costBenefitRatio.value()) {
        return this->costBenefitRatio.value() > other.costBenefitRatio.value();
      }
    }

    // If the gain/cost order fails or ties, order based loop depth.
    // lower depth is the better candidate of the two
    return this->targetLoop->getLoopDepth() > other.targetLoop->getLoopDepth();
  }

  bool operator>(const RegionPackingCandidate &other) const {
    return other < *this;
  }

  // Checks if it is legal to apply the transformation to a candidate
  bool isLegal(const DataLayout &DL, ScalarEvolution &SE, AliasAnalysis &AA, LoopInfo &LI) {

    // Get loads and stores of this candidate
    SmallVector<Instruction *> loadStores = this->memReg.getMemRegLoadStoresInLoop(this->targetLoop);

    Value *firstBaseObj = nullptr;
    for (auto loadStore : loadStores) {
      Value *ptrVal = getLoadStorePointerOperand(loadStore);
      if (!ptrVal) {
        dbgs() << "[RebaseDLPass] ERROR: Load/Store without pointer operand\n";
        return false;
      }

      // Get underlying object of ptrVal without going through phi and select instructions
      Value *baseObj = stripAccumulateAndCollectGEPs(ptrVal, DL);
      // Base object not found
      if (!baseObj) {
        dbgs() << "[RebaseDLPass] Legality: Base underlying object not found\n";
        return false;
      }

      // Ensure that all ptrs have the same base object
      if (!firstBaseObj) {
        firstBaseObj = baseObj;
      } else if (baseObj != firstBaseObj) {
        dbgs() << "[RebaseDLPass] Legality: Multiple underlying objects\n";
        return false;
      }
    }

    // If the base ptr is variant to the loops inside the target loop,
    // or the target loop, give up, as the base may not always be the same
    const SCEV *baseObjSCEV = SE.getSCEV(firstBaseObj);
    for (auto loop : this->targetLoop->getLoopsInPreorder()) {
      if (!isSCEVReallyInvariantToLoop(loop, baseObjSCEV, SE)) {
        dbgs() << "[RebaseDLPass] Legality: Base address defined inside target loop\n";
        return false;
      }
    }

    // TODO: If the base ptr is a load instruction defined in the target Loop,
    // we already know that it is invariant to the loop, but we may need to check if
    // if the pointer operand of this load is not passed to any functions in the loop
    // as they could access the memreg by making the load again.

    // Get the loops that loads and store of the candidate are variant with
    SmallSet<Loop*,2> loopsToBeCopied;
    for (auto inst : loadStores) {
      Loop *currLoop = LI.getLoopFor(inst->getParent());
      while (currLoop != targetLoop) {
        if (!this->memReg.isInvariantToLoop(currLoop, SE)) {
          loopsToBeCopied.insert(currLoop);
        }
        currLoop = currLoop->getParentLoop();
      }
    }

    // Must be able to determine bounds of loops to be copied for the transformation
    // Otherwise illegal
    for (auto loop : loopsToBeCopied) {
      auto bounds = loop->getBounds(SE);
      if (bounds == std::nullopt) {
        dbgs() << "[RebaseDLPass] Legality: Bounds not found \n";
        return false;
      }

      Value *initialIVVal = &bounds->getInitialIVValue();
      Value *finalIVVal = &bounds->getFinalIVValue();
      Value *stepVal = bounds->getStepValue();

      // Get scev of the bounds and step
      const SCEV *scevInitialIV = SE.getSCEV(initialIVVal);
      const SCEV *scevFinalIV = SE.getSCEV(finalIVVal);
      const SCEV *scevStep = SE.getSCEV(stepVal);

      // dbgs() << "[RebaseDLPass] Depth: " << loop->getLoopDepth() << "\n";
      // dbgs() << "[RebaseDLPass] Initial IV " << *scevInitialIV << "\n";
      // dbgs() << "[RebaseDLPass] Final IV Value " << *scevFinalIV << "\n";
      // dbgs() << "[RebaseDLPass] Step Value " << *scevStep << "\n";
      // dbgs() << "[RebaseDLPass] Initial IV " << *initialIVVal << "\n";
      // dbgs() << "[RebaseDLPass] Final IV Value " << *finalIVVal << "\n";
      // dbgs() << "[RebaseDLPass] Step Value " << *stepVal << "\n";

      // Bounds must be invariant to the target loop (and to the inner loops too)
      Loop *currLoop = loop;
      while (currLoop != targetLoop->getParentLoop()) {
        if (!isSCEVReallyInvariantToLoop(currLoop, scevInitialIV, SE) ||
            !isSCEVReallyInvariantToLoop(currLoop, scevFinalIV, SE) ||
            !isSCEVReallyInvariantToLoop(currLoop, scevStep, SE)) {
          dbgs() << "[RebaseDLPass] Legality: Bounds variant to target loop nest\n";
          return false;
        }
        currLoop = currLoop->getParentLoop();
      }
    }

    // Get calls in the loop
    SmallVector<CallInst *> calls = getInstructions<CallInst>(this->targetLoop);
    // Give up if
    for (auto call : calls) {
      // a call is indirect
      if (call->isIndirectCall()) {
        dbgs() << "[RebaseDLPass] Legality: Indirect call\n";
        return false;
      }

      Function *calledFunction = call->getCalledFunction();
      // ignore llvm functions
      if (calledFunction->isIntrinsic()) {
        continue;
      }
      // a call is to a function not defined in the module
      if (!calledFunction || calledFunction->isDeclaration()) {
        dbgs() << "[RebaseDLPass] Legality: Called function not found\n";
        return false;
      }

      // a call is recursive
      if (calledFunction == call->getFunction()) {
        dbgs() << "[RebaseDLPass] Legality: Called function is recursive\n";
        return false;
      }
    }

    // Check if any of the underlying objects of the memreg are globals and save
    // them
    SmallVector<const Value *> globals;
    for (auto obj : this->memReg.underlyingObjects) {
      if (isa<GlobalVariable>(obj)) {
        globals.push_back(obj);
      }
    }

    // If there is a global underlying object,
    // the target region cannot have any function calls
    // that modify or reference the global
    if (!globals.empty()) {
      // This check is here because the getModRefInfo function will check if the
      // underlying object of the memory location instruction is a global, so it
      // does not work if the memReg has multiple underlying objects
      if (this->memReg.underlyingObjects.size() > 1 || globals[0] != firstBaseObj) {
        dbgs() << "[RebaseDLPass] Legality: Accesses a global underlying object that is not the only underlying and base object\n";
        return false;
      }

      if (loadStores.empty()) {
        dbgs() << "[RebaseDLPass] ERROR: Load/Stores empty\n";
        return false;
      }

      // Since the base underlying object of all loads was ensured to be the same
      // we can pass the any of the load/store instructions as the memory location
      // if it is a global
      for (auto call : calls) {
        auto memLoc = MemoryLocation::get(loadStores[0]);
        if (AA.getModRefInfo(call, memLoc) != ModRefInfo::NoModRef) {
          return false;
        }
      }
    }

    return true;
  }

  // Check if one of the pointers of the memReg is an argument to a call
  // instruction
  bool isInterprocedural(const DataLayout &DL, ScalarEvolution &SE,
                         AliasAnalysis &AA) {
    for (auto ptrVal : this->memReg.ptrs) {
      for (auto user : ptrVal->users()) {
        if (auto call = dyn_cast<CallInst>(user)) {
          if (this->targetLoop->contains(call)) {
            return true;
          }
        }
      }
    }
    return false;
  }

  void computeCostBenefit(SmallVector<RegionPackingMemReg> &memRegs,
                          const DataLayout &DL, ScalarEvolution &SE,
                          LoopInfo &LI, BlockFrequencyInfo &BFI, DominatorTree &DT) {
    // dbgs() << "[RebaseDLPass] Cost/Benefit ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";

    // Get loads and stores for this candidate
    SmallVector<Instruction *> loadStores = this->memReg.getMemRegLoadStoresInLoop(this->targetLoop);

    // Get the loops that loads and store have as parents inside the target loop
    // (including the target loop)
    SmallSet<Loop*,2> parentLoops;
    for (auto inst : loadStores) {
      Loop *currLoop = LI.getLoopFor(inst->getParent());
      while (currLoop != targetLoop->getParentLoop()) {
        parentLoops.insert(currLoop);
        currLoop = currLoop->getParentLoop();
      }
    }

    // This check ensures that there is no break or return that would
    // cause the loops that access the transformed structure elements
    // to finish early and not access all of its elements
    for (auto loop : parentLoops) {
      // Ok if it has only one exit
      if (loop->getUniqueExitBlock()) {
        continue;
      }

      // Not ok if it has no exit
      if (loop->hasNoExitBlocks()) {
        dbgs() << "[RebaseDLPass] Cost/Benefit: Loop has no exit\n";
        return;
      }

      SmallVector<BasicBlock*> nonLatchExits;
      loop->getUniqueNonLatchExitBlocks(nonLatchExits);

      // If it has multiple exits, check if it is only because of asserts
      // these are fine, otherwise give up on multiple exits
      for (auto exit : nonLatchExits) {
        Instruction *terminator = exit->getTerminator();
        if (!isa<UnreachableInst>(terminator)) {
          dbgs() << "[RebaseDLPass] Cost/Benefit: Loop has multiple exits\n";
          return;
        }
      }
    }

    // Get blocks for load/stores
    SmallSet<BasicBlock*,2> loadStoreBlocks;
    for (auto loadStore: loadStores) {
      loadStoreBlocks.insert(loadStore->getParent());
    }
    // Get frequency for the header of the target loop
    uint64_t targetHeaderFreq = BFI.getBlockFreq(this->targetLoop->getHeader()).getFrequency();
    const double minFreqRatio = 0.35;
    for (auto block: loadStoreBlocks) {
      // Get node in the dominator tree for the basic block of load/store
      auto node = DT.getNode(block);

      // Go up the tree (through immediate dominators) until getting to
      // a basic block whose immediate loop parent is the target loop
      // this should always stop at most at the header of the target loop
      while (node) {

        // Sanity check
        if (!this->targetLoop->contains(node->getBlock())) {
          dbgs() << "[RebaseDLPass] ERROR: Load/Store without pointer operand\n";
          return;
        }

        uint64_t idomFreq = BFI.getBlockFreq(node->getBlock()).getFrequency();
        if (idomFreq < targetHeaderFreq * minFreqRatio) {
          // dbgs() << "[RebaseDLPass] BFI: targetHeaderFreq = " << targetHeaderFreq << "\n";
          // dbgs() << "[RebaseDLPass] - BFI: idomFreq/targetHeaderFreq = " << format("%.3f", idomFreq / (double) targetHeaderFreq) << "\n";
          dbgs() << "[RebaseDLPass] Cost/Benefit: Load dominator has a frequency that is too low\n";
          return;
        }

        // Stop when the idom is at the targetloop level
        if (LI.getLoopFor(node->getBlock()) == this->targetLoop) {
          break;
        }

        // Go to next immediate dominator
        node = node->getIDom();
      }
    }

    // Compute bytes accessed of the memory region in the target loop
    std::optional<uint64_t> bytesAccessed =
        getBytesAccessed(loadStores, this->targetLoop, DL, SE, LI);
    if (!bytesAccessed.has_value()) {
      // dbgs() << "[RebaseDLPass] bytesAccessed has no value\n";
      return;
    }

    // Compute cache lines accessed in bytes of the memory region in the target
    // loop
    const int cacheLineSize = 64;
    std::optional<uint64_t> cacheLinesAccessedInBytes =
        getCacheLinesAccessedInBytes(loadStores, this->targetLoop, DL, SE, LI,
                                     cacheLineSize);
    if (!cacheLinesAccessedInBytes.has_value()) {
      // dbgs() << "[RebaseDLPass] cacheLineBytesAccessed as no value\n";
      return;
    }

    // Compute data usage ratio and check if this candidate is bellow the
    // threshold
    this->cacheUtilization =
        (float)bytesAccessed.value() / cacheLinesAccessedInBytes.value();
    const float utilizationThreshold = 0.5;
    if (this->cacheUtilization > utilizationThreshold) {
      dbgs() << "[RebaseDLPass] Cost/Benefit: Above DU threshold\n";
      return;
    }

    // Compute bytes that are part of the cache lines accessed that were not
    // used
    uint64_t unusedCacheLineBytes =
        cacheLinesAccessedInBytes.value() - bytesAccessed.value();

    // TODO: simulate padding required by new type
    uint64_t cacheLinesNeededInBytes =
        ceilDiv(bytesAccessed.value(), cacheLineSize) * cacheLineSize;
    uint64_t unusedCacheLineBytesAfterTransformation =
        cacheLinesNeededInBytes - bytesAccessed.value();

    // Compute Benefit and Cost
    int64_t benefit =
        unusedCacheLineBytes - unusedCacheLineBytesAfterTransformation;
    uint64_t cost = cacheLinesAccessedInBytes.value();
    if (this->memReg.isStoredInLoop(this->targetLoop)) {
      cost *= 2;
    }

    if (benefit <= 0) {
      dbgs() << "[RebaseDLPass] Cost/Benefit: Benefit is zero or negative\n";
      return;
    }

    auto totalCacheLinesAccessed = getCacheLinesAccessedInBytes(memRegs, this->targetLoop, DL, SE, LI);
    if (totalCacheLinesAccessed.has_value()) {
      this->memRegImpact = (float)cacheLinesAccessedInBytes.value()/totalCacheLinesAccessed.value();
      // If the reduction in cache lines by applying the transformation
      // represents less than 10% of the cache lines accessed by the loop
      // give up as the impact on performance will likely be very low
      // if (benefit < 0.05 * totalCacheLinesAccessed.value()) {
      //   // dbgs() << "[RebaseDLPass] Benefit compared to total cache lines accessed is too low\n";
      //   this->costBenefit = 0;
      //   return;
      // }
    }

    // Multiply the benefit by the number of iterations of the invariant target
    // loop
    int64_t overallBenefit = benefit * estimateLoopTripCount(this->targetLoop, SE);

    // Compute net benefit
    this->costBenefitRatio = (float)cost/overallBenefit;

    // dbgs() << "[RebaseDLPass] - PIDV: " << bytesAccessed.value() << "\n";
    // dbgs() << "[RebaseDLPass] - AADV: " <<
    // cacheLinesAccessedInBytes.value()
    //        << "\n";
    // dbgs() << "[RebaseDLPass] - DVoh: " << unusedCacheLineBytes << "\n ";
    // dbgs() << "[RebaseDLPass] - DVoh_rbls : "
    //        << unusedCacheLineBytesAfterTransformation << "\n";
    // dbgs() << "[RebaseDLPass] - Reuse iterations: "
    //        << estimateLoopTripCount(this->targetLoop, SE) << "\n";
    // dbgs() << "[RebaseDLPass] - Benefit: " << benefit << "\n";
    // dbgs() << "[RebaseDLPass] - Cost: " << cost << "\n";
    // dbgs() << "[RebaseDLPass] - net: " << this->costBenefit << "\n";
  }

  bool isBeneficial() {
    if (this->costBenefitRatio.has_value())
      return this->costBenefitRatio < 0.5;

    return false;
  }

  void dump(const DataLayout &DL, LoopInfo &LI) {
    dbgs() << "[RebaseDLPass] RegionPackingCandidate ===========\n";
    dbgs() << "[RebaseDLPass] Target loop: " << this->targetLoop->getName()
           << "\n";
    if (this->targetLoop->getStartLoc()) {
      dbgs() << "[RebaseDLPass] - " << *this->targetLoop->getStartLoc() << "\n";
    }
    dbgs() << "[RebaseDLPass] - depth: " << this->targetLoop->getLoopDepth()
           << "\n";
    if (this->cacheUtilization.has_value())
      dbgs() << "[RebaseDLPass] Cache utilization: "
             << format("%.3f", this->cacheUtilization.value()) << "\n";
    if (this->memRegImpact.has_value())
      dbgs() << "[RebaseDLPass] Cache impact: "
             << format("%.3f", this->memRegImpact.value()) << "\n";
    if (this->costBenefitRatio.has_value())
      dbgs() << "[RebaseDLPass] Cost benefit: " << format("%.8f", this->costBenefitRatio.value())
             << "\n";
    this->memReg.dump(DL, this->targetLoop);
    dbgs() << "[RebaseDLPass] ==================================\n";
    dbgs() << "[RebaseDLPass] \n";
  }
};

void runOnOuterLoop(Loop *outerLoop, DenseSet<Loop *> &copyLoops,
                    const DataLayout &DL, LoopInfo &LI, ScalarEvolution &SE,
                    AliasAnalysis &AA, BlockFrequencyInfo &BFI, DominatorTree &DT) {

  // Skip copy loops created by this pass
  if (copyLoops.count(outerLoop) != 0)
    return;

  // Get pointers used in outer loop
  auto ptrsUsed = getPtrsUsedInLoop(outerLoop);
  if (ptrsUsed.empty()) {
    // dbgs() << "[RebaseDLPass] No ptrs used in loop\n";
    return;
  }

  // Get loads that use the pointer in the loop
  SmallVector<LoadInst *> ptrsLoads;
  for (Value *pointer : ptrsUsed) {
    for (auto pointerLoad : pointer->users()) {
      if (LoadInst *instruction = dyn_cast<LoadInst>(pointerLoad)) {
        if (outerLoop->contains(instruction)) {
          ptrsLoads.push_back(instruction);
        }
      }
    }
  }
  // Give up if there are no loads,
  // a loop with only stores is not a candidate for the transformation
  if (ptrsLoads.empty()) {
    // dbgs() << "[RebaseDLPass] No ptr loads in loop\n";
    return;
  }

  // Check if there are pointer loads at least at a loop depth of 2
  unsigned maxLoopDepth = 0;
  const int requiredLoopDepth = 2;
  for (LoadInst *pointerLoad : ptrsLoads) {
    maxLoopDepth =
        std::max(maxLoopDepth, LI.getLoopDepth(pointerLoad->getParent()));
    if (maxLoopDepth > requiredLoopDepth) {
      break;
    }
  }
  if (maxLoopDepth < requiredLoopDepth) {
    // dbgs() << "[RebaseDLPass] Loop is too shallow\n";
    return;
  }

  // Separate ptrs that access different objects
  // based on their underlying objects
  SmallVector<RegionPackingMemReg> memRegs;
  for (Value *pointer : ptrsUsed) {

    // Create new memReg of a single pointer
    RegionPackingMemReg newMemReg{pointer, DL};

    // The memReg may be empty if the pointer
    // has only gep users
    if (newMemReg.empty()) {
      continue;
    }

    // Try to find an existing memReg that intersects with the new one
    bool found = false;
    auto it = memRegs.begin();
    for (; it != memRegs.end(); ++it) {
      if (it->intersects(newMemReg, AA)) {
        found = true;
        break;
      }
    }

    if (found) {
      // Merge new memReg to the existing one that intersects
      auto mergingMemReg = it;
      mergingMemReg->merge(newMemReg);
      ++it;

      // Check if the merged memReg intersects with any other memReg 'X'
      // if it does, merge 'X' to the merging memReg and
      // erase 'X' from the list of memRegs
      while (it != memRegs.end()) {
        if (it->intersects(*mergingMemReg, AA)) {
          mergingMemReg->merge(*it);
          it = memRegs.erase(it);
        } else {
          ++it;
        }
      }
    } else {
      memRegs.push_back(newMemReg);
    }
  }

  // Get all nested loops including outermost loop
  auto loopNest = outerLoop->getLoopsInPreorder();
  SmallVector<RegionPackingCandidate> candidates;

  // Add candidates that show reuse
  for (Loop *subloop : loopNest) {
    for (RegionPackingMemReg &memReg : memRegs) {
      // Candidate has to be loaded in the subloop
      // has to have a load that is variant to a child loop of subloop
      // and must be invariant to subloop
      if (memReg.isLoadedInLoop(subloop) &&
          memReg.isVariantToChildLoop(subloop, LI, SE) &&
          memReg.isInvariantToLoop(subloop, SE)) {
        candidates.push_back(RegionPackingCandidate(&memReg, subloop, DL));
      }
    }
  }
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass] No reuse\n";
    return;
  }

  // Remove candidates that would involve an interprocedural transformation
  candidates.erase(
      std::remove_if(candidates.begin(), candidates.end(),
                     [&DL, &SE, &AA](RegionPackingCandidate &attr) {
                       return attr.isInterprocedural(DL, SE, AA);
                     }),
      candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass] Interprocedural\n";
    return;
  }

  // Remove illegal candidates
  candidates.erase(
      std::remove_if(candidates.begin(), candidates.end(),
                     [&DL, &SE, &AA, &LI](RegionPackingCandidate &attr) {
                       return !attr.isLegal(DL, SE, AA, LI);
                     }),
      candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass] Not legal\n";
    return;
  }

  // Compute benefit of remaining candidates
  for (RegionPackingCandidate &candidate : candidates) {
    candidate.computeCostBenefit(memRegs, DL, SE, LI, BFI, DT);
  }
  // Remove candidates that are not beneficial
  candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
                                  [](RegionPackingCandidate &attr) {
                                    return !attr.isBeneficial();
                                  }),
                   candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass] Not Beneficial\n";
    return;
  }

  // Greedy selection of candidates
  SmallVector<RegionPackingCandidate *> greedyCandidates;

  // Sort candidates options from best to worst options according to the
  // gain/cost.
  std::sort(candidates.begin(), candidates.end(),
            std::greater<RegionPackingCandidate>());

  // Select candidates
  for (auto &candidate : candidates) {
    if (greedyCandidates.empty()) {
      greedyCandidates.push_back(&candidate);
      continue;
    }

    bool shouldSelect = true;
    for (auto *greedyCandidate : greedyCandidates) {
      // Trying to pack an intersecting memReg
      // should only pack if selected memRegs are independent.
      if (candidate.memReg.intersects(greedyCandidate->memReg, AA)) {
        if (candidate.targetLoop->contains(greedyCandidate->targetLoop) ||
            greedyCandidate->targetLoop->contains(candidate.targetLoop)) {
          shouldSelect = false;
          break;
        }
      }
    }
    if (shouldSelect)
      greedyCandidates.push_back(&candidate);
  }

  // Print candidates
  if (!greedyCandidates.empty()) {
    dbgs() << "[RebaseDLPass] ================= Module name "
           << outerLoop->block_begin()[0]->getModule()->getName() << "\n";
    dbgs() << "[RebaseDLPass] ================= Function name "
           << outerLoop->block_begin()[0]->getParent()->getName() << "\n";
  }
  for (RegionPackingCandidate *candidate : greedyCandidates) {
    candidate->dump(DL, LI);
  }
}

PreservedAnalyses RebaseDLPass::run(Function &F,
                                              FunctionAnalysisManager &FAM) {
  // Get data layout of module
  Module *M = F.getParent();
  const DataLayout &DL = M->getDataLayout();

  // Get analyses
  LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);
  AliasAnalysis &AA = FAM.getResult<AAManager>(F);
  BlockFrequencyInfo &BFI = FAM.getResult<BlockFrequencyAnalysis>(F);
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);

  // Stores loops created by this pass
  DenseSet<Loop *> copyLoops;

  // if (F.getName() == "build_domain_forest")
  //   F.print(dbgs());

  for (auto loop : LI.getTopLevelLoops()) {
    runOnOuterLoop(loop, copyLoops, DL, LI, SE, AA, BFI, DT);
  }

  return PreservedAnalyses::all();
}

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
// Register in pipeline:

PassPluginLibraryInfo getRebaseDLPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
    PB.registerFullLinkTimeOptimizationLastEPCallback([&](ModulePassManager &MPM, auto) {
      MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LoopRotatePass())));
      MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LICMPass(LICMOptions()), /*UseMemorySSA*/ true)));
      MPM.addPass(createModuleToFunctionPassAdaptor(RebaseDLPass()));
      return true;
    });

    // PB.registerVectorizerStartEPCallback([&](FunctionPassManager &FPM, auto) {
    //   FPM.addPass(createFunctionToLoopPassAdaptor(LoopRotatePass()));
    //   FPM.addPass(createFunctionToLoopPassAdaptor(LICMPass(LICMOptions()), /*UseMemorySSA*/ true));
    //   FPM.addPass(RebaseDLPass());
    //   return true;
    // });

    PB.registerPipelineParsingCallback(
      [](StringRef Name, llvm::FunctionPassManager &PM,
         ArrayRef<llvm::PassBuilder::PipelineElement>) {
        if (Name == "rebasedl") {
          PM.addPass(RebaseDLPass());
          return true;
        }
        return false;
      });
  };

  return {LLVM_PLUGIN_API_VERSION, "rebasedl-pass", "0.0.1", callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getRebaseDLPassPluginInfo();
}
