#include "RebaseDL.h"
#include <llvm/ADT/SmallSet.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/BlockFrequencyInfo.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>
#include <llvm/Transforms/Scalar/LICM.h>
#include <llvm/Transforms/Scalar/LoopRotation.h>

using namespace llvm;

inline uint64_t ceilDiv(uint64_t numerator, uint64_t denominator) {
  return (numerator / denominator + (numerator % denominator != 0));
}

// Returns a set with all pointers that have uses in a loop
SetVector<Value *> getPtrsUsedInLoop(Loop *loop) {
  SetVector<Value *> ptrs;
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

// Returns vector with all instructions of type T in a loop L
template <typename T> SmallVector<T *> getInstructionsInLoop(Loop *L) {
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

template <class S1Ty, class S2Ty>
static bool hasIntersection(S1Ty S1, S2Ty S2) {
  for (typename S1Ty::iterator I = S1.begin(); I != S1.end(); ++I) {
    if (S2.count(*I) != 0)
      return true;
  }
  return false;
}

// From ScalarEvolution.cpp, but relaxed to not loop at dominance
bool isSCEVInvariantToLoop(const SCEV *S, const Loop *L) {
  switch (S->getSCEVType()) {
  case scConstant:
  case scVScale:
    return true;
  case scAddRecExpr: {
    const SCEVAddRecExpr *AR = cast<SCEVAddRecExpr>(S);

    // If L is the addrec's loop, it's variant.
    if (AR->getLoop() == L)
      return false;

    // Add recurrences are never invariant in the function-body (null loop).
    if (!L)
      return false;

    // This recurrence is invariant w.r.t. L if AR's loop contains L.
    if (AR->getLoop()->contains(L))
      return true;

    // This recurrence is variant w.r.t. L if any of its operands
    // are variant.
    for (const auto *Op : AR->operands())
      if (!isSCEVInvariantToLoop(Op, L))
        return false;

    // Otherwise it's loop-invariant.
    return true;
  }
  case scTruncate:
  case scZeroExtend:
  case scSignExtend:
  case scPtrToInt:
  case scAddExpr:
  case scMulExpr:
  case scUDivExpr:
  case scUMaxExpr:
  case scSMaxExpr:
  case scUMinExpr:
  case scSMinExpr:
  case scSequentialUMinExpr: {
    for (const auto *Op : S->operands())
      if (!isSCEVInvariantToLoop(Op, L))
        return false;
    return true;
  }
  case scUnknown:
    // All non-instruction values are loop invariant.  All instructions are loop
    // invariant if they are not contained in the specified loop.
    // Instructions are never considered invariant in the function body
    // (null loop) because they are defined within the "loop".
    if (auto *I = dyn_cast<Instruction>(cast<SCEVUnknown>(S)->getValue()))
      return L && !L->contains(I);
    return true;
  case scCouldNotCompute:
    llvm_unreachable("Attempt to use a SCEVCouldNotCompute object!");
  }
  llvm_unreachable("Unknown SCEV kind!");
}

// Check if pointer is invariant a loop
bool isPtrInvariantToLoop(Loop *loop, Value *ptr, ScalarEvolution &SE) {
  const SCEV *scev = SE.getSCEV(ptr);
  return isSCEVInvariantToLoop(scev, loop);
}

// This function is from ValueTracking, updated here to be uniform with
// stripAndAccumulateConstantOffsets, which is also updated here
const Value *getUnderlyingObjectRebaseDL(const Value *V) {
  if (!V->getType()->isPointerTy())
    return V;

  // Even though we don't look through PHI nodes, we could be called on an
  // instruction in an unreachable block, which may be on a cycle.
  SmallPtrSet<const Value *, 4> Visited;
  Visited.insert(V);
  do {
    if (auto *GEP = dyn_cast<GEPOperator>(V)) {
      V = GEP->getPointerOperand();
    } else if (Operator::getOpcode(V) == Instruction::BitCast ||
               Operator::getOpcode(V) == Instruction::AddrSpaceCast) {
      V = cast<Operator>(V)->getOperand(0);
    } else if (auto *GA = dyn_cast<GlobalAlias>(V)) {
      if (!GA->isInterposable())
        V = GA->getAliasee();
    } else if (const auto *Call = dyn_cast<CallBase>(V)) {
      if (auto *RP = getArgumentAliasingToReturnedPointer(Call, false))
        V = RP;
    } else if (auto *PHI = dyn_cast<PHINode>(V)) {
      // Look through single-arg phi nodes created by LCSSA.
      if (PHI->getNumIncomingValues() == 1)
        V = PHI->getIncomingValue(0);
    }
    assert(V->getType()->isPtrOrPtrVectorTy() && "Unexpected operand type!");
  } while (Visited.insert(V).second);

  return V;
}
inline Value *getUnderlyingObjectRebaseDL(Value *V) {
  // Force const to avoid infinite recursion.
  const Value *VConst = V;
  return const_cast<Value *>(getUnderlyingObjectRebaseDL(VConst));
}

// This function is from ValueTracking, updated here to be uniform with
// stripAndAccumulateConstantOffsets, which is also updated here
void getUnderlyingObjectsRebaseDL(const Value *V,
                                  SmallVectorImpl<const Value *> &Objects) {
  SmallPtrSet<const Value *, 4> Visited;
  SmallVector<const Value *, 4> Worklist;
  Worklist.push_back(V);
  do {
    const Value *P = Worklist.pop_back_val();
    P = getUnderlyingObjectRebaseDL(P);

    if (!Visited.insert(P).second)
      continue;

    if (auto *SI = dyn_cast<SelectInst>(P)) {
      Worklist.push_back(SI->getTrueValue());
      Worklist.push_back(SI->getFalseValue());
      continue;
    }

    if (auto *PN = dyn_cast<PHINode>(P)) {
      append_range(Worklist, PN->incoming_values());
      continue;
    }

    Objects.push_back(P);
  } while (!Worklist.empty());
}

// This function is from Value, updated here to be uniform with
// getUnderlyingObject, which is also updated here
const Value *stripAndAccumulateConstantOffsetsRebaseDL(
    const Value *V, const DataLayout &DL, APInt &Offset, bool AllowNonInbounds,
    bool AllowInvariantGroup,
    function_ref<bool(Value &, APInt &)> ExternalAnalysis,
    SmallVectorImpl<const GEPOperator *> *geps) {

  if (!V->getType()->isPtrOrPtrVectorTy())
    return V;

  unsigned BitWidth = Offset.getBitWidth();
  assert(BitWidth == DL.getIndexTypeSizeInBits(getType()) &&
         "The offset bit width does not match the DL specification.");

  // Even though we don't look through PHI nodes, we could be called on an
  // instruction in an unreachable block, which may be on a cycle.
  SmallPtrSet<const Value *, 4> Visited;
  Visited.insert(V);
  do {
    if (auto *GEP = dyn_cast<GEPOperator>(V)) {
      // If in-bounds was requested, we do not strip non-in-bounds GEPs.
      if (!AllowNonInbounds && !GEP->isInBounds())
        return V;

      // If one of the values we have visited is an addrspacecast, then
      // the pointer type of this GEP may be different from the type
      // of the Ptr parameter which was passed to this function.  This
      // means when we construct GEPOffset, we need to use the size
      // of GEP's pointer type rather than the size of the original
      // pointer type.
      APInt GEPOffset(DL.getIndexTypeSizeInBits(V->getType()), 0);
      if (!GEP->accumulateConstantOffset(DL, GEPOffset, ExternalAnalysis))
        return V;

      // Stop traversal if the pointer offset wouldn't fit in the bit-width
      // provided by the Offset argument. This can happen due to AddrSpaceCast
      // stripping.
      if (GEPOffset.getSignificantBits() > BitWidth)
        return V;

      // External Analysis can return a result higher/lower than the value
      // represents. We need to detect overflow/underflow.
      APInt GEPOffsetST = GEPOffset.sextOrTrunc(BitWidth);
      if (!ExternalAnalysis) {
        Offset += GEPOffsetST;
      } else {
        bool Overflow = false;
        APInt OldOffset = Offset;
        Offset = Offset.sadd_ov(GEPOffsetST, Overflow);
        if (Overflow) {
          Offset = OldOffset;
          return V;
        }
      }
      V = GEP->getPointerOperand();
      if (geps)
        geps->push_back(GEP);
    } else if (Operator::getOpcode(V) == Instruction::BitCast ||
               Operator::getOpcode(V) == Instruction::AddrSpaceCast) {
      V = cast<Operator>(V)->getOperand(0);
    } else if (auto *GA = dyn_cast<GlobalAlias>(V)) {
      if (!GA->isInterposable())
        V = GA->getAliasee();
    } else if (const auto *Call = dyn_cast<CallBase>(V)) {
      if (auto *RP = getArgumentAliasingToReturnedPointer(Call, false))
        V = RP;
    } else if (auto *PHI = dyn_cast<PHINode>(V)) {
      // Look through single-arg phi nodes created by LCSSA.
      if (PHI->getNumIncomingValues() == 1)
        V = PHI->getIncomingValue(0);
    }
    assert(V->getType()->isPtrOrPtrVectorTy() && "Unexpected operand type!");
  } while (Visited.insert(V).second);

  return V;
}

/// This is a wrapper around Value::stripAndAccumulateConstantOffsets that
/// creates and later unpacks the required APInt.
inline const Value *getPointerBaseWithConstantOffsetRebaseDL(
    const Value *Ptr, int64_t &Offset, const DataLayout &DL,
    SmallVectorImpl<const GEPOperator *> *geps = nullptr,
    bool AllowNonInbounds = true, bool AllowInvariantGroup = false) {
  // Offset is zero for non constant sequential indexes
  auto ExternalAnalysis = [](Value &operand, APInt &offset) -> bool {
    offset = 0;
    return true;
  };

  APInt OffsetAPInt(DL.getIndexTypeSizeInBits(Ptr->getType()), 0);
  const Value *Base = stripAndAccumulateConstantOffsetsRebaseDL(
      Ptr, DL, OffsetAPInt, AllowNonInbounds, AllowInvariantGroup,
      ExternalAnalysis, geps);

  Offset = OffsetAPInt.getSExtValue();
  return Base;
}
inline Value *getPointerBaseWithConstantOffsetRebaseDL(
    Value *Ptr, int64_t &Offset, const DataLayout &DL,
    SmallVectorImpl<const GEPOperator *> *geps = nullptr,
    bool AllowNonInbounds = true, bool AllowInvariantGroup = false) {
  const Value *PtrConst = Ptr;
  return const_cast<Value *>(getPointerBaseWithConstantOffsetRebaseDL(
      PtrConst, Offset, DL, geps, AllowNonInbounds, AllowInvariantGroup));
}

std::optional<int64_t> getMinConstOffset(SmallVector<Instruction *> &loadStores,
                                         const DataLayout &DL) {
  std::optional<int64_t> minOffset;

  // Get the minimum base offset of all geps
  for (auto inst : loadStores) {
    Value *ptr = getLoadStorePointerOperand(inst);
    if (!ptr)
      return std::nullopt;

    int64_t constOffset;
    getPointerBaseWithConstantOffsetRebaseDL(ptr, constOffset, DL);

    if (!minOffset)
      minOffset = constOffset;
    else
      minOffset = std::min(minOffset.value(), constOffset);
  }

  return minOffset;
}

// Visitor to collect the step of the add recurrence of \p loop.
struct SCEVCollectStep {
  ScalarEvolution &SE;
  Loop *loop;
  const SCEV *&step;

  SCEVCollectStep(ScalarEvolution &SE, const SCEV *&S, Loop *loop)
      : SE(SE), loop{loop}, step(S) {}

  bool follow(const SCEV *S) {
    if (auto addRecSCEV = dyn_cast<SCEVAddRecExpr>(S)) {
      if (addRecSCEV->getLoop() == this->loop) {
        this->step = addRecSCEV->getStepRecurrence(SE);
        return true;
      }
    }
    return false;
  }

  bool isDone() const { return false; }
};

// Returns the constant stride applied to the SCEV of the \p val by loop \p
// loop. If no stride is found, or if it is not constant, return 1.
int64_t getLoopStride(Value *val, Loop *loop, ScalarEvolution &SE) {
  int64_t stride = 1;
  const SCEV *scev = SE.getSCEV(val);

  const SCEV *stepSCEV = nullptr;
  SCEVCollectStep collectstep(SE, stepSCEV, loop);
  visitAll(scev, collectstep);

  // TODO: what to do if there is more than one stride scev?
  //       or if not constant

  // Try to get constant step
  if (stepSCEV)
    if (auto constantScev = dyn_cast<SCEVConstant>(stepSCEV))
      stride = constantScev->getValue()->getSExtValue();

  return stride;
}

/// Estimates the offset applied to the pointer defined by a succession of gep
/// instructions (\p geps) and the base pointer \p basePtr between two
/// iterations of \p loop. Return nullopt if unknown
std::optional<uint64_t>
getLoopOffset(SmallVectorImpl<const GEPOperator *> &geps, Value *basePtr,
              Loop *loop, ScalarEvolution &SE, const DataLayout &DL) {
  if (geps.empty())
    return 0;

  uint64_t loopOffset = 0;

  // For all geps that are applied to the pointer
  for (auto gep : geps) {
    // Look at all gep operands, if the operand is sequential and variant to
    // the loop, the loop offset is the size of the indexed type multiplied by a
    // stride, if any
    for (gep_type_iterator GTI = gep_type_begin(gep), GTE = gep_type_end(gep);
         GTI != GTE; ++GTI) {
      Value *operand = GTI.getOperand();

      if (isPtrInvariantToLoop(loop, operand, SE))
        continue;

      // Give up it is a loop variant structure (non-sequential) index
      if (!GTI.isSequential())
        return std::nullopt;

      int64_t stride = getLoopStride(operand, loop, SE);
      // Don't use negative strides
      if (stride < 0)
        stride *= -1;

      loopOffset +=
          DL.getTypeAllocSize(GTI.getIndexedType()).getFixedValue() * stride;
    }
  }

  return loopOffset;
}

// Returns the constant trip count of the loop if known. It looks at the trip
// count of all exiting blocks and returns the maximum if there are multiple
// values. Otherwise returns the default value.
unsigned estimateLoopTripCount(Loop *loop, ScalarEvolution &SE,
                               unsigned defaultCount = 100) {
  unsigned tripCount = 0;
  SmallVector<BasicBlock *> ExitingBlocks;
  loop->getExitingBlocks(ExitingBlocks);
  for (BasicBlock *ExitingBlock : ExitingBlocks)
    if (unsigned exactCount = SE.getSmallConstantTripCount(loop, ExitingBlock))
      tripCount = std::max(tripCount, exactCount);

  if (!tripCount)
    tripCount = defaultCount;

  return tripCount;
}

// Returns the constant trip count of the loop if known. If not known, looks at
// the list of geps and checks if there is an operand that varies with the loop
// and that accesses a vector or array of constant size, if it does, returns the
// size of the array divided by the constant stride applied to the operant, if
// any. Otherwise it returns default value.
unsigned estimateLoopTripCount(SmallVectorImpl<const GEPOperator *> &geps,
                               Loop *loop, ScalarEvolution &SE,
                               const DataLayout &DL,
                               unsigned defaultCount = 100) {

  // If there is a exact trip count, return it
  if (unsigned exactCount = estimateLoopTripCount(loop, SE, /*defaulCount*/ 0))
    return exactCount;

  // If pointer is not computed by gep, give up
  if (geps.empty())
    return defaultCount;

  unsigned tripCount = 0;

  // Initialize type as type of the base ptr
  Type *previousTy = geps.back()->getSourceElementType();

  // Look at the gep instructions in reverse order, the last gep in the list
  // uses the base pointer as an operand and the first gep in the list produces
  // the final pointer
  for (auto it = geps.rbegin(); it != geps.rend(); ++it) {
    const GEPOperator *gep = *it;

    // Look at the operands from first to last
    for (gep_type_iterator GTI = gep_type_begin(gep), GTE = gep_type_end(gep);
         GTI != GTE; ++GTI) {
      Value *operand = GTI.getOperand();

      // Skip if the operand is not sequential or invariant to loop
      if (!GTI.isSequential() || isPtrInvariantToLoop(loop, operand, SE)) {
        previousTy = GTI.getIndexedType();
        continue;
      }

      int64_t stride = getLoopStride(operand, loop, SE);
      // Don't use negative strides
      if (stride < 0)
        stride *= -1;

      // Use the previous and not the current type because if the IV accesses
      // a vector its indexed type will be the type of the elements of the
      // vector. The previous indexed type will be a vector of that element
      // type.
      if (auto arrTy = dyn_cast<ArrayType>(previousTy)) {
        unsigned arrTrip = (unsigned)ceilDiv(arrTy->getNumElements(), stride);
        tripCount = std::max(tripCount, arrTrip);
      } else if (auto vecTy = dyn_cast<FixedVectorType>(previousTy)) {
        unsigned vecTrip = (unsigned)ceilDiv(vecTy->getNumElements(), stride);
        tripCount = std::max(tripCount, vecTrip);
      }

      previousTy = GTI.getIndexedType();
    }
  }

  // If still unknown, return default
  if (!tripCount)
    tripCount = defaultCount;

  return tripCount;
}

// Simulate bytes and cache lines accessed by the load and store instructions
// in \p loadStores in \p targetLoop. It maps bytes and cache lines accessed to
// unlimited contiguous memory, but it stops if the size surpasses \p
// cacheMaxSizeInKB.
//
// The mapping of accesses is done by looking at the constant offset and loop
// (dependent) offsets applied to the pointers of loads and stores in \p
// targetLoop.
void countBytesAndCacheLinesAccessed(SmallVector<Instruction *> &loadStores,
                                     Loop *targetLoop, const DataLayout &DL,
                                     ScalarEvolution &SE, LoopInfo &LI,
                                     uint64_t &bytesAccessed,
                                     uint64_t &cacheLinesAccessed,
                                     const int cacheLineSize = 64,
                                     const int cacheMaxSizeInKB = 8000) {
  if (loadStores.empty())
    return;

  // Save ptrs counted to avoid double counting loads and stores that use the
  // same ptr
  SmallSet<Value *, 4> ptrsCounted;

  // Smallest base offset. Used to avoid simulating that the first field of a
  // structure accessed is at the end of a cache line, thus bringing more cache
  // lines than actually needed
  std::optional<int64_t> minConstOffset = getMinConstOffset(loadStores, DL);
  if (!minConstOffset)
    return;

  // Maps bytes accessed. A set bit is a bytes that was accessed.
  // Size limited to \p cacheMaxSizeInKB.
  BitVector bytesAccessedMap{};

  for (auto inst : loadStores) {
    Value *ptr = getLoadStorePointerOperand(inst);
    // If ptr was already counted, skip it
    if (!ptrsCounted.insert(ptr).second)
      continue;

    // Compute constant offset of ptr and save geps that are applied to the ptr
    int64_t constOffset;
    SmallVector<const GEPOperator *> geps;
    Value *basePtr =
        getPointerBaseWithConstantOffsetRebaseDL(ptr, constOffset, DL, &geps);

    // Get size of field accessed by the load/store
    Type *ty = getLoadStoreType(inst);
    if (!ty || !ty->isSized())
      return;
    TypeSize fieldSize = DL.getTypeAllocSize(ty);

    // dbgs() << "[RebaseDLPass]---- load/store: " << *inst << "\n";
    // dbgs() << "[RebaseDLPass] fieldSize: " << fieldSize << "\n";
    // dbgs() << "[RebaseDLPass] costant offset: " << constOffset << "\n";

    // Store trip count and loop offset of loops to which the ptr is variant
    SmallVector<std::pair<unsigned, uint64_t>> tripCountAndLoopOffsets;
    Loop *currLoop = LI.getLoopFor(inst->getParent());

    while (currLoop != targetLoop) {
      if (isPtrInvariantToLoop(currLoop, ptr, SE)) {
        currLoop = currLoop->getParentLoop();
        continue;
      }

      // Compute loop offset of ptr based on the geps applied to it
      std::optional<uint64_t> loopOffset =
          getLoopOffset(geps, basePtr, currLoop, SE, DL);
      if (!loopOffset.has_value())
        return;

      assert(loopOffset != 0 && "Why is loop offset zero?");

      unsigned tripCount = estimateLoopTripCount(geps, currLoop, SE, DL);
      tripCountAndLoopOffsets.push_back({tripCount, loopOffset.value()});

      // dbgs() << "[RebaseDLPass] variant loop and depth: "
      //        << currLoop->getName()
      //        << " " << currLoop->getLoopDepth() << "\n";
      // dbgs() << "[RebaseDLPass] loop offset: " << loopOffset.value() << "\n";
      // dbgs() << "[RebaseDLPass] trip count: " << tripCount << "\n";

      currLoop = currLoop->getParentLoop();
    }

    // Compute total trip count of the loops
    unsigned totalTripCount = 1;
    for (auto tlPair : tripCountAndLoopOffsets) {
      unsigned tripCount = tlPair.first;
      totalTripCount *= tripCount;
    }

    // Consider the accesses to all iterations in all loops
    for (unsigned i = 0; i < totalTripCount; i++) {
      int loopPart = 0;
      int accumulatedTripCounts = 1;
      for (auto tlPair : tripCountAndLoopOffsets) {
        unsigned tripCount = tlPair.first;
        unsigned loopOffset = tlPair.second;
        // Decompose iteration i of the total trip count into the iteration of
        // the current loop
        int loopIter = (i / accumulatedTripCounts) % tripCount;
        // Multiply the iteration of a loop by its loop offset
        loopPart += loopIter * loopOffset;
        accumulatedTripCounts *= tripCount;
      }

      // First and last bytes of the access
      unsigned start = loopPart + (constOffset - minConstOffset.value());
      unsigned end = start + fieldSize;

      // End mapping if it is too big
      if (end > cacheMaxSizeInKB * 1000) {
        dbgs() << "[RebaseDLPass][Warning] Bytes accessed  is too big";
        break;
      }

      // Resize bitvector if needed
      if (bytesAccessedMap.size() < end)
        bytesAccessedMap.resize(end);

      // Set the bits corresponding to the access
      bytesAccessedMap.set(start, end);
    }
  }

  // Count how many bytes were mapped
  bytesAccessed = bytesAccessedMap.count();

  cacheLinesAccessed = 0;
  unsigned lineNum = ceilDiv(bytesAccessedMap.size(), cacheLineSize);

  // For each cache line and for each byte in it, add a cache line accessed if
  // one of the bytes of a line is set
  for (unsigned line = 0; line < lineNum; ++line) {
    for (unsigned byte = 0; byte < cacheLineSize; ++byte) {
      unsigned index = line * cacheLineSize + byte;

      if (index >= bytesAccessedMap.size())
        break;

      if (bytesAccessedMap.test(line * cacheLineSize + byte)) {
        cacheLinesAccessed++;
        break;
      }
    }
  }
}

// A collection of pointers that point to the same region of memory assuming a
// contiguous allocation from a base pointer
class RegionPackingMemReg {
public:
  // List of pointers that point to the same memory region
  SmallSet<Value *, 4> ptrs;
  // Base pointer, it can be multiple pointers if two pointers are aliases
  SmallSet<Value *, 1> basePtrs;
  // Underlying objects, similar from base pointers, but these are obtained by
  // going through phi instructions if a base pointer may have multiple values
  SmallSet<const Value *, 1> underlyingObjects;

  RegionPackingMemReg(){};

  RegionPackingMemReg(Value *ptrVal, const DataLayout &DL) {
    this->addPtr(ptrVal, DL);
  };

  // Add a pointer, its base pointer and its underlying objects
  void addPtr(Value *ptrVal, const DataLayout &DL) {
    if (!ptrVal->getType()->isPointerTy())
      return;

    this->ptrs.insert(ptrVal);
    this->basePtrs.insert(getUnderlyingObjectRebaseDL(ptrVal));

    SmallVector<const Value *> objs{};
    getUnderlyingObjectsRebaseDL(ptrVal, objs);
    for (auto obj : objs)
      this->underlyingObjects.insert(obj);
  }

  bool empty() { return this->ptrs.empty(); }

  // True if the set base pointers of this MemReg intersects with
  // the base pointers of another MemReg. Also true if the base
  // pointers of these objects must alias.
  bool intersects(RegionPackingMemReg &other, AliasAnalysis &AA) {
    if (hasIntersection(this->basePtrs, other.basePtrs))
      return true;

    // TODO: check for partial alias
    for (auto thisBase : this->basePtrs) {
      for (auto otherBase : other.basePtrs) {
        auto aliasResult = AA.alias(thisBase, otherBase);
        if (aliasResult == AliasResult::MustAlias)
          return true;
      }
    }

    return false;
  }

  // Merge the pointer, base pointers, and underlying objects of another
  // MemReg to this MemReg
  void merge(RegionPackingMemReg &other) {
    set_union(this->ptrs, other.ptrs);
    set_union(this->basePtrs, other.basePtrs);
    set_union(this->underlyingObjects, other.underlyingObjects);
  }

  // Check if one of the pointers of this MemReg is loaded in a loop
  bool isLoadedInLoop(Loop *loop) {
    SmallVector<LoadInst *> loads = getInstructionsInLoop<LoadInst>(loop);
    for (auto load : loads)
      if (this->ptrs.contains(load->getPointerOperand()))
        return true;

    return false;
  }

  // Check if one of the pointers of this MemReg is stored in a loop
  bool isStoredInLoop(Loop *loop) {
    SmallVector<StoreInst *> stores = getInstructionsInLoop<StoreInst>(loop);
    for (auto store : stores)
      if (this->ptrs.contains(store->getPointerOperand()))
        return true;

    return false;
  }

  // Returns true if this MemReg has a load that
  // is variant to a child loop of \p parentLoop
  bool isVariantToChildLoop(Loop *parentLoop, LoopInfo &LI,
                            ScalarEvolution &SE) {
    auto loopNest = parentLoop->getLoopsInPreorder();

    SmallVector<LoadInst *> loads = getInstructionsInLoop<LoadInst>(parentLoop);
    for (auto load : loads) {
      // Skip if this load is not from this MemReg
      if (!this->ptrs.contains(load->getPointerOperand()))
        continue;

      for (auto loop : loopNest) {
        // Skip parent loop
        if (loop == parentLoop)
          continue;

        if (loop->contains(load) &&
            !isPtrInvariantToLoop(loop, load->getPointerOperand(), SE)) {
          return true;
        }
      }
    }

    return false;
  }

  // Check if the pointers of this MemReg are invariant to a loop
  bool isInvariantToLoop(Loop *loop, ScalarEvolution &SE) {
    for (auto ptr : this->ptrs)
      if (!isPtrInvariantToLoop(loop, ptr, SE))
        return false;
    return true;
  }

  // Get loads and store instructions of this memReg that are
  // in \p loop
  SmallVector<Instruction *> getLoadStoresInLoop(Loop *loop) {
    SmallVector<Instruction *> loadStores;

    SmallVector<LoadInst *> loads = getInstructionsInLoop<LoadInst>(loop);
    for (auto load : loads)
      if (this->ptrs.contains(load->getPointerOperand()))
        loadStores.push_back(load);

    SmallVector<StoreInst *> stores = getInstructionsInLoop<StoreInst>(loop);
    for (auto store : stores)
      if (this->ptrs.contains(store->getPointerOperand()))
        loadStores.push_back(store);

    return loadStores;
  }

  // Print information about this MemReg such as load and store that use it.
  // If \p targetLoop is not null, only instructions loads and stores inside
  // \p target loop are printed.
  void dump(const DataLayout &DL, Loop *targetLoop = nullptr) {
    dbgs() << "[RebaseDLPass] Memreg: ------------------\n";

    SmallVector<LoadInst *> loads;
    SmallVector<StoreInst *> stores;
    SmallVector<User *> otherUsers;

    for (auto ptrVal : this->ptrs) {
      for (auto user : ptrVal->users()) {
        // Load uses ptrVal
        if (auto loadInst = dyn_cast<LoadInst>(user)) {
          if (ptrVal == loadInst->getPointerOperand() &&
              (!targetLoop || targetLoop->contains(loadInst))) {
            loads.push_back(loadInst);
          }
          // Store uses ptrVal as the pointer operand
        } else if (auto storeInst = dyn_cast<StoreInst>(user)) {
          if (ptrVal == storeInst->getPointerOperand() &&
              (!targetLoop || targetLoop->contains(storeInst))) {
            stores.push_back(storeInst);
          }
        } else if (auto inst = dyn_cast<Instruction>(user)) {
          if (!targetLoop || targetLoop->contains(inst))
            otherUsers.push_back(user);
        }
      }
    }

    if (!loads.empty()) {
      dbgs() << "[RebaseDLPass] - Loads:\n";
      for (auto load : loads) {
        dbgs() << "[RebaseDLPass]     - " << *load << "\n";
        if (load->getDebugLoc()) {
          dbgs() << "[RebaseDLPass]         - " << *load->getDebugLoc() << "\n";
        }
      }
    }

    if (!stores.empty()) {
      dbgs() << "[RebaseDLPass] - Stores:\n";
      for (auto store : stores) {
        dbgs() << "[RebaseDLPass]     - " << *store << "\n";
        if (store->getDebugLoc()) {
          dbgs() << "[RebaseDLPass]         - " << *store->getDebugLoc()
                 << "\n";
        }
      }
    }

    if (!otherUsers.empty()) {
      dbgs() << "[RebaseDLPass] - Other Users:\n";
      for (auto user : otherUsers) {
        if (auto inst = dyn_cast<Instruction>(user)) {
          dbgs() << "[RebaseDLPass]     - " << *inst << "\n";
          if (inst->getDebugLoc()) {
            dbgs() << "[RebaseDLPass]         - " << *inst->getDebugLoc()
                   << "\n";
          }
        } else {
          dbgs() << "[RebaseDLPass]     - " << *user << "\n";
        }
      }
    }

    dbgs() << "[RebaseDLPass] - Base pointer(s):\n";
    for (auto basePtr : this->basePtrs) {
      if (auto inst = dyn_cast<Instruction>(basePtr)) {
        dbgs() << "[RebaseDLPass]     - " << *inst << "\n";
        if (inst->getDebugLoc()) {
          dbgs() << "[RebaseDLPass]         - " << *inst->getDebugLoc() << "\n";
        }
      } else {
        dbgs() << "[RebaseDLPass]     - " << *basePtr << "\n";
      }

      for (auto user : basePtr->users()) {
        if (auto *GEP = dyn_cast<GEPOperator>(user)) {
          dbgs() << "[RebaseDLPass]     - Type: "
                 << *GEP->getSourceElementType() << "\n";
          break;
        }
      }
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

    dbgs() << "[RebaseDLPass] --------------------------\n";
    dbgs() << "[RebaseDLPass] \n";
  }
};

// A candidate for the data layout transformation, defined by the memReg (what
// to transform) and the targetLoop (code region to apply transformation)
class RegionPackingCandidate {
public:
  // Target memory region for data layout transformation
  RegionPackingMemReg *memReg;
  // Target loop to apply the transformation
  Loop *targetLoop;
  // Relative frequency of execution of the loads/store
  // of this memReg in targetLoop
  std::optional<float> minAccessFrequency;
  // Ratio of bytes accessed by cache lines accessed
  std::optional<float> cacheUtilization;
  // Ratio of benefit/cost of this candidate
  std::optional<float> benefitCostRatio;

  RegionPackingCandidate(RegionPackingMemReg *memReg, Loop *loop,
                         const DataLayout &DL)
      : memReg{memReg}, targetLoop{loop} {}

  bool operator<(const RegionPackingCandidate &other) const {
    // First, order is based on benefit/cost
    if (this->benefitCostRatio.has_value() &&
        other.benefitCostRatio.has_value() &&
        this->benefitCostRatio.value() != other.benefitCostRatio.value()) {
      return this->benefitCostRatio.value() < other.benefitCostRatio.value();
    }

    // Second, based on cache utilization
    if (this->cacheUtilization.has_value() &&
        other.cacheUtilization.has_value() &&
        this->cacheUtilization.value() != other.cacheUtilization.value()) {
      return this->cacheUtilization.value() > other.cacheUtilization.value();
    }

    // Third, based on minAccessFrequency
    if (this->minAccessFrequency.has_value() &&
        other.minAccessFrequency.has_value() &&
        this->minAccessFrequency.value() != other.minAccessFrequency.value()) {
      return this->minAccessFrequency.value() <
             other.minAccessFrequency.value();
    }

    // If everything else fails/ties order based loop depth. The candidate with
    // the target loop that has the lowest depth is considered better because it
    // impacts a wider code region.
    return this->targetLoop->getLoopDepth() > other.targetLoop->getLoopDepth();
  }

  bool operator>(const RegionPackingCandidate &other) const {
    return other < *this;
  }

  // Check if one of the pointers of the memReg is an argument to a call
  // instruction
  bool isInterprocedural() {
    SmallVector<CallInst *> calls =
        getInstructionsInLoop<CallInst>(this->targetLoop);
    for (auto call : calls) {
      for (auto &arg : call->args()) {
        if (!arg->getType()->isPointerTy())
          continue;

        if (this->memReg->ptrs.contains(arg))
          return true;
      }
    }
    return false;
  }

  // Checks if it is legal to apply the transformation to this candidate
  bool isLegal(const DataLayout &DL, ScalarEvolution &SE, AliasAnalysis &AA,
               LoopInfo &LI) {

    // If the base ptr is variant to the loops inside the target loop,
    // or the target loop, give up, as the base may not always be the same
    for (auto basePtr : this->memReg->basePtrs) {
      for (auto loop : this->targetLoop->getLoopsInPreorder()) {
        if (loop != this->targetLoop &&
            !isPtrInvariantToLoop(loop, basePtr, SE)) {
          dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Base "
                    "pointer varies with loop inside target loop\n";
          return false;
        }
      }
    }

    // Get the loops that are variant to the candidate's memReg
    SmallVector<Loop *> loopsToBeCopied;
    for (Loop *loop : this->targetLoop->getLoopsInPreorder()) {
      if (loop != this->targetLoop &&
          !this->memReg->isInvariantToLoop(loop, SE)) {
        loopsToBeCopied.push_back(loop);
      }
    }

    // Must be able to determine bounds of loops to be copied for the
    // transformation, otherwise the transformation is illegal
    for (Loop *loop : loopsToBeCopied) {
      auto bounds = loop->getBounds(SE);
      if (bounds == std::nullopt) {
        dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Bounds not "
                  "found \n";
        return false;
      }

      Value *initialIVVal = &bounds->getInitialIVValue();
      Value *finalIVVal = &bounds->getFinalIVValue();
      Value *stepVal = bounds->getStepValue();

      // Bounds must be invariant to its parent loops inside the target loop
      Loop *currLoop = loop;
      while (currLoop != targetLoop->getParentLoop()) {
        if (!isPtrInvariantToLoop(currLoop, initialIVVal, SE) ||
            !isPtrInvariantToLoop(currLoop, finalIVVal, SE) ||
            !isPtrInvariantToLoop(currLoop, stepVal, SE)) {
          dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Bounds "
                    "variant to target loop nest\n";
          return false;
        }
        currLoop = currLoop->getParentLoop();
      }
    }

    // Get calls in the loop
    SmallVector<CallInst *> calls =
        getInstructionsInLoop<CallInst>(this->targetLoop);
    // Give up if
    for (auto call : calls) {
      // a call is indirect
      if (call->isIndirectCall()) {
        dbgs()
            << "[RebaseDLPass][Candidate Dismissed] Legality: Indirect call\n";
        return false;
      }

      Function *calledFunction = call->getCalledFunction();
      // ignore llvm functions
      if (calledFunction->isIntrinsic())
        continue;

      // a call is to a function not defined in the module
      if (!calledFunction || calledFunction->isDeclaration()) {
        dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Called "
                  "function not found: "
               << *call << "\n";
        return false;
      }

      // a call is recursive
      if (calledFunction == call->getFunction()) {
        dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Called "
                  "function is recursive\n";
        return false;
      }
    }

    // Check if any of the underlying objects of the memreg are globals and save
    // them
    SmallVector<const Value *, 1> globals;
    for (auto obj : this->memReg->underlyingObjects)
      if (isa<GlobalVariable>(obj))
        globals.push_back(obj);

    // If there is a global underlying object,
    // the target region cannot have any function calls
    // that modify or reference the global
    if (!globals.empty()) {
      // This check is here because the getModRefInfo function will check if the
      // base pointer of the memory location instruction is a global, so it
      // does not work if the base pointers of the memReg don't contain
      // the global variables that are present in the underlying objects
      for (auto global : globals) {
        if (!this->memReg->basePtrs.contains(global)) {
          dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Accesses a "
                    "global underlying object that is not a base pointer\n";
          return false;
        }
      }

      // Get loads and stores of this candidate
      SmallVector<Instruction *> loadStores =
          this->memReg->getLoadStoresInLoop(this->targetLoop);

      if (loadStores.empty()) {
        dbgs() << "[RebaseDLPass] ERROR: Load/Stores empty\n";
        return false;
      }

      for (auto call : calls) {
        // ignore llvm functions
        Function *calledFunction = call->getCalledFunction();
        if (calledFunction->isIntrinsic())
          continue;

        for (auto loadStore : loadStores) {
          auto memLoc = MemoryLocation::get(loadStore);
          if (AA.getModRefInfo(call, memLoc) != ModRefInfo::NoModRef) {
            dbgs() << "[RebaseDLPass][Candidate Dismissed] Legality: Call may "
                      "modify global underlying object\n";
            return false;
          }
        }
      }
    }

    return true;
  }

  bool hasSingleExit(LoopInfo &LI) {
    // Get loads and stores for this candidate
    SmallVector<Instruction *> loadStores =
        this->memReg->getLoadStoresInLoop(this->targetLoop);

    // Get the loops that loads and store have as parents inside the target loop
    // (including the target loop)
    SmallSet<Loop *, 2> parentLoops;
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
      if (loop->getUniqueExitBlock())
        continue;

      // Not ok if it has no exit
      if (loop->hasNoExitBlocks()) {
        dbgs() << "[RebaseDLPass][Candidate Dismissed] Cost/Benefit: Loop has "
                  "no exit\n";
        return false;
      }

      SmallVector<BasicBlock *> nonLatchExits;
      loop->getUniqueNonLatchExitBlocks(nonLatchExits);

      // If it has multiple exits, check if it is only because of asserts
      // these are fine, otherwise give up on multiple exits
      for (auto exit : nonLatchExits) {
        Instruction *terminator = exit->getTerminator();
        if (!isa<UnreachableInst>(terminator)) {
          dbgs() << "[RebaseDLPass][Candidate Dismissed] Cost/Benefit: Loop "
                    "has non-latch exit that does not end on unreachable "
                    "instruction\n";
          return false;
        }
      }
    }

    return true;
  }

  // Compute estimative of execution frequency of execution of the loads/stores
  // of memReg in targetLoop. It is the minimum of the frequency of first
  // dominator of the loads/stores of memReg whose immediate parent loop is the
  // target loop divided by the frequency of the header of the target loop.
  void computeMinAccessFrequency(LoopInfo &LI, BlockFrequencyInfo &BFI,
                                 DominatorTree &DT) {
    // Get loads and stores for this candidate
    SmallVector<Instruction *> loadStores =
        this->memReg->getLoadStoresInLoop(this->targetLoop);

    // Get blocks for load/stores
    SmallSet<BasicBlock *, 4> loadStoreBlocks;
    for (auto loadStore : loadStores)
      loadStoreBlocks.insert(loadStore->getParent());

    // Get frequency for the header of the target loop
    uint64_t targetHeaderFreq =
        BFI.getBlockFreq(this->targetLoop->getHeader()).getFrequency();

    for (auto block : loadStoreBlocks) {
      // Get node in the dominator tree for the basic block of load/store
      auto node = DT.getNode(block);

      // Go up the tree (through immediate dominators) until getting to
      // a basic block whose immediate loop parent is the target loop
      // this should always stop at most at the header of the target loop
      while (node) {
        if (LI.getLoopFor(node->getBlock()) == this->targetLoop)
          break;
        node = node->getIDom();
      }

      if (!node) {
        dbgs() << "[RebaseDLPass] Error: Failed going up dominator tree\n";
        return;
      }

      uint64_t idomFreq = BFI.getBlockFreq(node->getBlock()).getFrequency();
      float relativeFreq = static_cast<float>(idomFreq) / targetHeaderFreq;

      if (!this->minAccessFrequency.has_value())
        this->minAccessFrequency = relativeFreq;
      else
        this->minAccessFrequency =
            std::min(this->minAccessFrequency.value(), relativeFreq);
    }
  }

  // Computes cost benefit of applying the transformation to this candidate. It
  // estimates the number of bytes accessed of the memReg in targetLoop vs the
  // number of cache lines brought to cache with these accesses. It first checks
  // if the cache utilization is low. Then, it computes the benefit as the
  // number of cache lines that will not be brought to cache after the
  // transformation multiplied by the number of reuse iterations (trip count of
  // target loop). The cost is the number of cache lines brought to cache to do
  // the transformation, multiplied by 2 if there are writes to the memReg.
  void computeBenefitCost(const DataLayout &DL, ScalarEvolution &SE,
                          LoopInfo &LI, const int cacheLineSize = 64) {
    // Get loads and stores for this candidate
    SmallVector<Instruction *> loadStores =
        this->memReg->getLoadStoresInLoop(this->targetLoop);

    uint64_t bytesAccessed = 0;
    uint64_t cacheLinesAccessed = 0;
    countBytesAndCacheLinesAccessed(loadStores, this->targetLoop, DL, SE, LI,
                                    bytesAccessed, cacheLinesAccessed);
    uint64_t cacheLinesAccessedInBytes = cacheLinesAccessed * cacheLineSize;
    if (!bytesAccessed || !cacheLinesAccessed) {
      dbgs() << "[RebaseDLPass] Error: Unable to compute bytes/cache "
                "lines accessed\n";
      return;
    }

    // Compute cache utilization ratio and check if this candidate is bellow the
    // threshold
    this->cacheUtilization =
        static_cast<float>(bytesAccessed) / cacheLinesAccessedInBytes;

    // TODO: simulate padding required by new type
    uint64_t cacheLinesAfterTransformInBytes =
        ceilDiv(bytesAccessed, cacheLineSize) * cacheLineSize;

    // Benefit can be compute as the following, but it can be simplified to the
    // uncommented code the following
    // uint64_t unusedCacheLineBytes = cacheLinesAccessedInBytes -
    // bytesAccessed; uint64_t unusedCacheLineBytesAfterTransformation =
    //     cacheLinesNeededInBytes - bytesAccessed;
    // int64_t benefit =
    //     unusedCacheLineBytes - unusedCacheLineBytesAfterTransformation;
    int64_t benefit =
        cacheLinesAccessedInBytes - cacheLinesAfterTransformInBytes;

    uint64_t cost = cacheLinesAccessedInBytes;
    if (this->memReg->isStoredInLoop(this->targetLoop))
      cost *= 2;

    // Multiply the benefit by the number of iterations of the invariant target
    // loop. The default count here is lower to avoid inflating the
    // overallBenefit if the trip count in unknown
    unsigned reuseIterations =
        estimateLoopTripCount(this->targetLoop, SE, /*defaultCount=*/10);
    int64_t overallBenefit = benefit * reuseIterations;

    // Compute cost benefit ratio
    this->benefitCostRatio = static_cast<float>(overallBenefit) / cost;

    // dbgs() << "[RebaseDLPass] - Bytes accessed: " << bytesAccessed << "\n";
    // dbgs() << "[RebaseDLPass] - Cache lines accessed: "
    //        << cacheLinesAccessedInBytes << "\n";
    // dbgs() << "[RebaseDLPass] - Cache lines accessed after transformation: "
    //        << cacheLinesAfterTransformInBytes << "\n ";
    // dbgs() << "[RebaseDLPass] - Benefit: " << benefit << "\n";
    // dbgs() << "[RebaseDLPass] - Cost: " << cost << "\n";
    // dbgs() << "[RebaseDLPass] - Reuse iterations: " << reuseIterations
    //        << "\n";
    // dbgs() << "[RebaseDLPass] - Benefit/Cost: "
    //        << format("%.3f", this->benefitCostRatio.value()) << "\n";
  }

  bool isFrequent(const float minFrequency = 0.35) {
    if (this->minAccessFrequency.has_value())
      return this->minAccessFrequency > minFrequency;

    return false;
  }

  bool hasLowCacheUtilization(const float maxCacheUtilization = 0.5) {
    if (this->cacheUtilization.has_value())
      return this->cacheUtilization < maxCacheUtilization;

    return false;
  }

  bool isBeneficial(const float minBenefitCost = 2.0) {
    if (this->benefitCostRatio.has_value())
      return this->benefitCostRatio >= minBenefitCost;

    return false;
  }

  // Print information about this candidate
  void dump(const DataLayout &DL, LoopInfo &LI) {
    dbgs() << "[RebaseDLPass] RegionPackingCandidate ===========\n";
    dbgs() << "[RebaseDLPass] Target loop: " << this->targetLoop->getName()
           << "\n";
    if (this->targetLoop->getStartLoc()) {
      dbgs() << "[RebaseDLPass] - " << *this->targetLoop->getStartLoc() << "\n";
    }
    dbgs() << "[RebaseDLPass] - depth: " << this->targetLoop->getLoopDepth()
           << "\n";
    if (this->minAccessFrequency.has_value())
      dbgs() << "[RebaseDLPass] Minimum access frequency: "
             << format("%.3f", this->minAccessFrequency.value()) << "\n";
    if (this->cacheUtilization.has_value())
      dbgs() << "[RebaseDLPass] Cache utilization: "
             << format("%.3f", this->cacheUtilization.value()) << "\n";
    if (this->benefitCostRatio.has_value())
      dbgs() << "[RebaseDLPass] Cost benefit: "
             << format("%.8f", this->benefitCostRatio.value()) << "\n";
    this->memReg->dump(DL, this->targetLoop);
    dbgs() << "[RebaseDLPass] ==================================\n";
    dbgs() << "[RebaseDLPass] \n";
  }
};

// Returns a vector containing RegionPackingMemReg objects where each object is
// a group of pointers that have the same base pointers, or that have two base
// pointers that must alias. Pointers to intrinsic (llvm.) functions are
// ignored.
//
// \p pointers is a set with the pointers to separated
SmallVector<RegionPackingMemReg> separateMemRegs(SetVector<Value *> &pointers,
                                                 const DataLayout &DL,
                                                 AliasAnalysis &AA) {
  // Separate into a map based on the base pointer
  MapVector<const Value *, RegionPackingMemReg> memRegMap;
  for (Value *pointer : pointers) {
    const Value *basePointer = getUnderlyingObjectRebaseDL(pointer);

    // Skip pointers to intrinsic functions
    if (auto func = dyn_cast<Function>(basePointer))
      if (func->isIntrinsic())
        continue;

    if (memRegMap.count(basePointer) == 0)
      memRegMap[basePointer] = RegionPackingMemReg{pointer, DL};
    else
      memRegMap[basePointer].addPtr(pointer, DL);
  }

  // Move already pre-separated RegionPackingMemRegs into a vector and if two
  // base pointers must alias, merge their RegionPackingMemReg objects
  SmallVector<RegionPackingMemReg> memRegs;
  for (auto &map : memRegMap) {
    auto &memReg = map.second;

    // Add first memReg
    if (memRegs.empty()) {
      memRegs.push_back(memReg);
      continue;
    }

    // Merge memRegs if they intersect
    for (auto &memRegFromList : memRegs) {
      if (memRegFromList.intersects(memReg, AA)) {
        memRegFromList.merge(memReg);
        continue;
      }
    }

    // Add another memReg
    memRegs.push_back(memReg);
  }

  return memRegs;
}

void runOnOuterLoop(Loop *outerLoop, DenseSet<Loop *> &copyLoops,
                    const DataLayout &DL, LoopInfo &LI, ScalarEvolution &SE,
                    AliasAnalysis &AA, BlockFrequencyInfo &BFI,
                    DominatorTree &DT) {

  // Skip copy loops created by this pass
  if (copyLoops.count(outerLoop) != 0)
    return;

  // Get pointers used in the outer loop
  SetVector<Value *> pointers = getPtrsUsedInLoop(outerLoop);
  if (pointers.empty()) {
    // dbgs() << "[RebaseDLPass][Loop Dismissed] No ptrs used in loop nest\n";
    return;
  }

  // Get loads in the loop
  SmallVector<LoadInst *> loads = getInstructionsInLoop<LoadInst>(outerLoop);
  // Give up if there are no loads, a loop with only
  // stores is not a candidate for the transformation
  if (loads.empty()) {
    // dbgs() << "[RebaseDLPass][Loop Dismissed] No loads in loop nest\n";
    return;
  }

  // Check if there are loads at least at a loop depth of 2
  unsigned maxLoopDepth = 0;
  const int requiredLoopDepth = 2;
  for (LoadInst *load : loads) {
    maxLoopDepth = std::max(maxLoopDepth, LI.getLoopDepth(load->getParent()));
    if (maxLoopDepth >= requiredLoopDepth)
      break;
  }
  if (maxLoopDepth < requiredLoopDepth) {
    // dbgs() << "[RebaseDLPass][Loop Dismissed] Loads in loop nest are too "
    //           "shallow\n";
    return;
  }

  // Separate pointers into memory regions based
  // on the base pointer and alias analysis
  SmallVector<RegionPackingMemReg> memRegs = separateMemRegs(pointers, DL, AA);

  // Get all nested loops including outermost loop
  auto loopNest = outerLoop->getLoopsInPreorder();

  // Create candidates that show data reuse
  SmallVector<RegionPackingCandidate> candidates;
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
    // dbgs() << "[RebaseDLPass][Loop Dismissed] No candidates that show data "
    //           "reuse\n";
    return;
  }

  // Remove candidates that would involve an interprocedural transformation
  candidates.erase(
      std::remove_if(
          candidates.begin(), candidates.end(),
          [](RegionPackingCandidate &attr) {
            if (attr.isInterprocedural()) {
              dbgs() << "[RebaseDLPass][Candidate Dismissed] Interprocedural\n";
              return true;
            } else {
              return false;
            }
          }),
      candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass][Loop Dismissed] Remaining candidates are "
              "interprocedural\n";
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
    dbgs() << "[RebaseDLPass] Remaining candidates are illegal\n";
    return;
  }

  // Remove candidates that are not single-exits regions
  candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
                                  [&LI](RegionPackingCandidate &attr) {
                                    if (!attr.hasSingleExit(LI)) {
                                      dbgs()
                                          << "[RebaseDLPass][Candidate "
                                             "Dismissed] Has multiple exits\n";
                                      return true;
                                    } else {
                                      return false;
                                    }
                                  }),
                   candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass][Loop Dismissed] Remaining candidates have "
              "multiple exits\n";
    return;
  }

  for (RegionPackingCandidate &candidate : candidates)
    candidate.computeMinAccessFrequency(LI, BFI, DT);

  // Remove candidates that are not frequent
  candidates.erase(
      std::remove_if(candidates.begin(), candidates.end(),
                     [](RegionPackingCandidate &attr) {
                       if (!attr.isFrequent()) {
                         dbgs()
                             << "[RebaseDLPass][Candidate Dismissed] Load "
                                "dominator has a frequency that is too low\n";
                         return true;
                       } else {
                         return false;
                       }
                     }),
      candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass][Loop Dismissed] Remaining candidates have load "
              "dominators that are executed infrequently\n";
    return;
  }

  for (RegionPackingCandidate &candidate : candidates)
    candidate.computeBenefitCost(DL, SE, LI);

  // Remove candidates that are not beneficial
  candidates.erase(
      std::remove_if(
          candidates.begin(), candidates.end(),
          [](RegionPackingCandidate &attr) {
            if (!attr.hasLowCacheUtilization()) {
              dbgs() << "[RebaseDLPass][Candidate Dismissed] Cache utilization "
                        "is too high\n";
              return true;
            }
            if (!attr.isBeneficial()) {
              dbgs() << "[RebaseDLPass][Candidate Dismissed] Not beneficial\n";
              return true;
            }
            return false;
          }),
      candidates.end());
  if (candidates.empty()) {
    dbgs() << "[RebaseDLPass][Loop Dismissed] Remaining candidates are not "
              "beneficial\n";
    return;
  }

  // Sort candidates options from best to worst
  llvm::stable_sort(candidates, std::greater<RegionPackingCandidate>());

  // Greedy selection of candidates
  SmallVector<RegionPackingCandidate *> greedyCandidates;

  for (auto &candidate : candidates) {
    // Always add the first candidate
    if (greedyCandidates.empty()) {
      greedyCandidates.push_back(&candidate);
      continue;
    }

    bool conflictingCandidate = false;
    for (auto *greedyCandidate : greedyCandidates) {
      // Skip if the memReg is not the same
      if (candidate.memReg != greedyCandidate->memReg)
        continue;

      // Should only transform the same memReg if the target loops of the
      // candidates are independent, otherwise do not transform this candidate.
      if (candidate.targetLoop->contains(greedyCandidate->targetLoop) ||
          greedyCandidate->targetLoop->contains(candidate.targetLoop)) {
        conflictingCandidate = true;
        break;
      }
    }

    if (conflictingCandidate)
      continue;

    greedyCandidates.push_back(&candidate);
  }

  dbgs() << "[RebaseDLPass] ================= Module name "
         << outerLoop->block_begin()[0]->getModule()->getName() << "\n";
  dbgs() << "[RebaseDLPass] ================= Function name "
         << outerLoop->block_begin()[0]->getParent()->getName() << "\n";
  for (auto candidate : greedyCandidates)
    candidate->dump(DL, LI);

  return;
}

PreservedAnalyses RebaseDLPass::run(Function &F, FunctionAnalysisManager &FAM) {
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

  // Run pass on every outer loop
  for (auto loop : LI.getTopLevelLoops())
    runOnOuterLoop(loop, copyLoops, DL, LI, SE, AA, BFI, DT);

  return PreservedAnalyses::all();
}

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------

// Use the O1, O2, or O3 pipelines
// The extra passes are needed if clang is compiled with O2 or O3
// For O2 and O3, disable loop unrolling
PassPluginLibraryInfo getRebaseDLPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
    // Link-time pipeline
    // PB.registerFullLinkTimeOptimizationLastEPCallback([&](ModulePassManager
    // &MPM, auto) {
    //   MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LoopRotatePass())));
    //   MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LICMPass(LICMOptions()),
    //   /*UseMemorySSA*/ true)));
    //   MPM.addPass(createModuleToFunctionPassAdaptor(RebaseDLPass()));
    //   return true;
    // });

    // Compile-time pipeline
    PB.registerVectorizerStartEPCallback([&](FunctionPassManager &FPM, auto) {
      FPM.addPass(createFunctionToLoopPassAdaptor(LoopRotatePass()));
      FPM.addPass(createFunctionToLoopPassAdaptor(LICMPass(LICMOptions()),
                                                  /*UseMemorySSA*/ true));
      FPM.addPass(RebaseDLPass());
      return true;
    });

    // Call it with opt
    PB.registerPipelineParsingCallback(
        [](StringRef Name, llvm::FunctionPassManager &FPM,
           ArrayRef<llvm::PassBuilder::PipelineElement>) {
          if (Name == "rebasedl") {
            FPM.addPass(createFunctionToLoopPassAdaptor(LoopRotatePass()));
            FPM.addPass(createFunctionToLoopPassAdaptor(LICMPass(LICMOptions()),
                                                        /*UseMemorySSA*/ true));
            FPM.addPass(RebaseDLPass());
            return true;
          }
          return false;
        });
  };

  return {LLVM_PLUGIN_API_VERSION, "RebaseDL", LLVM_VERSION_STRING, callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getRebaseDLPassPluginInfo();
}
