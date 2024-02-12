
#ifndef LLVM_TRANSFORMS_REBASEDL_PASS_H
#define LLVM_TRANSFORMS_REBASEDL_PASS_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class RebaseDLPass : public PassInfoMixin<RebaseDLPass> {
public:

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
  static bool isRequired() { return true; }
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_REBASEDL_PASS_H
