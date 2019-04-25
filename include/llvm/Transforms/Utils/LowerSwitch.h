#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include <algorithm>

namespace llvm {
  /// Replace all SwitchInst instructions with chained branch instructions.
  class LowerSwitch : public FunctionPass {
  public:
    static char ID; // Pass identification, replacement for typeid
    LowerSwitch() : FunctionPass(ID) {
      initializeLowerSwitchPass(*PassRegistry::getPassRegistry());
    } 

    bool runOnFunction(Function &F) override;

    struct IntRange {
      int64_t Low, High;
    };
    struct CaseRange {
      ConstantInt* Low;
      ConstantInt* High;
      BasicBlock* BB;

      CaseRange(ConstantInt *low, ConstantInt *high, BasicBlock *bb)
          : Low(low), High(high), BB(bb) {}
    };

    typedef std::vector<CaseRange> CaseVector;
    typedef std::vector<CaseRange>::iterator CaseItr;
  protected:
    virtual void processSwitchInst(SwitchInst *SI, SmallPtrSetImpl<BasicBlock*> &DeleteList);
  private:

    BasicBlock *switchConvert(CaseItr Begin, CaseItr End,
                              ConstantInt *LowerBound, ConstantInt *UpperBound,
                              Value *Val, BasicBlock *Predecessor,
                              BasicBlock *OrigBlock, BasicBlock *Default,
                              const std::vector<IntRange> &UnreachableRanges);
    BasicBlock *newLeafBlock(CaseRange &Leaf, Value *Val, BasicBlock *OrigBlock,
                             BasicBlock *Default);
    unsigned Clusterify(CaseVector &Cases, SwitchInst *SI);
  };
}

