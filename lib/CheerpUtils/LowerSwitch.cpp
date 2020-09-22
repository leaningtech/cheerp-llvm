//===-- LowerSwitch.cpp - Cheerp optimization pass ------------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2019 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LowerSwitch.h"
#include  "llvm/Cheerp/CFGPasses.h"

using namespace llvm;

namespace {

class CheerpLowerSwitch: public LowerSwitch {
public:
	CheerpLowerSwitch(bool onlyLowerI64 = true): onlyLowerI64(onlyLowerI64)
	{
	}
	StringRef getPassName() const override {
		return "CheerpLowerSwitch";
	}
	static char ID;
private:
	bool onlyLowerI64;

	void processSwitchInst(SwitchInst *SI, SmallPtrSetImpl<BasicBlock*> &DeleteList) override;
	bool keepSwitch(const SwitchInst* si);
};

}

static int64_t getCaseValue(const ConstantInt* c, uint32_t bitWidth)
{
	return bitWidth >= 32 ? c->getSExtValue() : c->getZExtValue();
};

bool CheerpLowerSwitch::keepSwitch(const SwitchInst* si)
{
	// At least 3 successors
	if (si->getNumSuccessors() < 3)
		return false;
	uint32_t bitWidth = si->getCondition()->getType()->getIntegerBitWidth();
	// No 64 bit
	if (bitWidth == 64)
		return false;
	if (onlyLowerI64)
		return true;
	//In asm.js cases values must be in the range [-2^31,2^31),
	//and the difference between the biggest and the smaller must be < 2^31
	int64_t max = std::numeric_limits<int64_t>::min();
	int64_t min = std::numeric_limits<int64_t>::max();
	for (auto& c: si->cases())
	{
		int64_t curr = getCaseValue(c.getCaseValue(), bitWidth);
		max = std::max(max,curr);
		min = std::min(min,curr);
	}
	if (min >= std::numeric_limits<int32_t>::min() &&
		max <= std::numeric_limits<int32_t>::max() && 
		//NOTE: this number is the maximum allowed by V8 for wasm's br_table,
		// it is not defined in the spec
		max-min <= 32 * 1024 &&
		// Avoid extremely big and extremely sparse tables, require at least 3% fill rate
		(max-min <= 100 || si->getNumCases() * 100 >= 3 * (max-min)))
	{
		return true;
	}
	return false;
}

void CheerpLowerSwitch::processSwitchInst(SwitchInst *SI, SmallPtrSetImpl<BasicBlock*> &DeleteList)
{
	if(keepSwitch(SI))
		return;
	LowerSwitch::processSwitchInst(SI, DeleteList);
}

char CheerpLowerSwitch::ID = 0;

namespace llvm {

FunctionPass* createCheerpLowerSwitchPass(bool onlyLowerI64)
{
	return new CheerpLowerSwitch(onlyLowerI64);
}

}

INITIALIZE_PASS_BEGIN(CheerpLowerSwitch, "CheerpLowerSwitch", "Lower switches too sparse or big into if/else branch chains",
                      false, false)
INITIALIZE_PASS_END(CheerpLowerSwitch, "CheerpLowerSwitch", "Lower switches too sparse or big into if/else branch chains",
                    false, false)
