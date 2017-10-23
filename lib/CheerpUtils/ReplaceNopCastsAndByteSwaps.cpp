//===-- ReplaceNopCastsAndByteSwaps.cpp - The Cheerp JavaScript generator -===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2014-2016 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Cheerp/ReplaceNopCastsAndByteSwaps.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/FormattedStream.h"

namespace cheerp {

using namespace llvm;

bool ReplaceNopCastsAndByteSwaps::runOnFunction(Function & F)
{
	// We can use the same IntrinsicLowering over and over again
	if ( !IL )
	{
		DataLayoutPass* DLP = getAnalysisIfAvailable<DataLayoutPass>();
		assert(DLP);
		const DataLayout* DL = &DLP->getDataLayout();
		assert(DL);
		IL = new IntrinsicLowering(*DL);
	}

	if ( F.empty() )
		return false;

	bool Changed = false;

	for ( BasicBlock & BB : F )
		Changed |= processBasicBlock(BB);
	
	assert( ! verifyFunction(F, &llvm::errs()) );

	return Changed;
}

bool ReplaceNopCastsAndByteSwaps::processBasicBlock(BasicBlock& BB)
{
	bool Changed = false;
	
	/**
	 * First pass: replace nopCasts with bitcasts and bswap intrinsics with logic operations
	
	 */
	for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); )
	{
		Instruction * Inst = it++;
		
		if (isNopCast(Inst) )
		{
			assert( isa<CallInst>(Inst) );
			
			CallInst * call = cast<CallInst>(Inst);
			
			if ( TypeSupport::isClientType( call->getType()) )
			{
				llvm::errs() << "Cast of client type: " << *call << "\n";
				continue;
			}
			if ( TypeSupport::isClientType( call->getArgOperand(0)->getType()) )
			{
				llvm::errs() << "Cast of client type: " << *call->getArgOperand(0) << "\n";
				continue;
			}

			ReplaceInstWithInst( call,  BitCastInst::Create( Instruction::CastOps::BitCast, call->getArgOperand(0), call->getType() ) );

			Changed = true;
		}
		else if( IntrinsicInst* II = dyn_cast<IntrinsicInst>(Inst) )
		{
			if(II->getIntrinsicID() == Intrinsic::bswap)
			{
				IL->LowerIntrinsicCall(II);
				Changed = true;
			}
#if 0
			else if(II->getIntrinsicID() == Intrinsic::cheerp_deallocate)
			{
				II->eraseFromParent();
				Changed = true;
			}
#endif
		}
		else if( LoadInst* LI = dyn_cast<LoadInst>(Inst) )
		{
			llvm::Value* ptr = LI->getOperand(0);
			if(cheerp::visitPointerByteLayoutChain(ptr) && LI->getType()->isIntegerTy() && LI->getType()->getIntegerBitWidth() > 8)
			{
				llvm::Instruction* val1 = cheerp::emitByteLayoutLoad(ptr, LI->getType(), LI);
				LI->replaceAllUsesWith(val1);
				LI->eraseFromParent();
			}
		}
		else if( StoreInst* SI = dyn_cast<StoreInst>(Inst) )
		{
			llvm::Value* ptr = SI->getPointerOperand();
			llvm::Value* val = SI->getValueOperand();
			if(cheerp::visitPointerByteLayoutChain(ptr) && val->getType()->isIntegerTy() && val->getType()->getIntegerBitWidth() > 8)
			{
				// Decompose this store into N byte store, the backend would do the same in an inefficient way
				llvm::Type* Int8Ty = IntegerType::get(val->getType()->getContext(), 8);
				llvm::Instruction* ptr8 = new BitCastInst(ptr, Int8Ty->getPointerTo(), "", SI);
				int bitWidth = val->getType()->getIntegerBitWidth();
				assert((bitWidth % 8) == 0);
				for(int i=0;i<bitWidth;i+=8)
				{
					llvm::Value* val1 = val;
					if(i!=0)
					{
						llvm::Value* Indexes[] = { ConstantInt::get(IntegerType::get(val->getType()->getContext(), 32), 1) };
						ptr8 = GetElementPtrInst::Create(ptr8, Indexes, "", SI);
						val1 = BinaryOperator::CreateAShr(val, ConstantInt::get(val->getType(), i), "", SI);
					}
					val1 = new TruncInst(val1, Int8Ty, "", SI);
					new StoreInst(val1, ptr8, SI);
				}
				SI->eraseFromParent();
			}
		}
	}
	
	/**
	 * Second pass: collapse bitcasts of bitcasts.
	 * 
	 * Note: this might leave some dead instruction around, but we don't care since bitcasts are inlined anyway
	 */
	for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); ++it )
	{
		if ( isa<BitCastInst>(it) ) 
		{
			while ( BitCastInst * src = dyn_cast<BitCastInst>(it->getOperand(0) ) )
			{
				it->setOperand(0, src->getOperand(0) );
				Changed = true;
			}
		}
	}

	return Changed;
}

const char *ReplaceNopCastsAndByteSwaps::getPassName() const {
	return "ReplaceNopCastsAndByteSwaps";
}

char ReplaceNopCastsAndByteSwaps::ID = 0;

FunctionPass *createReplaceNopCastsAndByteSwapsPass() { return new ReplaceNopCastsAndByteSwaps(); }

}

using namespace cheerp;

INITIALIZE_PASS_BEGIN(ReplaceNopCastsAndByteSwaps, "ReplaceNopCasts", "Replace type safe cast intrinsics with bitcasts and bswap intrinsics with logical operations",
                      false, false)
INITIALIZE_PASS_END(ReplaceNopCastsAndByteSwaps, "ReplaceNopCastsAndByteSwaps", "Replace type safe cast intrinsics with bitcasts and bswap intrinsics with logical operations",
                    false, false)
