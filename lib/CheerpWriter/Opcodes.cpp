//===-- Opcodes.cpp - The Cheerp JavaScript generator ---------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2014 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Cheerp/Utility.h"
#include "llvm/Cheerp/Writer.h"

using namespace llvm;
using namespace cheerp;

void CheerpWriter::compileIntegerComparison(const llvm::Value* lhs, const llvm::Value* rhs, CmpInst::Predicate p)
{
	if(lhs->getType()->isPointerTy())
	{
		if(p==CmpInst::ICMP_EQ || p==CmpInst::ICMP_NE)
			compileEqualPointersComparison(lhs, rhs, p);
		else
		{
			//Comparison on different bases is anyway undefined, so ignore them
			Type* lastType1=compileObjectForPointer(lhs, DRY_RUN);
			Type* lastType2=compileObjectForPointer(rhs, DRY_RUN);
			bool notFirst=compileOffsetForPointer(lhs,lastType1);
			if(!notFirst)
				stream << '0';
			compilePredicate(p);
			notFirst=compileOffsetForPointer(rhs,lastType2);
			if(!notFirst)
				stream << '0';
		}
	}
	else
	{
		compileOperandForIntegerPredicate(lhs,p);
		compilePredicate(p);
		compileOperandForIntegerPredicate(rhs,p);
	}
}

void CheerpWriter::compilePtrToInt(const llvm::Value* v)
{
	Type* lastType = compileObjectForPointer(v, DRY_RUN);
	stream << '(';
	bool ret=compileOffsetForPointer(v, lastType);
	if(!ret)
		stream << '0';
	stream << ')';
}

void CheerpWriter::compileSubtraction(const llvm::Value* lhs, const llvm::Value* rhs)
{
	//Integer subtraction
	//TODO: optimize negation
	stream << "((";
	compileOperand(lhs);
	stream << '-';
	compileOperand(rhs);
	stream << ')';
	if(types.isI32Type(lhs->getType()))
		stream << ">>0";
	else
		stream << '&' << getMaskForBitWidth(lhs->getType()->getIntegerBitWidth());
	stream << ')';
}
