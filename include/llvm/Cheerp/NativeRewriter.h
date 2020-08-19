//===-- Cheerp/NativeRewriter.h - Cheerp utility code ---------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2014 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef CHEERP_NATIVE_REWRITER_H
#define CHEERP_NATIVE_REWRITER_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include <string>

namespace llvm
{

class CheerpNativeRewriter: public FunctionPass
{
private:
	static bool isBuiltinConstructor(const char* s, const char*& startOfType, const char*& endOfType);
	static bool isBuiltinConstructorForType(const char* s, const std::string& typeName);
	static bool isBuiltinType(const char* typeName, std::string& builtinName);
	static void baseSubstitutionForBuiltin(llvm::User* i, llvm::Instruction* old, llvm::AllocaInst* source);
	static bool findMangledClassName(const char* const s, const char* &className, int& classLen);
	static llvm::Function* getReturningConstructor(llvm::Module& M, llvm::Function* called);
	static void rewriteConstructorImplementation(llvm::Module& M, llvm::Function& F);
	static bool rewriteNativeObjectsConstructors(llvm::Module& M, llvm::Function& F);
	/*
	 * Return true if callInst has been rewritten and it must be deleted
	 */
	static bool rewriteIfNativeConstructorCall(llvm::Module& M, llvm::Instruction* i, llvm::AllocaInst* newI,
					    llvm::Instruction* callInst, llvm::Function* called,
					    const std::string& builtinTypeName,
					    llvm::SmallVector<llvm::Value*, 4>& initialArgs);
	static void rewriteNativeAllocationUsers(llvm::Module& M,llvm::SmallVector<llvm::Instruction*,4>& toRemove,
							llvm::Instruction* allocation, llvm::Type* t,
							const std::string& builtinTypeName);
public:
	static char ID;
	explicit CheerpNativeRewriter() : FunctionPass(ID) { }
	bool runOnFunction(Function &F);
	StringRef getPassName() const;
};

//===----------------------------------------------------------------------===//
//
// CheerpNativeRewriter - This pass converts constructors of classes implemented
// on the browser to returning constructors
//
FunctionPass *createCheerpNativeRewriterPass();

}

#endif
