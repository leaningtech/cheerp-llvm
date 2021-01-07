//===-- Cheerp/NameGenerator.h - Cheerp name generator code ----------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2013 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_NAME_GENERATOR_H
#define _CHEERP_NAME_GENERATOR_H

#include "llvm/ADT/SmallString.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Cheerp/Registerize.h"
#include "llvm/Cheerp/PointerAnalyzer.h"
#include <unordered_map>

namespace cheerp {

class GlobalDepsAnalyzer;

// This class is responsible for generate unique names for a llvm::Value
// The class is dependent on registerize to work properly
class NameGenerator
{
public:
	/**
	 * This initialize the namegenerator by collecting
	 * all the global variable names
	 */
	explicit NameGenerator( const llvm::Module&, const GlobalDepsAnalyzer &, const Registerize &, const PointerAnalyzer& PA, bool makeReadableNames = true );

	/**
	 * Return the computed name for the given variable.
	 * This function can be called only if the passed value is not an inlined instruction
	 */
	llvm::StringRef getName(const llvm::Value* v) const
	{
		assert(namemap.count(v) );
		assert(! namemap.at(v).empty() );
		if(!edgeContext.isNull())
			return getNameForEdge(v);
		return namemap.at(v);
	}

	/**
	 * Some values, such as arguments which are REGULAR pointers needs two names
	 */
	llvm::StringRef getSecondaryName(const llvm::Value* v) const
	{
		assert(secondaryNamemap.count(v) );
		assert(!secondaryNamemap.at(v).empty());
		if(!edgeContext.isNull())
			return getSecondaryNameForEdge(v);
		return secondaryNamemap.at(v);
	}

	/**
	 * Return a JS compatible name for the StructType, potentially minimized
	 * A name is guaranteed also for literal structs which have otherwise no name
	 */
	llvm::StringRef getTypeName(llvm::Type* T) const
	{
		assert(typemap.count(T));
		return typemap.at(T);
	}

	/**
	 * Same as getName, but supports the required temporary variables in edges between blocks
	 * It uses the current edge context.
	*/
	llvm::StringRef getNameForEdge(const llvm::Value* v) const;
	llvm::StringRef getSecondaryNameForEdge(const llvm::Value* v) const;

	void setEdgeContext(const llvm::BasicBlock* fromBB, const llvm::BasicBlock* toBB)
	{
		assert(edgeContext.isNull());
		edgeContext.fromBB=fromBB;
		edgeContext.toBB=toBB;
	}

	void clearEdgeContext()
	{
		edgeContext.clear();
	}

	enum NAME_FILTER_MODE { GLOBAL = 0, GLOBAL_SECONDARY, LOCAL, LOCAL_SECONDARY };
	// Filter the original string so that it no longer contains invalid JS characters.
	static llvm::SmallString<4> filterLLVMName( llvm::StringRef, NAME_FILTER_MODE filterMode );

private:
	void generateCompressedNames( const llvm::Module& M, const GlobalDepsAnalyzer & );
	void generateReadableNames( const llvm::Module& M, const GlobalDepsAnalyzer & );
	void generateTypeNames( const GlobalDepsAnalyzer& );
	
	// Determine if an instruction actually needs a name
	bool needsName(const llvm::Instruction &, const PointerAnalyzer& PA) const;
	bool needsSecondaryName(const llvm::Value*, const PointerAnalyzer& PA) const;

	const Registerize& registerize;
	const PointerAnalyzer& PA;
	std::unordered_map<const llvm::Value*, llvm::SmallString<4> > namemap;
	std::unordered_map<const llvm::Value*, llvm::SmallString<4> > secondaryNamemap;
	std::unordered_map<llvm::Type*, llvm::SmallString<4> > typemap;
	struct InstOnEdge
	{
		const llvm::BasicBlock* fromBB;
		const llvm::BasicBlock* toBB;
		uint32_t registerId;
		InstOnEdge(const llvm::BasicBlock* f, const llvm::BasicBlock* t, uint32_t r):fromBB(f),toBB(t),registerId(r)
		{
		}
		bool operator==(const InstOnEdge& r) const
		{
			return fromBB==r.fromBB && toBB==r.toBB && registerId==r.registerId;
		}
		struct Hash
		{
			size_t operator()(const InstOnEdge& i) const
			{
				return std::hash<const llvm::BasicBlock*>()(i.fromBB) ^
					std::hash<const llvm::BasicBlock*>()(i.toBB) ^
					std::hash<uint32_t>()(i.registerId);
			}
		};
	};
	typedef std::unordered_map<InstOnEdge, llvm::SmallString<8>, InstOnEdge::Hash > EdgeNameMapTy;
	EdgeNameMapTy edgeNamemap;
	EdgeNameMapTy edgeSecondaryNamemap;
	struct EdgeContext
	{
		const llvm::BasicBlock* fromBB;
		const llvm::BasicBlock* toBB;
		EdgeContext():fromBB(NULL), toBB(NULL)
		{
		}
		bool isNull() const
		{
			return fromBB==NULL;
		}
		void clear()
		{
			fromBB=NULL;
			toBB=NULL;
		}
	};
	EdgeContext edgeContext;
};

}

#endif //_CHEERP_NAME_GENERATOR_H
