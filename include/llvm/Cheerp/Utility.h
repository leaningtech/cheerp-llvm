//===-- Cheerp/Utility.h - Cheerp common routines -------------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2013 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_UTILITY_H
#define _CHEERP_UTILITY_H

#include <set>
#include <unordered_set>
#include "llvm/ADT/SmallString.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"

namespace cheerp
{

bool isNopCast(const llvm::Value* val);
bool isValidVoidPtrSource(const llvm::Value* val, std::set<const llvm::PHINode*>& visitedPhis);

inline bool isValidVoidPtrSource(const llvm::Value* val)
{
	std::set<const llvm::PHINode*> visitedPhis;
	return isValidVoidPtrSource(val, visitedPhis);
}

bool isInlineable(const llvm::Instruction& I);

inline bool isBitCast(const llvm::Value* v)
{
	if( llvm::isa< llvm::BitCastInst>(v) )
		return true;
	if(const llvm::ConstantExpr * ce = llvm::dyn_cast<llvm::ConstantExpr>(v) )
		return ce->getOpcode() == llvm::Instruction::BitCast;
	return false;
}

inline bool isGEP(const llvm::Value* v)
{
	if( llvm::isa<llvm::GetElementPtrInst>(v) )
		return true;
	if(const llvm::ConstantExpr * ce = llvm::dyn_cast<llvm::ConstantExpr>(v) )
		return ce->getOpcode() == llvm::Instruction::GetElementPtr;
	return false;
}

uint32_t getIntFromValue(const llvm::Value* v);

// Printable name of the llvm type - useful only for debugging
std::string valueObjectName(const llvm::Value * v);

class TypeSupport
{
public:
	TypeSupport( const llvm::Module & module,
		     const std::unordered_set<llvm::StructType*> & basesInfo ) : 
		module(module),
		classesWithBaseInfo(basesInfo) {}

	static bool isValidTypeCast(const llvm::Value * castOp, llvm::Type * dstPtr);

	static bool isDerivedStructType(llvm::StructType* derivedType, llvm::StructType* baseType);

	static bool isClientGlobal(const llvm::Value * v)
	{
		return v->getName().startswith("_ZN6client");
	}

	static bool isClientType(llvm::Type* t)
	{
		if ( llvm::StructType * st = llvm::dyn_cast<llvm::StructType>(t) )
			return st->hasName() && st->getName().startswith("class._ZN6client");
		else 
			return false;
	}

	static bool isClientArrayType(llvm::Type* t)
	{
		if ( llvm::StructType * st = llvm::dyn_cast<llvm::StructType>(t) )
			return st->hasName() && st->getName().startswith("class._ZN6client5ArrayE");
		else 
			return false;
	}

	static bool isI32Type(llvm::Type* t)
	{
		return t->isIntegerTy(32);
	}

	static bool isTypedArrayType(llvm::Type* t)
	{
		return t->isIntegerTy(8) || t->isIntegerTy(16) || t->isIntegerTy(32) ||
			t->isFloatTy() || t->isDoubleTy();
	}

	static bool isImmutableType(llvm::Type* t)
	{
		if(t->isIntegerTy() || t->isFloatTy() || t->isDoubleTy() || t->isPointerTy())
			return true;
		return false;
	}

	static bool hasByteLayout(llvm::Type* t)
	{
		if ( llvm::StructType * st = llvm::dyn_cast<llvm::StructType>(t) )
			return st->hasByteLayout();
		else
			return false;
	}

	static bool hasBasesInfoMetadata(llvm::StructType* t, const llvm::Module & m)
	{
		return getBasesMetadata(t, m) != nullptr;
	}

	bool hasBasesInfo(llvm::StructType* t) const
	{
		assert( !( classesWithBaseInfo.count(t) && !hasBasesInfoMetadata(t, module) ) );
		return classesWithBaseInfo.count(t);
	}

	// Syntactic sugar for when we do not know if we have a struct type
	bool hasBasesInfo(llvm::Type * t) const
	{
		if ( llvm::StructType * st = llvm::dyn_cast<llvm::StructType>(t) )
			return hasBasesInfo(st);
		return false;
	}

	// Bridge to the static version
	bool getBasesInfo(const llvm::StructType* t, uint32_t& firstBase, uint32_t& baseCount) const
	{
		return getBasesInfo(module, t, firstBase, baseCount);
	}
	static bool getBasesInfo(const llvm::Module& module, const llvm::StructType* t, uint32_t& firstBase, uint32_t& baseCount);

private:
	static const llvm::NamedMDNode* getBasesMetadata(const llvm::StructType * t, const llvm::Module & m)
	{
		if(!t->hasName())
			return nullptr;

		return m.getNamedMetadata(llvm::Twine(t->getName(),"_bases"));
	}

	static bool safeCallForNewedMemory(const llvm::CallInst* ci);

	const llvm::Module & module;
	const std::unordered_set<llvm::StructType*> & classesWithBaseInfo;
};

/*
 * Provide information about a malloc/calloc/etc call
 */
class DynamicAllocInfo
{
public:
	enum AllocType
	{
		not_an_alloc,
		malloc,
		calloc,
		cheerp_allocate,
		cheerp_reallocate,
		opnew, // operator new(unsigned int)
		opnew_array // operator new[](unsigned int)
	};
	
	/**
	 * This constructor works with any instruction.
	 * 
	 * If the passed argument is not a call, or is not an alloc,
	 * isValidAlloc will return false. In this case any other
	 * use of this object is not permitted.
	 */
	DynamicAllocInfo(llvm::ImmutableCallSite);
	
	bool isValidAlloc() const { return type != not_an_alloc; }
	
	AllocType getAllocType() const { return type; }
	
	static AllocType getAllocType(llvm::ImmutableCallSite);

	/**
	 * Get the call/invoke instruction
	 */
	const llvm::Instruction * getInstruction() const
	{
		return call.getInstruction();
	}

	/**
	 * Every alloc instruction produces an i8*.
	 * This function tries to understand how the result of an alloc
	 * is used, and deduce the actual used type of the allocation.
	 * 
	 * Will report an llvm error if the use of the result is not consistent
	 */
	llvm::PointerType * getCastedType() const { return castedType; }
	
	/**
	 * This argument will never be null
	 */
	const llvm::Value * getByteSizeArg() const;
	
	/**
	 * This can be null if getAllocType() == calloc
	 */
	const llvm::Value * getNumberOfElementsArg() const;

	/**
	 * This can be null if getAllocType() != cheerp_reallocate
	 */
	const llvm::Value * getMemoryArg() const;

	/**
	 * Check if the size of the allocation is known only at runtime
	 */
	bool sizeIsRuntime() const;
	
	/**
	 * Check if the allocation should use a createArray function
	 */
	bool useCreateArrayFunc() const;
	
	/**
	 * Check if the allocation should use a createTypedArray function
	 */
	bool useCreatePointerArrayFunc() const;
	
	/**
	 * Check if the allocation should use typed arrays
	 */
	bool useTypedArray() const;

private:
	llvm::PointerType * computeCastedType() const;
	
	llvm::ImmutableCallSite call;
	AllocType type;
	llvm::PointerType * castedType;
};

/**
 * Iterator over all the words composed by a given set of symbols.
 * 
 * SymbolTraits model:
 * 
 * struct SymbolTraits {
 * 	static constexpr char first_symbol = ... ; // The first symbol in the symbol order (i.e. 'a' for alphabet, etc.)
 * 	static char next( char c ); // The symbol after c, or first symbol if c is the last symbol
 * 	// Determine if the passed string is valid. 
 * 	// The implementation is free to modify the passed string in order to skip a long sequence of invalid symbols
 * 	template< class String >
 * 	static bool is_valid( String & ); 
 * };
 */
template<class SymbolTraits, unsigned StringSize = 4>
class name_iterator : 
	public std::iterator< std::input_iterator_tag, llvm::SmallString<StringSize> >,
	SymbolTraits // Empty base opt
{
public:
	name_iterator(SymbolTraits st = SymbolTraits () ) : 
		SymbolTraits( std::move(st) )
	{
		value_.assign(1, SymbolTraits::first_symbol );
	}
	
	explicit name_iterator(llvm::StringRef s, SymbolTraits st = SymbolTraits () ) : 
		SymbolTraits( std::move(st) ),
		value_(s) 
	{}
	
	const llvm::SmallString<4>& operator*() const { return value_; }
	const llvm::SmallString<4>* operator->() const { return &value_; }
	
	name_iterator& operator++() { advance(); return *this; }
	name_iterator operator++(int) { name_iterator cpy(*this); advance(); return cpy; }
	
	bool operator==(const name_iterator & other) const { return value_ == other.value_; }
	bool operator!=(const name_iterator & other) const { return ! operator==(other); }
	
private:
	void advance()
	{
		do
		{
			for ( std::size_t i = value_.size(); (i--) > 0; )
			{
				value_[i] = SymbolTraits::next(value_[i]);
				
				if ( i == 0 )
				{
					if ( value_[0] == SymbolTraits::first_symbol )
						value_.insert( value_.begin(), SymbolTraits::first_symbol );
				}
				else if ( value_[i] != SymbolTraits::first_symbol  )
					break;
			}
		}
		while( !SymbolTraits::is_valid( value_ ) );
	}
	
	llvm::SmallString<4> value_;
};

/**
 * Demangles a C++ name by iterating over its (demangled) nested names.
 * We do not need to handle arguments' types (yet!).
 * 
 * Hopefully we can use this everywhere we need demangling, in order
 * to be safe.
 * 
 * Whenever we find a demangling error, we set an error state "error".
 * Whenever this happens, we set ourself to the "end" iterator. So error() can
 * never return true for a non-end iterator.
 * 
 * NOTE we obviously do not honor all the rules of a mangled C++ identifier.
 * We ignore templates, union and probably much more.
 */
struct demangler_iterator : std::iterator< 
	std::forward_iterator_tag,
	llvm::StringRef,
	std::ptrdiff_t,
	const char *,
	llvm::StringRef>
{
	demangler_iterator() {}

	explicit demangler_iterator( llvm::StringRef i ) : tokenSize(0),isNested(false)
	{
		if ( i.startswith("_ZN") )
		{
			isNested = true;
			input = i.drop_front(3);
		}
		else if ( i.startswith("_Z") )
		{
			input = i.drop_front(2);
		}
		else
		{
			// Just return the name
			input = i;
			tokenSize = input.size();
			return;
		}

		advance();
	}
	
	llvm::StringRef operator*() const {
		assert( tokenSize <= input.size());
		return llvm::StringRef( input.begin(), tokenSize );
	}
	
	// TODO find a way to safely implement this
// 	const char * operator->() const;
	
	bool operator==(const demangler_iterator & other) const
	{
		return input == other.input;
	}
	
	bool operator!=(const demangler_iterator & other) const
	{
		return !operator==(other);
	}
	
	demangler_iterator& operator++() {
		advance();
		return *this;
	}
	
	demangler_iterator operator++(int) {
		demangler_iterator cpy(*this);
		advance();
		return cpy;
	}
	
	bool error() const { return hasFailed; }
	
private:
	
	void advance()
	{
		// Advance by tokenSize;
		input = input.drop_front(tokenSize);
		
		if ( input.empty() )
		{
			// End of input
			if ( isNested ) hasFailed = true;
			input = llvm::StringRef();
			return;
		}
		
		// We can not use strtol since StringRef is not guaranteed to be null-terminated!
		const char * FirstValid = std::find_if_not( 
			input.begin(),
			input.end(),
			::isdigit );

		bool parseFail = input.drop_back( input.end() -  FirstValid ).getAsInteger(10, tokenSize);

		if ( parseFail )
		{
			// Check if we have a constructor/destructor
			if ( input.size() >= 2 &&
				(input.startswith("C") || input.startswith("D") ) &&
				std::isdigit( input[1] ) )
			{
				tokenSize = 2;
			}
			else
			{
				// Bail out.
				if ( isNested && input.front() != 'E' )
					hasFailed = true;
				input = llvm::StringRef();
			}
		}
		else
		{
			// We successfully parsed tokenSize.
			// Drop all the initial characters which represent the token length
			input = input.drop_front( FirstValid - input.begin() );
			if ( input.size() < tokenSize )
			{
				//Oh oh.. the mangled name lied to us!
				hasFailed = true;
				input = llvm::StringRef();
			}
		}
	}
	
	llvm::StringRef input;
	std::size_t tokenSize;
	bool isNested;
	bool hasFailed = false;
};

// Forward define the Registerize class
class Registerize;

class EndOfBlockPHIHandler
{
public:
	void runOnEdge(const Registerize& registerize, const llvm::BasicBlock* fromBB, const llvm::BasicBlock* toBB);
protected:
	virtual ~EndOfBlockPHIHandler()
	{
	}
private:
	struct PHIRegData
	{
		const llvm::PHINode* phiInst;
		uint32_t incomingReg;
		enum STATUS { NOT_VISITED=0, VISITING, VISITED };
		STATUS status;
		PHIRegData(const llvm::PHINode* p, uint32_t r):
			phiInst(p), incomingReg(r), status(NOT_VISITED)
		{
		}
	};
	typedef std::map<uint32_t, PHIRegData> PHIRegs;
	void runOnPHI(PHIRegs& phiRegs, uint32_t phiId, llvm::SmallVector<const llvm::PHINode*, 4>& orderedPHIs);
	// Callbacks implemented by derived classes
	virtual void handleRecursivePHIDependency(const llvm::Instruction* phi) = 0;
	virtual void handlePHI(const llvm::Instruction* phi, const llvm::Value* incoming) = 0;
};

}

#endif //_CHEERP_UTILITY_H
