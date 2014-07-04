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

#include "llvm/ADT/StringExtras.h"
#include "llvm/Cheerp/NameGenerator.h"
#include "llvm/Cheerp/GlobalDepsAnalyzer.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/IR/Function.h"
#include <set>

using namespace llvm;

namespace cheerp {

/**
 * Note: this describes the valid *C++* identifiers.
 * 
 * Iterate over all the valid JS identifier is much more complicated , because JS uses unicode.
 * Reference for valid JS identifiers:
*  http://stackoverflow.com/questions/1661197/valid-characters-for-javascript-variable-names
*/
struct JSSymbols
{
	enum : char {first_symbol = 'a' };
	static char next( char c )
	{
		return  c == '_' ? 'a' :
			c == 'z' ? 'A' :
			c == 'Z' ? '0' :
			c == '9' ? '_' :
			++c;
	}

	template< class String >
	static bool is_valid( String & s )
	{
		// Can not be empty
		if ( s.empty() ) return false;
		
		// Can not start with a digit
		if ( std::isdigit(s.front() ) )
		{
			std::fill( s.begin(), s.end(), '_' );
			return false;
		}
		
		// Can not be made only of '_';
		if ( std::all_of( s.begin(), s.end(), [](char c) { return c == '_'; }) )
			return false;
		
		// Check for reserved keywords
		if ( reserved_names.count(s) )
			return false;
		
		// "null" is used by cheerp internally
		if ( s == "null" )
			return false;
		
		// In the rare case that a name is longer than 4 characters, it need to start with an underscore
		// just to be safe.
		if ( s.size() > 4 && s.front() != '_' )
		{
			std::fill( s.begin(), s.end(), '_' );
			return false;
		}
		
		// Check for labels generated by the relooper
		if ( s.front() == 'L' && std::all_of( s.begin()+1, s.end(), ::isdigit ) )
		{
			std::fill( s.begin()+1,s.end(),'9');
			return false;
		}

		return true;
	}

	static const std::set< StringRef > reserved_names;
};

const std::set< StringRef > JSSymbols::reserved_names = {
	"byte",
	"case",
	"char",
	"do",
	"else",
	"enum",
	"for",
	"goto",
	"if",
	"in",
	"int",
	"let",
	"new",
	"this",
	"top",
	"try",
	"var",
	"void",
	"with"
};

NameGenerator::NameGenerator(const GlobalDepsAnalyzer& gda, bool makeReadableNames)
{
	if ( makeReadableNames )
		generateReadableNames(gda);
	else
		generateCompressedNames(gda);
}

uint32_t NameGenerator::getUniqueIndexForPHI(const llvm::Function * f)
{
	return currentUniqueIndexForPHI[f]++;
}

SmallString< 4 > NameGenerator::filterLLVMName(StringRef s, bool isGlobalName)
{
	SmallString< 4 > ans;
	ans.reserve( s.size() + 1 );

	//Add an '_' or 'L' to skip reserved names
	ans.push_back( isGlobalName ? '_' : 'L' );

	for ( char c : s )
	{
		//We need to escape invalid chars
		switch(c)
		{
			case '.':
				ans.append("$p");
				break;
			case '-':
				ans.append("$m");
				break;
			case ':':
				ans.append("$c");
				break;
			case '<':
				ans.append("$l");
				break;
			case '>':
				ans.append("$r");
				break;
			case ' ':
				ans.append("$s");
				break;
			default:
				ans.push_back(c);
		}
	}

	return ans;
}

void NameGenerator::generateCompressedNames(const GlobalDepsAnalyzer& gda)
{
	typedef std::pair<unsigned, const Value *> useValuePair;
	typedef std::pair<unsigned, std::vector<const Value *> > useValuesPair;
	typedef std::vector<useValuesPair> useValuesVec;
        
	/**
	 * Collect the local values.
	 * 
	 * We sort them by uses, then store together those in the same position.
	 * i.e. allLocalValues[0].second will contain all the most used local values
	 * for each function, and allLocalValues[0].first will be the sum of the uses
	 * of all those local values.
	 */
        
        useValuesVec allLocalValues;
        
	for (const Function * f : gda.functionOrderedList() )
	{
		/**
		 * TODO, some cheerp-internals functions are actually generated even with an empty IR.
		 * They should be considered here.
		 */
		if ( f->empty() ) 
			continue;

		std::set< useValuePair > thisFunctionLocals;

		// Insert all the instructions
		for (const BasicBlock & bb : *f)
			for (const Instruction & I : bb)
			{
				if ( needsName(I) )
				{
					thisFunctionLocals.emplace( I.getNumUses(), &I );
				}
			}

		// Insert the arguments
		for ( auto arg_it = f->arg_begin(); arg_it != f->arg_end(); ++arg_it )
			thisFunctionLocals.emplace( arg_it->getNumUses(), arg_it );

		// Resize allLocalValues so that we have empty useValuesPair at the end of the container
		if ( thisFunctionLocals.size() > allLocalValues.size() )
			allLocalValues.resize( thisFunctionLocals.size() );

		auto dst_it = allLocalValues.begin();

		for (auto src_it = thisFunctionLocals.rbegin(); src_it != thisFunctionLocals.rend(); ++src_it, ++dst_it )
		{
			dst_it->first += src_it->first;
			dst_it->second.push_back( src_it->second );
		}
	}
        
	assert( std::is_sorted( 
		allLocalValues.rbegin(), 
		allLocalValues.rend(),
		[] (const useValuesPair & lhs, const useValuesPair & rhs) { return lhs.first < rhs.first; } 
		) );

	/**
	 * Sort the global values by number of uses
	 */
	std::set< useValuePair, std::greater< useValuePair > > allGlobalValues;

	for ( const GlobalValue * GV : gda.globalOrderedList() )
	{
		if ( isa<GlobalVariable>(GV) && TypeSupport::isClientGlobal(GV) )
		{
			demangler_iterator dmg( GV->getName() );
			assert(*dmg == "client");
			
			namemap.emplace( GV, *(++dmg) );
			
			continue;
		}

		unsigned nUses = GV->getNumUses();
		
		if ( GV->getName() == "_Z7webMainv" )
			++nUses; // We explicitly invoke the webmain
		
		// Constructors are also explicitly invoked
		if ( std::find(gda.constructors().begin(), gda.constructors().end(), GV ) != gda.constructors().end() )
			++nUses;
		
		allGlobalValues.emplace( nUses, GV );
	}

	/**
	 * Now generate the names and fill the namemap.
	 * 
	 * Note that there will never be a global with the same name as a local.
	 * This is suboptimal, since in theory we could check out for the uses
	 * of the global inside the function.
	 */
	name_iterator<JSSymbols> name_it;
	
	// Instead of merging allGlobalValues and allLocalValues, we iterate
	// over *both* of them, incrementing selectively only one of the iterator
	
	std::set< useValuePair >::const_iterator global_it = allGlobalValues.begin();
	useValuesVec::const_iterator local_it = allLocalValues.begin();

	for ( ; global_it != allGlobalValues.end() && local_it != allLocalValues.end(); ++name_it )
	{
		if ( global_it->first >= local_it->first )
		{
			// Assign this name to a global value
			namemap.emplace( global_it->second, *name_it );
			
			++global_it;
		}
		else
		{
			// Assign this name to all the local values
			for ( const Value * v : local_it->second )
				namemap.emplace( v, *name_it );
			
			++local_it;
		}
	}

	// Assign remaining vars        
	for ( ; global_it != allGlobalValues.end(); ++global_it, ++name_it )
		namemap.emplace( global_it->second, *name_it );

	for ( ; local_it != allLocalValues.end(); ++local_it, ++name_it )
		for ( const Value * v : local_it->second )
			namemap.emplace( v, *name_it );
}

void NameGenerator::generateReadableNames(const GlobalDepsAnalyzer& gda)
{
	for (const Function * f : gda.functionOrderedList() )
	{
		unsigned tmpCounter = 0;

		for (const BasicBlock & bb : *f)
			for (const Instruction & I : bb)
			{
				if ( needsName(I) )
				{
					if ( I.hasName() )
						namemap.emplace( &I, filterLLVMName(I.getName(), false) );
					else
						namemap.emplace( &I, StringRef( "tmp" + std::to_string(tmpCounter++) ) );
				}
			}

		unsigned argCounter = 0;
		for ( auto arg_it = f->arg_begin(); arg_it != f->arg_end(); ++arg_it )
			if ( arg_it->hasName() )
				namemap.emplace( arg_it, filterLLVMName(arg_it->getName(), false) );
			else
				namemap.emplace( arg_it, StringRef( "arg" + std::to_string(argCounter++) ) );
			
		namemap.emplace( f, filterLLVMName( f->getName(), true ) );
	}

	for (const GlobalVariable * GV : gda.varsOrderedList() )
		if (TypeSupport::isClientGlobal(GV) )
		{
			demangler_iterator dmg( GV->getName() );
			assert(*dmg == "client");
			
			namemap.emplace( GV, *(++dmg) );
			
		}
		else
			namemap.emplace( GV, filterLLVMName( GV->getName(), true ) );
}

bool NameGenerator::needsName(const Instruction & I) const
{
	return !isInlineable(I) && !I.getType()->isVoidTy();
}

}
