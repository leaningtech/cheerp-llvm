//===-- Cheerp/TokenList.h - Control Flow representation for js/wasm ------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2019 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_TOKEN_LIST_H
#define _CHEERP_TOKEN_LIST_H

#include "llvm/ADT/ilist.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"

#define DEBUG_TOKENLIST 1

#ifdef DEBUG_TOKENLIST
	#include "llvm/Support/raw_ostream.h"
#endif

namespace cheerp {

class TokenList;

class Token: public llvm::ilist_node_with_parent<Token, TokenList> {
public:
	friend class TokenList;

	enum TokenKind {
		TK_Invalid = 0,
		TK_BasicBlock = 1<<0,
		TK_Loop = 1<<1,
		TK_Block = 1<<2,
		TK_If = 1<<3,
		TK_IfNot = 1<<4,
		TK_Else = 1<<5,
		TK_Switch = 1<<6,
		TK_Case = 1<<7,
		TK_Branch = 1<<8,
		TK_End = 1<<9,
		TK_Prologue = 1<<10,
		TK_BrIf = 1<<11,
		TK_BrIfNot = 1<<12,
		TK_Condition = 1<<13,
	};
private:
	TokenKind Kind;
	const llvm::BasicBlock* BB;
	Token* Match;
	TokenList* Parent;
	int Id;
public:
	TokenKind getKind() const  { return Kind; }
	TokenList* getParent() const { return Parent; }
	const llvm::BasicBlock* getBB() const {
		assert(BB);
		return BB;
	}
	int getId() const {
		assert(Id != -1);
		return Id;
	}
	Token* getMatch() {
		assert(Kind != TK_BasicBlock);
		assert(Match);
		return Match;
	}
	void setMatch(Token* M) {
		assert(M);
		Match = M;
	}
	const Token* getMatch() const {
		assert(Kind != TK_BasicBlock);
		assert(Match);
		return Match;
	}
	llvm::iplist<Token>::iterator getIter() {
		return llvm::iplist<Token>::iterator(*this);
	}
	llvm::iplist<Token>::reverse_iterator getRevIter() {
		return llvm::iplist<Token>::reverse_iterator(getIterator());
	}
	llvm::iplist<Token>::const_iterator getIter() const {
		return llvm::iplist<Token>::const_iterator(*this);
	}
	llvm::iplist<Token>::const_reverse_iterator getRevIter() const {
		return llvm::iplist<Token>::const_reverse_iterator(getIterator());
	}
	static Token* createBasicBlock(const llvm::BasicBlock* BB, int Id) {
		return new Token(TK_BasicBlock, BB, nullptr);
	}
	static Token* createLoop() {
		return new Token(TK_Loop, nullptr, nullptr);
	}
	static Token* createLoopEnd(Token* Begin) {
		assert(Begin && Begin->Kind == TK_Loop);
		Token* End = new Token(TK_End, nullptr, Begin);
		Begin->Match = End;
		return End;
	}
	static Token* createBlock() {
		return new Token(TK_Block, nullptr, nullptr);
	}
	static Token* createBlockEnd(Token* Begin) {
		assert(Begin && Begin->Kind == TK_Block);
		Token* End = new Token(TK_End, nullptr, Begin);
		Begin->Match = End;
		return End;
	}
	static Token* createIf(const llvm::BasicBlock* CondBlock) {
		return new Token(TK_If, CondBlock, nullptr);
	}
	static Token* createIfNot(const llvm::BasicBlock* CondBlock) {
		return new Token(TK_IfNot, CondBlock, nullptr);
	}
	static Token* createElse(Token* If) {
		assert(!If || If->Kind == TK_If);
		Token* Else = new Token(TK_Else, nullptr, nullptr);
		if (If)
			If->Match = Else;
		return Else;
	}
	static Token* createSwitch(const llvm::BasicBlock* CondBlock) {
		return new Token(TK_Switch, CondBlock, nullptr);
	}
	static Token* createSwitchEnd(Token* Switch, Token* LastCase) {
		assert(Switch && Switch->Kind == TK_Switch);
		assert(LastCase && LastCase->Kind == TK_Case);
		Token* End = new Token(TK_End, nullptr, Switch);
		LastCase->Match = End;
		return End;
	}
	static Token* createCase(const llvm::BasicBlock* CondBlock, int Id, Token* Prev) {
		assert(Prev);
		assert(Prev->getKind() == TK_Switch || Prev->getKind() == TK_Case);
		Token* Ret =  new Token(TK_Case, CondBlock, nullptr);
		Prev->Match = Ret;
		Ret->Id = Id;
		return Ret;
	}
	static Token* createIfEnd(Token* If, Token* Else) {
		assert(!If || If->Kind == TK_If);
		assert(!Else || Else->Kind == TK_Else);
		assert(If || Else);
		Token* End = new Token(TK_End, nullptr, If);
		if (Else)
			Else->Match = End;
		else
			If->Match = End;
		return End;
	}
	static Token* createBranch(Token* Dest) {
		return new Token(TK_Branch, nullptr, Dest);
	}
	static Token* createPrologue(const llvm::BasicBlock* From, int ToId) {
		assert(From);
		Token* Ret =  new Token(TK_Prologue, From, nullptr);
		Ret->Id = ToId;
		return Ret;
	}
	static Token* createBrIf(const llvm::BasicBlock* CondBlock, Token* Dest) {
		return new Token(TK_BrIf, CondBlock, Dest);
	}
	static Token* createBrIfNot(const llvm::BasicBlock* CondBlock, Token* Dest) {
		return new Token(TK_BrIfNot, CondBlock, Dest);
	}
	static Token* createCondition(const llvm::BasicBlock* CondBlock) {
		return new Token(TK_Condition, CondBlock, nullptr);
	}
#ifdef DEBUG_TOKENLIST
	void dump() const
	{
		llvm::errs()<< this << " ";
		switch(Kind)
		{
			case TK_BasicBlock:
				llvm::errs()<<"BB "<<BB->getName()<<"\n";
				break;
			case TK_Loop:
				llvm::errs()<<"LOOP " << Match << "\n";
				break;
			case TK_Block:
				llvm::errs()<<"BLOCK " << Match << "\n";
				break;
			case TK_If:
				llvm::errs()<<"IF\n";
				break;
			case TK_IfNot:
				llvm::errs()<<"IF_NOT\n";
				break;
			case TK_Else:
				llvm::errs()<<"ELSE\n";
				break;
			case TK_Switch:
				llvm::errs()<<"SWITCH\n";
				break;
			case TK_Case:
				llvm::errs()<<"CASE\n";
				break;
			case TK_Branch:
				llvm::errs()<<"BRANCH " << Match << "\n";
				break;
			case TK_End:
				llvm::errs()<<"END " << Match << "\n";
				break;
			case TK_Prologue:
				llvm::errs()<<"PROLOGUE From "<<BB->getName()<<" To "<<BB->getTerminator()->getSuccessor(Id)->getName()<<"\n";
				break;
			case TK_Condition:
				llvm::errs()<<"CONDITION\n";
				break;
			case TK_BrIf:
				llvm::errs()<<"BR_IF " << Match << "\n";
				break;
			case TK_BrIfNot:
				llvm::errs()<<"BR_IF_NOT " << Match << "\n";
				break;
			case TK_Invalid:
				llvm::errs()<<"INVALID TOKEN\n";
				break;
		}
	}
#endif
	Token(): Kind(TK_Invalid), BB(nullptr), Match(nullptr), Parent(nullptr), Id(-1) {}
private:
	Token(TokenKind K, const llvm::BasicBlock* BB, Token* Match, int Id = -1)
		: Kind(K), BB(BB), Match(Match), Parent(nullptr), Id(Id) {}
};

class TokenList {
	typedef llvm::iplist<Token> TokenListType;
	llvm::iplist<Token> List;
public:
	/// Token iterators...
	typedef TokenListType::iterator iterator;
	typedef TokenListType::const_iterator const_iterator;
	typedef TokenListType::reverse_iterator reverse_iterator;
	typedef TokenListType::const_reverse_iterator const_reverse_iterator;

	/// Token iterator methods
	inline iterator                begin()       { return List.begin(); }
	inline const_iterator          begin() const { return List.begin(); }
	inline iterator                end  ()       { return List.end();   }
	inline const_iterator          end  () const { return List.end();   }

	inline reverse_iterator        rbegin()       { return List.rbegin(); }
	inline const_reverse_iterator  rbegin() const { return List.rbegin(); }
	inline reverse_iterator        rend  ()       { return List.rend();   }
	inline const_reverse_iterator  rend  () const { return List.rend();   }

	inline size_t                   size() const { return List.size();  }
	inline bool                    empty() const { return List.empty(); }
	inline const Token      &front() const { return List.front(); }
	inline       Token      &front()       { return List.front(); }
	inline const Token       &back() const { return List.back();  }
	inline       Token       &back()       { return List.back();  }

	/// Modify list
	void append(Token* T) {
		T->Parent = this;
		List.push_back(T);
	}
	iterator insert(iterator where, Token* T) {
		T->Parent = this;
		return List.insert(where, T);
	}
	iterator insertAfter(iterator where, Token* T) {
		T->Parent = this;
		return List.insertAfter(where, T);
	}
	void moveAfter(iterator where, iterator First, iterator Last) {
		return List.splice(std::next(where), List, First, Last);
	}
	iterator erase(Token* T) {
		assert(T);
		T->Parent = nullptr;
		return List.erase(T);
	}
	static TokenListType TokenList::*getSublistAccess(Token *) {
		return &TokenList::List;
	}
#ifdef DEBUG_TOKENLIST
	void dump(const Token* Pos = nullptr) const
	{
		int indentLevel = Pos != nullptr;
		for (auto& T: List)
		{
			if (T.Kind == Token::TK_End || T.Kind == Token::TK_Else)
				indentLevel--;
			for (int i = 0; i < indentLevel; ++i)
				llvm::errs() << (i==0 && Pos == &T ? "->" : "  ");
			T.dump();
			if (T.Kind == Token::TK_If
				|| T.Kind == Token::TK_IfNot
				|| T.Kind == Token::TK_Else
				|| T.Kind == Token::TK_Loop
				|| T.Kind == Token::TK_Block
				|| T.Kind == Token::TK_Switch
			) indentLevel++;
		}
	}
#endif
};
}

#endif
