// Developed as part of the emscripten project. License: MIT&LLVM
/*
This is an optimized C++ implemention of the Relooper algorithm originally
developed as part of Emscripten. This implementation includes optimizations
added since the original academic paper [1] was published about it, and is
written in an LLVM-friendly way with the goal of inclusion in upstream
LLVM.

[1] Alon Zakai. 2011. Emscripten: an LLVM-to-JavaScript compiler. In Proceedings of the ACM international conference companion on Object oriented programming systems languages and applications companion (SPLASH '11). ACM, New York, NY, USA, 301-312. DOI=10.1145/2048147.2048224 http://doi.acm.org/10.1145/2048147.2048224
*/

#include <assert.h>
#include <stdio.h>
#include <stdarg.h>

#ifdef __cplusplus

#include <map>
#include <deque>
#include <set>
#include <vector>

struct Block;
struct Shape;

class RenderInterface
{
public:
	RenderInterface() {};
	virtual ~RenderInterface() {};
	virtual void renderBlock(const void* privateBlock) = 0;
	virtual void renderIfOnLabel(int labelId, bool first) = 0;
	virtual void renderIfBlockBegin(const void* privateBlock, int branchId, bool first) = 0;
	virtual void renderIfBlockBegin(const void* privateBlock, const std::vector<int>& skipBranchIds, bool first) = 0;
	virtual void renderElseBlockBegin() = 0;
	virtual void renderBlockEnd() = 0;
	virtual void renderBlockPrologue(const void* privateBlockTo, const void* privateBlockFrom) = 0;
	virtual bool hasBlockPrologue(const void* privateBlockTo, const void* privateBlockFrom) const = 0;
	virtual void renderWhileBlockBegin() = 0;
	virtual void renderWhileBlockBegin(int labelId) = 0;
	virtual void renderDoBlockBegin() = 0;
	virtual void renderDoBlockBegin(int labelId) = 0;
	virtual void renderDoBlockEnd() = 0;
	virtual void renderBreak() = 0;
	virtual void renderBreak(int labelId) = 0;
	virtual void renderContinue() = 0;
	virtual void renderContinue(int labelId) = 0;
	virtual void renderLabel(int labelId) = 0;
};

// Info about a branching from one block to another
struct Branch {
  enum FlowType {
    Direct = 0, // We will directly reach the right location through other means, no need for continue or break
    Break = 1,
    Continue = 2
  };
  Shape *Ancestor; // If not NULL, this shape is the relevant one for purposes of getting to the target block. We break or continue on it
  Branch::FlowType Type; // If Ancestor is not NULL, this says whether to break or continue
  bool Labeled; // If a break or continue, whether we need to use a label
  int branchId;

  Branch(int bId);
  ~Branch();

  // Prints out the branch
  void Render(Block *Target, bool SetLabel, RenderInterface* renderInterface);
};

struct OrderBlocksById
{
	bool operator()(Block* lhs, Block* rhs) const;
};

typedef std::map<Block*, Branch*, OrderBlocksById> BlockBranchMap;

// Represents a basic block of code - some instructions that end with a
// control flow modifier (a branch, return or throw).
struct Block {
  // Branches become processed after we finish the shape relevant to them. For example,
  // when we recreate a loop, branches to the loop start become continues and are now
  // processed. When we calculate what shape to generate from a set of blocks, we ignore
  // processed branches.
  // Blocks own the Branch objects they use, and destroy them when done.
  BlockBranchMap BranchesOut;
  BlockBranchMap BranchesIn; // TODO: make this just a list of Incoming, without branch info - should be just on BranchesOut
  BlockBranchMap ProcessedBranchesOut;
  BlockBranchMap ProcessedBranchesIn;
  Shape *Parent; // The shape we are directly inside
  int Id; // A unique identifier
  const void* privateBlock; //A private value that will be passed back to the callback
  Block *DefaultTarget; // The block we branch to without checking the condition, if none of the other conditions held.
                        // Since each block *must* branch somewhere, this must be set
  bool IsCheckedMultipleEntry; // If true, we are a multiple entry, so reaching us requires setting the label variable
  bool IsSplittable;

  Block(const void* privateBlock, bool splittable, int Id);
  ~Block();

  /*
   * Return false is a branch to the Target already exists
   */
  bool AddBranchTo(Block *Target, int branchId);

  // Prints out the instructions code and branchings
  void Render(bool InLoop, RenderInterface* renderInterface);
};

inline bool OrderBlocksById::operator()(Block* lhs, Block* rhs) const
{
	return lhs->Id < rhs->Id;
}
// Represents a structured control flow shape, one of
//
//  Simple: No control flow at all, just instructions. If several
//          blocks, then
//
//  Multiple: A shape with more than one entry. If the next block to
//            be entered is among them, we run it and continue to
//            the next shape, otherwise we continue immediately to the
//            next shape.
//
//  Loop: An infinite loop.
//
//  Emulated: Control flow is managed by a switch in a loop. This
//            is necessary in some cases, for example when control
//            flow is not known until runtime (indirect branches,
//            setjmp returns, etc.)
//

struct SimpleShape;
struct LabeledShape;
struct MultipleShape;
struct LoopShape;

struct Shape {
  int Id; // A unique identifier. Used to identify loops, labels are Lx where x is the Id.
  Shape *Next; // The shape that will appear in the code right after this one

  enum ShapeType {
    Simple,
    Multiple,
    Loop
  };
  ShapeType Type;

  Shape(ShapeType TypeInit, int Id) : Id(Id), Next(NULL), Type(TypeInit) {}
  virtual ~Shape() {}

  virtual void Render(bool InLoop, RenderInterface* renderInterface) = 0;

  static SimpleShape *IsSimple(Shape *It) { return It && It->Type == Simple ? (SimpleShape*)It : NULL; }
  static MultipleShape *IsMultiple(Shape *It) { return It && It->Type == Multiple ? (MultipleShape*)It : NULL; }
  static LoopShape *IsLoop(Shape *It) { return It && It->Type == Loop ? (LoopShape*)It : NULL; }
  static LabeledShape *IsLabeled(Shape *It) { return IsMultiple(It) || IsLoop(It) ? (LabeledShape*)It : NULL; }
};

struct SimpleShape : public Shape {
  Block *Inner;

  SimpleShape(int Id) : Shape(Simple, Id), Inner(NULL) {}
  void Render(bool InLoop, RenderInterface* renderInterface) {
    Inner->Render(InLoop, renderInterface);
    if (Next) Next->Render(InLoop, renderInterface);
  }
};

typedef std::map<Block*, Shape*, OrderBlocksById> BlockShapeMap;

// A shape that may be implemented with a labeled loop.
struct LabeledShape : public Shape {
  bool Labeled; // If we have a loop, whether it needs to be labeled

  LabeledShape(ShapeType TypeInit, int Id) : Shape(TypeInit, Id), Labeled(false) {}
};

struct MultipleShape : public LabeledShape {
  BlockShapeMap InnerMap; // entry block -> shape
  int NeedLoop; // If we have branches, we need a loop. This is a counter of loop requirements,
                // if we optimize it to 0, the loop is unneeded

  MultipleShape(int Id) : LabeledShape(Multiple, Id), NeedLoop(0) {}

  void RenderLoopPrefix(RenderInterface* renderInterface);
  void RenderLoopPostfix(RenderInterface* renderInterface);

  void Render(bool InLoop, RenderInterface* renderInterface);
};

struct LoopShape : public LabeledShape {
  Shape *Inner;

  LoopShape(int Id) : LabeledShape(Loop, Id), Inner(NULL) {}
  void Render(bool InLoop, RenderInterface* renderInterface);
};

/*
struct EmulatedShape : public Shape {
  std::deque<Block*> Blocks;
  void Render(bool InLoop);
};
*/

// Implements the relooper algorithm for a function's blocks.
//
// Usage:
//  1. Instantiate this struct.
//  2. Call AddBlock with the blocks you have. Each should already
//     have its branchings in specified (the branchings out will
//     be calculated by the relooper).
//  3. Call Render().
//
// Implementation details: The Relooper instance has
// ownership of the blocks and shapes, and frees them when done.
struct Relooper {
  std::deque<Block*> Blocks;
  std::deque<Shape*> Shapes;
  Shape *Root;
  bool NeedsLabel;
  int IdCounter;

  Relooper(int BlockCount);
  ~Relooper();

  void AddBlock(Block *New);

  // Calculates the shapes
  void Calculate(Block *Entry);

  // Renders the result.
  void Render(RenderInterface* renderInterface);

  bool needsLabel() const { return NeedsLabel; }
};

typedef std::set<Block*> BlockSet;
typedef std::map<Block*, BlockSet, OrderBlocksById> BlockBlockSetMap;

#if DEBUG
struct Debugging {
  static void Dump(BlockSet &Blocks, const char *prefix=NULL);
};
#endif

#endif // __cplusplus
