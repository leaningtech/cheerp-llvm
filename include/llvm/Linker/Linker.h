//===- Linker.h - Module Linker Interface -----------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LINKER_LINKER_H
#define LLVM_LINKER_LINKER_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/DiagnosticInfo.h"

namespace llvm {
class Module;
class StructType;
class Type;

/// This class provides the core functionality of linking in LLVM. It keeps a
/// pointer to the merged module so far. It doesn't take ownership of the
/// module since it is assumed that the user of this class will want to do
/// something with it after the linking.
class Linker {
public:
  typedef DenseSet<StructType *> NonOpaqueStructTypeSet;
  typedef DenseSet<StructType *> OpaqueStructTypeSet;

  struct IdentifiedStructTypeSet {
    // The set of opaque types is the composite module.
    OpaqueStructTypeSet OpaqueStructTypes;

    // The set of identified but non opaque structures in the composite module.
    NonOpaqueStructTypeSet NonOpaqueStructTypes;

    void addNonOpaque(StructType *Ty);
    void addOpaque(StructType *Ty);
    bool hasType(StructType *Ty);
  };

  Linker(Module *M, DiagnosticHandlerFunction DiagnosticHandler);
  Linker(Module *M);
  ~Linker();

  Module *getModule() const { return Composite; }
  void deleteModule();

  /// \brief Link \p Src into the composite. The source is destroyed.
  /// Returns true on error.
  bool linkInModule(Module *Src);

  static bool LinkModules(Module *Dest, Module *Src,
                          DiagnosticHandlerFunction DiagnosticHandler);

  static bool LinkModules(Module *Dest, Module *Src);

private:
  void init(Module *M, DiagnosticHandlerFunction DiagnosticHandler);
  Module *Composite;

  IdentifiedStructTypeSet IdentifiedStructTypes;

  DiagnosticHandlerFunction DiagnosticHandler;
};

} // End llvm namespace

#endif
