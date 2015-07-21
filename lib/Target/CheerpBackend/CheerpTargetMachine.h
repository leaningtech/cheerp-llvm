//===-- CheerpTargetMachine.h - TargetMachine for the CheerpBackend -------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2013 Leaning Technlogies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_TARGETMACHINE_H
#define _CHEERP_TARGETMACHINE_H

#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetSubtargetInfo.h"
#include "llvm/IR/DataLayout.h"

namespace llvm {

class formatted_raw_ostream;

class CheerpSubtarget : public TargetSubtargetInfo {
private:
  const DataLayout DL;

public:
  CheerpSubtarget(const char* dlInit) : DL(dlInit) { }
  virtual const DataLayout* getDataLayout() const
  {
    return &DL;
  }
};

struct CheerpTargetMachine : public TargetMachine {
  CheerpTargetMachine(const Target &T, StringRef TT,
                   StringRef CPU, StringRef FS, const TargetOptions &Options,
                   Reloc::Model RM, CodeModel::Model CM,
                   CodeGenOpt::Level OL)
      : TargetMachine(T, TT, CPU, FS, Options),
           //NOTE: This is duplicate from clang target
           Subtarget("b-e-p:32:8:8-i1:8:8-i8:8:8-i16:8:8-i32:8:8-"
                        "i64:8:8-f32:8:8-f64:8:8-"
                        "a0:0:8-f80:8:8-n8:8:8-S8") { }
private:
  CheerpSubtarget Subtarget;

public:
  const CheerpSubtarget *getSubtargetImpl() const override { return &Subtarget; }
  virtual bool addPassesToEmitFile(PassManagerBase &PM,
                                   formatted_raw_ostream &Out,
                                   CodeGenFileType FileType,
                                   bool DisableVerify,
                                   AnalysisID StartAfter,
                                   AnalysisID StopAfter) override;
};

extern Target TheCheerpBackendTarget;

} // End llvm namespace

#endif
