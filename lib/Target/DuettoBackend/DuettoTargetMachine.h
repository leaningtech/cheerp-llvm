//===-- DuettoTargetMachine.h - TargetMachine for the DuettoBackend -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2013 Leaning Technlogies
//===----------------------------------------------------------------------===//

#ifndef _DUETTO_TARGETMACHINE_H
#define _DUETTO_TARGETMACHINE_H

#include "llvm/Target/TargetMachine.h"
#include "llvm/IR/DataLayout.h"

namespace llvm {

class formatted_raw_ostream;

struct DuettoTargetMachine : public TargetMachine {
  DuettoTargetMachine(const Target &T, StringRef TT,
                   StringRef CPU, StringRef FS, const TargetOptions &Options,
                   Reloc::Model RM, CodeModel::Model CM,
                   CodeGenOpt::Level OL)
      : TargetMachine(T, TT, CPU, FS, Options),
           //NOTE: This is duplicate from clang target
           DL("b-e-p:32:8:8-i1:8:8-i8:8:8-i16:8:8-i32:8:8-"
                        "i64:8:8-f32:8:8-f64:8:8-"
                        "a0:0:8-f80:8:8-n8:8:8-S8") { }
private:
  const DataLayout DL;
public:
  virtual bool addPassesToEmitFile(PassManagerBase &PM,
                                   formatted_raw_ostream &Out,
                                   CodeGenFileType FileType,
                                   bool DisableVerify,
                                   AnalysisID StartAfter,
                                   AnalysisID StopAfter);
  virtual const DataLayout* getDataLayout() const
  {
    return &DL;
  }
};

extern Target TheDuettoBackendTarget;

} // End llvm namespace

#endif
