//===-- CheerpTargetMachine.h - TargetMachine for the CheerpBackend -------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2019 Leaning Technlogies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_TARGETMACHINE_H
#define _CHEERP_TARGETMACHINE_H

#include "llvm/ADT/Optional.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLowering.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetSubtargetInfo.h"

namespace llvm {

class formatted_raw_ostream;

class CheerpTargetLowering: public TargetLowering {
public:
  CheerpTargetLowering(const TargetMachine &TM) : TargetLowering(TM) {}
};

class CheerpSubtarget: public TargetSubtargetInfo {
private:
  CheerpTargetLowering targetLowering;
public:
  CheerpSubtarget(const TargetMachine &TM, const Target &T, const Triple& TT, StringRef CPU, StringRef FS) :
        TargetSubtargetInfo(TT, CPU, FS, None, None, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr),
        targetLowering(TM) { }
  virtual const CheerpTargetLowering *getTargetLowering() const override;
};

struct CheerpTargetMachine : public LLVMTargetMachine {
  CheerpTargetMachine(const Target &T, const Triple& TT,
                   StringRef CPU, StringRef FS, const TargetOptions &Options,
                   Optional<Reloc::Model> RM, CodeModel::Model CM,
                   CodeGenOpt::Level OL)
      : LLVMTargetMachine(T, "b-e-p:32:8:8-i1:8:8-i8:8:8-i16:8:8-i32:8:8-"
                        "i64:8:8-f32:8:8-f64:8:8-"
                        "a0:0:8-f80:8:8-n8:8:8-S8",
                      TT, CPU, FS, Options, Reloc::PIC_, CM, OL),
        subTargetInfo(*this, T, TT, CPU, FS) { }
  CheerpSubtarget subTargetInfo;

public:
  virtual bool addPassesToEmitFile(PassManagerBase &PM,
                                   raw_pwrite_stream &Out,
                                   CodeGenFileType FileType,
                                   bool DisableVerify,
                                   AnalysisID StartBefore,
                                   AnalysisID StartAfter,
                                   AnalysisID StopBefore,
                                   AnalysisID StopAfter,
                                   MachineFunctionInitializer* MFInit) override;
  virtual const CheerpSubtarget* getSubtargetImpl(const Function &F) const override;
};

extern Target TheCheerpBackendTarget;

} // End llvm namespace

#endif
