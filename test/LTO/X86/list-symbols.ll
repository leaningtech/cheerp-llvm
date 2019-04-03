; RUN: llvm-as -o %T/1.bc %s
; RUN: llvm-as -o %T/2.bc %S/Inputs/list-symbols.ll
; RUN: llvm-lto -list-symbols-only %T/1.bc %T/2.bc | FileCheck %s
; REQUIRES: default_triple

; CHECK-LABEL: 1.bc:
; CHECK-DAG: foo
; CHECK-DAG: glob
; CHECK-LABEL: 2.bc:
; CHECK-DAG: glob
; CHECK-DAG: bar

target triple = "x86_64-apple-macosx10.10.0"

@glob = global i32 0
define void @foo() {
  ret void
}
