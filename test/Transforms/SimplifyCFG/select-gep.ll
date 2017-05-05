; RUN: opt -S -simplifycfg < %s | FileCheck %s
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%ST = type { i8, i8 }

define i8* @test1(%ST* %x, i8* %y) nounwind {
entry:
  %cmp = icmp eq %ST* %x, null
  br i1 %cmp, label %if.then, label %if.end

if.then:
  %incdec.ptr = getelementptr %ST, %ST* %x, i32 0, i32 1
  br label %if.end

if.end:
  %x.addr = phi i8* [ %incdec.ptr, %if.then ], [ %y, %entry ]
  ret i8* %x.addr

; CHECK-LABEL: @test1(
; CHECK: %incdec.ptr.y = select i1 %cmp, i8* %incdec.ptr, i8* %y
; CHECK: ret i8* %incdec.ptr.y
}
