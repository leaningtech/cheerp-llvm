; Tests to make sure elimination of casts is working correctly
; RUN: opt < %s -instcombine -S | FileCheck %s

target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128"
define i64 @test_sext_zext(i16 %A) {
        %c1 = zext i16 %A to i32                ; <i32> [#uses=1]
        %c2 = sext i32 %c1 to i64               ; <i64> [#uses=1]
        ret i64 %c2
; CHECK-NOT: %c1
; CHECK: %c2 = zext i16 %A to i64
; CHECK: ret i64 %c2
}
