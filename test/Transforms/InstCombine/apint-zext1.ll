; Tests to make sure elimination of casts is working correctly
; This test is for Integer BitWidth <= 64 && BitWidth % 2 != 0.
; RUN: opt < %s -instcombine -S | FileCheck %s

target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128"
define i47 @test_sext_zext(i11 %A) {
    %c1 = zext i11 %A to i39
    %c2 = sext i39 %c1 to i47
    ret i47 %c2
; CHECK: %c2 = zext i11 %A to i47
; CHECK: ret i47 %c2
}
