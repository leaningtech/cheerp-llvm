; Tests to make sure elimination of casts is working correctly
; This test is for Integer BitWidth > 64 && BitWidth <= 1024.
; RUN: opt < %s -instcombine -S | FileCheck %s

target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128"
define i1024 @test_sext_zext(i77 %A) {
    %c1 = zext i77 %A to i533
    %c2 = sext i533 %c1 to i1024
    ret i1024 %c2
; CHECK: %c2 = zext i77 %A to i1024
; CHECK: ret i1024 %c2
}
