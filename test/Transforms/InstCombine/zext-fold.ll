; RUN: opt < %s -instcombine -S | grep "zext " | count 1
; PR1570

target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128"
define i32 @test2(float %X, float %Y) {
entry:
        %tmp3 = fcmp uno float %X, %Y           ; <i1> [#uses=1]
        %tmp34 = zext i1 %tmp3 to i8            ; <i8> [#uses=1]
        %tmp = xor i8 %tmp34, 1         ; <i8> [#uses=1]
        %toBoolnot5 = zext i8 %tmp to i32               ; <i32> [#uses=1]
        ret i32 %toBoolnot5
}

