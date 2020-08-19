; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -slp-vectorizer < %s -S | FileCheck %s

; Verify that the SLP vectorizer is able to figure out that commutativity
; offers the possibility to splat/broadcast %c and thus make it profitable
; to vectorize this case


; ModuleID = 'bugpoint-reduced-simplified.bc'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.11.0"

@cle = external unnamed_addr global [32 x i8], align 16
@cle32 = external unnamed_addr global [32 x i32], align 16


; Check that we correctly detect a splat/broadcast by leveraging the
; commutativity property of `xor`.

define void @splat(i8 %a, i8 %b, i8 %c) {
; CHECK-LABEL: @splat(
; CHECK-NEXT:    [[TMP1:%.*]] = insertelement <16 x i8> undef, i8 [[C:%.*]], i32 0
; CHECK-NEXT:    [[TMP2:%.*]] = insertelement <16 x i8> [[TMP1]], i8 [[C]], i32 1
; CHECK-NEXT:    [[TMP3:%.*]] = insertelement <16 x i8> [[TMP2]], i8 [[C]], i32 2
; CHECK-NEXT:    [[TMP4:%.*]] = insertelement <16 x i8> [[TMP3]], i8 [[C]], i32 3
; CHECK-NEXT:    [[TMP5:%.*]] = insertelement <16 x i8> [[TMP4]], i8 [[C]], i32 4
; CHECK-NEXT:    [[TMP6:%.*]] = insertelement <16 x i8> [[TMP5]], i8 [[C]], i32 5
; CHECK-NEXT:    [[TMP7:%.*]] = insertelement <16 x i8> [[TMP6]], i8 [[C]], i32 6
; CHECK-NEXT:    [[TMP8:%.*]] = insertelement <16 x i8> [[TMP7]], i8 [[C]], i32 7
; CHECK-NEXT:    [[TMP9:%.*]] = insertelement <16 x i8> [[TMP8]], i8 [[C]], i32 8
; CHECK-NEXT:    [[TMP10:%.*]] = insertelement <16 x i8> [[TMP9]], i8 [[C]], i32 9
; CHECK-NEXT:    [[TMP11:%.*]] = insertelement <16 x i8> [[TMP10]], i8 [[C]], i32 10
; CHECK-NEXT:    [[TMP12:%.*]] = insertelement <16 x i8> [[TMP11]], i8 [[C]], i32 11
; CHECK-NEXT:    [[TMP13:%.*]] = insertelement <16 x i8> [[TMP12]], i8 [[C]], i32 12
; CHECK-NEXT:    [[TMP14:%.*]] = insertelement <16 x i8> [[TMP13]], i8 [[C]], i32 13
; CHECK-NEXT:    [[TMP15:%.*]] = insertelement <16 x i8> [[TMP14]], i8 [[C]], i32 14
; CHECK-NEXT:    [[TMP16:%.*]] = insertelement <16 x i8> [[TMP15]], i8 [[C]], i32 15
; CHECK-NEXT:    [[TMP17:%.*]] = insertelement <2 x i8> undef, i8 [[A:%.*]], i32 0
; CHECK-NEXT:    [[TMP18:%.*]] = insertelement <2 x i8> [[TMP17]], i8 [[B:%.*]], i32 1
; CHECK-NEXT:    [[SHUFFLE:%.*]] = shufflevector <2 x i8> [[TMP18]], <2 x i8> undef, <16 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 0, i32 1, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
; CHECK-NEXT:    [[TMP19:%.*]] = xor <16 x i8> [[TMP16]], [[SHUFFLE]]
; CHECK-NEXT:    store <16 x i8> [[TMP19]], <16 x i8>* bitcast (i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 0) to <16 x i8>*), align 16
; CHECK-NEXT:    ret void
;
  %1 = xor i8 %c, %a
  store i8 %1, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 0), align 16
  %2 = xor i8 %a, %c
  store i8 %2, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 1)
  %3 = xor i8 %a, %c
  store i8 %3, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 2)
  %4 = xor i8 %a, %c
  store i8 %4, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 3)
  %5 = xor i8 %c, %a
  store i8 %5, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 4)
  %6 = xor i8 %c, %b
  store i8 %6, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 5)
  %7 = xor i8 %c, %a
  store i8 %7, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 6)
  %8 = xor i8 %c, %b
  store i8 %8, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 7)
  %9 = xor i8 %a, %c
  store i8 %9, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 8)
  %10 = xor i8 %a, %c
  store i8 %10, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 9)
  %11 = xor i8 %a, %c
  store i8 %11, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 10)
  %12 = xor i8 %a, %c
  store i8 %12, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 11)
  %13 = xor i8 %a, %c
  store i8 %13, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 12)
  %14 = xor i8 %a, %c
  store i8 %14, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 13)
  %15 = xor i8 %a, %c
  store i8 %15, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 14)
  %16 = xor i8 %a, %c
  store i8 %16, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @cle, i64 0, i64 15)
  ret void
}



; Check that we correctly detect that we can have the same opcode on one side by
; leveraging the commutativity property of `xor`.

define void @same_opcode_on_one_side(i32 %a, i32 %b, i32 %c) {
; CHECK-LABEL: @same_opcode_on_one_side(
; CHECK-NEXT:    [[TMP1:%.*]] = insertelement <4 x i32> undef, i32 [[C:%.*]], i32 0
; CHECK-NEXT:    [[TMP2:%.*]] = insertelement <4 x i32> [[TMP1]], i32 [[C]], i32 1
; CHECK-NEXT:    [[TMP3:%.*]] = insertelement <4 x i32> [[TMP2]], i32 [[C]], i32 2
; CHECK-NEXT:    [[TMP4:%.*]] = insertelement <4 x i32> [[TMP3]], i32 [[C]], i32 3
; CHECK-NEXT:    [[TMP5:%.*]] = insertelement <4 x i32> undef, i32 [[A:%.*]], i32 0
; CHECK-NEXT:    [[TMP6:%.*]] = insertelement <4 x i32> [[TMP5]], i32 [[A]], i32 1
; CHECK-NEXT:    [[TMP7:%.*]] = insertelement <4 x i32> [[TMP6]], i32 [[A]], i32 2
; CHECK-NEXT:    [[TMP8:%.*]] = insertelement <4 x i32> [[TMP7]], i32 [[A]], i32 3
; CHECK-NEXT:    [[TMP9:%.*]] = add <4 x i32> [[TMP4]], [[TMP8]]
; CHECK-NEXT:    [[TMP10:%.*]] = insertelement <4 x i32> [[TMP5]], i32 [[B:%.*]], i32 1
; CHECK-NEXT:    [[TMP11:%.*]] = insertelement <4 x i32> [[TMP10]], i32 [[C]], i32 2
; CHECK-NEXT:    [[TMP12:%.*]] = insertelement <4 x i32> [[TMP11]], i32 [[A]], i32 3
; CHECK-NEXT:    [[TMP13:%.*]] = xor <4 x i32> [[TMP9]], [[TMP12]]
; CHECK-NEXT:    store <4 x i32> [[TMP13]], <4 x i32>* bitcast ([32 x i32]* @cle32 to <4 x i32>*), align 16
; CHECK-NEXT:    ret void
;
  %add1 = add i32 %c, %a
  %add2 = add i32 %c, %a
  %add3 = add i32 %a, %c
  %add4 = add i32 %c, %a
  %1 = xor i32 %add1, %a
  store i32 %1, i32* getelementptr inbounds ([32 x i32], [32 x i32]* @cle32, i64 0, i64 0), align 16
  %2 = xor i32 %b, %add2
  store i32 %2, i32* getelementptr inbounds ([32 x i32], [32 x i32]* @cle32, i64 0, i64 1)
  %3 = xor i32 %c, %add3
  store i32 %3, i32* getelementptr inbounds ([32 x i32], [32 x i32]* @cle32, i64 0, i64 2)
  %4 = xor i32 %a, %add4
  store i32 %4, i32* getelementptr inbounds ([32 x i32], [32 x i32]* @cle32, i64 0, i64 3)
  ret void
}
