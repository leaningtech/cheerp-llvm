; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -slp-vectorizer -slp-vectorizer -mcpu=bdver1 < %s | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@a = common local_unnamed_addr global [1 x i32] zeroinitializer, align 4
@b = common local_unnamed_addr global [1 x i32] zeroinitializer, align 4

define i32 @slp_schedule_bundle() local_unnamed_addr #0 {
; CHECK-LABEL: @slp_schedule_bundle(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[TMP0:%.*]] = load <4 x i32>, <4 x i32>* bitcast (i32* getelementptr inbounds ([1 x i32], [1 x i32]* @b, i64 0, i64 0) to <4 x i32>*), align 4
; CHECK-NEXT:    [[TMP1:%.*]] = lshr <4 x i32> [[TMP0]], <i32 31, i32 31, i32 31, i32 31>
; CHECK-NEXT:    [[TMP2:%.*]] = xor <4 x i32> [[TMP1]], <i32 1, i32 1, i32 1, i32 1>
; CHECK-NEXT:    store <4 x i32> [[TMP2]], <4 x i32>* bitcast ([1 x i32]* @a to <4 x i32>*), align 4
; CHECK-NEXT:    [[TMP3:%.*]] = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 4, i64 0), align 4
; CHECK-NEXT:    [[DOTLOBIT_4:%.*]] = lshr i32 [[TMP3]], 31
; CHECK-NEXT:    [[DOTLOBIT_NOT_4:%.*]] = xor i32 [[DOTLOBIT_4]], 1
; CHECK-NEXT:    store i32 [[DOTLOBIT_NOT_4]], i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 4, i64 0), align 4
; CHECK-NEXT:    [[TMP4:%.*]] = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 5, i64 0), align 4
; CHECK-NEXT:    [[DOTLOBIT_5:%.*]] = lshr i32 [[TMP4]], 31
; CHECK-NEXT:    [[DOTLOBIT_NOT_5:%.*]] = xor i32 [[DOTLOBIT_5]], 1
; CHECK-NEXT:    store i32 [[DOTLOBIT_NOT_5]], i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 5, i64 0), align 4
; CHECK-NEXT:    ret i32 undef
;
entry:
  %0 = load i32, i32* getelementptr inbounds ([1 x i32], [1 x i32]* @b, i64 0, i64 0), align 4
  %.lobit = lshr i32 %0, 31
  %.lobit.not = xor i32 %.lobit, 1
  store i32 %.lobit.not, i32* getelementptr inbounds ([1 x i32], [1 x i32]* @a, i64 0, i64 0), align 4
  %1 = load i32, i32* getelementptr inbounds ([1 x i32], [1 x i32]* @b, i64 1, i64 0), align 4
  %.lobit.1 = lshr i32 %1, 31
  %.lobit.not.1 = xor i32 %.lobit.1, 1
  store i32 %.lobit.not.1, i32* getelementptr inbounds ([1 x i32], [1 x i32]* @a, i64 1, i64 0), align 4
  %2 = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 2, i64 0), align 4
  %.lobit.2 = lshr i32 %2, 31
  %.lobit.not.2 = xor i32 %.lobit.2, 1
  store i32 %.lobit.not.2, i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 2, i64 0), align 4
  %3 = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 3, i64 0), align 4
  %.lobit.3 = lshr i32 %3, 31
  %.lobit.not.3 = xor i32 %.lobit.3, 1
  store i32 %.lobit.not.3, i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 3, i64 0), align 4
  %4 = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 4, i64 0), align 4
  %.lobit.4 = lshr i32 %4, 31
  %.lobit.not.4 = xor i32 %.lobit.4, 1
  store i32 %.lobit.not.4, i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 4, i64 0), align 4
  %5 = load i32, i32* getelementptr ([1 x i32], [1 x i32]* @b, i64 5, i64 0), align 4
  %.lobit.5 = lshr i32 %5, 31
  %.lobit.not.5 = xor i32 %.lobit.5, 1
  store i32 %.lobit.not.5, i32* getelementptr ([1 x i32], [1 x i32]* @a, i64 5, i64 0), align 4
  ret i32 undef
}
