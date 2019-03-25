; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -slp-vectorizer -S -mtriple=x86_64-unknown-linux-gnu -mcpu=bdver2 < %s | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"

define void @hoge() {
; CHECK-LABEL: @hoge(
; CHECK-NEXT:  bb:
; CHECK-NEXT:    br i1 undef, label [[BB1:%.*]], label [[BB2:%.*]]
; CHECK:       bb1:
; CHECK-NEXT:    ret void
; CHECK:       bb2:
; CHECK-NEXT:    [[TMP:%.*]] = select i1 undef, i16 undef, i16 15
; CHECK-NEXT:    [[TMP0:%.*]] = insertelement <2 x i16> undef, i16 [[TMP]], i32 0
; CHECK-NEXT:    [[TMP1:%.*]] = insertelement <2 x i16> [[TMP0]], i16 undef, i32 1
; CHECK-NEXT:    [[TMP2:%.*]] = sext <2 x i16> [[TMP1]] to <2 x i32>
; CHECK-NEXT:    [[REORDER_SHUFFLE:%.*]] = shufflevector <2 x i32> [[TMP2]], <2 x i32> undef, <2 x i32> <i32 1, i32 0>
; CHECK-NEXT:    [[TMP3:%.*]] = sub nsw <2 x i32> <i32 63, i32 undef>, [[REORDER_SHUFFLE]]
; CHECK-NEXT:    [[TMP4:%.*]] = sub <2 x i32> [[TMP3]], undef
; CHECK-NEXT:    [[SHUFFLE8:%.*]] = shufflevector <2 x i32> [[TMP4]], <2 x i32> undef, <4 x i32> <i32 0, i32 1, i32 1, i32 1>
; CHECK-NEXT:    [[TMP5:%.*]] = add <4 x i32> [[SHUFFLE8]], <i32 undef, i32 15, i32 31, i32 47>
; CHECK-NEXT:    [[TMP11:%.*]] = icmp sgt i32 undef, undef
; CHECK-NEXT:    [[TMP12:%.*]] = select i1 [[TMP11]], i32 undef, i32 undef
; CHECK-NEXT:    [[TMP14:%.*]] = icmp sgt i32 [[TMP12]], undef
; CHECK-NEXT:    [[TMP15:%.*]] = select i1 [[TMP14]], i32 [[TMP12]], i32 undef
; CHECK-NEXT:    [[TMP17:%.*]] = icmp sgt i32 [[TMP15]], undef
; CHECK-NEXT:    [[RDX_SHUF9:%.*]] = shufflevector <4 x i32> [[TMP5]], <4 x i32> undef, <4 x i32> <i32 2, i32 3, i32 undef, i32 undef>
; CHECK-NEXT:    [[RDX_MINMAX_CMP10:%.*]] = icmp sgt <4 x i32> [[TMP5]], [[RDX_SHUF9]]
; CHECK-NEXT:    [[RDX_MINMAX_SELECT11:%.*]] = select <4 x i1> [[RDX_MINMAX_CMP10]], <4 x i32> [[TMP5]], <4 x i32> [[RDX_SHUF9]]
; CHECK-NEXT:    [[RDX_SHUF12:%.*]] = shufflevector <4 x i32> [[RDX_MINMAX_SELECT11]], <4 x i32> undef, <4 x i32> <i32 1, i32 undef, i32 undef, i32 undef>
; CHECK-NEXT:    [[RDX_MINMAX_CMP13:%.*]] = icmp sgt <4 x i32> [[RDX_MINMAX_SELECT11]], [[RDX_SHUF12]]
; CHECK-NEXT:    [[RDX_MINMAX_SELECT14:%.*]] = select <4 x i1> [[RDX_MINMAX_CMP13]], <4 x i32> [[RDX_MINMAX_SELECT11]], <4 x i32> [[RDX_SHUF12]]
; CHECK-NEXT:    [[TMP6:%.*]] = extractelement <4 x i32> [[RDX_MINMAX_SELECT14]], i32 0
; CHECK-NEXT:    [[TMP18:%.*]] = select i1 [[TMP17]], i32 [[TMP15]], i32 undef
; CHECK-NEXT:    [[TMP19:%.*]] = select i1 undef, i32 [[TMP6]], i32 undef
; CHECK-NEXT:    [[TMP20:%.*]] = icmp sgt i32 [[TMP19]], 63
; CHECK-NEXT:    [[TMP7:%.*]] = sub nsw <2 x i32> undef, [[TMP2]]
; CHECK-NEXT:    [[TMP8:%.*]] = sub <2 x i32> [[TMP7]], undef
; CHECK-NEXT:    [[SHUFFLE:%.*]] = shufflevector <2 x i32> [[TMP8]], <2 x i32> undef, <4 x i32> <i32 0, i32 1, i32 0, i32 1>
; CHECK-NEXT:    [[TMP9:%.*]] = add nsw <4 x i32> [[SHUFFLE]], <i32 -49, i32 -33, i32 -33, i32 -17>
; CHECK-NEXT:    [[TMP26:%.*]] = icmp sgt i32 undef, undef
; CHECK-NEXT:    [[TMP27:%.*]] = select i1 [[TMP26]], i32 undef, i32 undef
; CHECK-NEXT:    [[TMP28:%.*]] = icmp sgt i32 [[TMP27]], undef
; CHECK-NEXT:    [[TMP29:%.*]] = select i1 [[TMP28]], i32 undef, i32 [[TMP27]]
; CHECK-NEXT:    [[TMP31:%.*]] = icmp sgt i32 undef, undef
; CHECK-NEXT:    [[TMP32:%.*]] = select i1 [[TMP31]], i32 undef, i32 undef
; CHECK-NEXT:    [[TMP33:%.*]] = icmp sgt i32 [[TMP32]], [[TMP29]]
; CHECK-NEXT:    [[TMP34:%.*]] = select i1 [[TMP33]], i32 [[TMP29]], i32 [[TMP32]]
; CHECK-NEXT:    [[TMP36:%.*]] = icmp sgt i32 undef, undef
; CHECK-NEXT:    [[TMP37:%.*]] = select i1 [[TMP36]], i32 undef, i32 undef
; CHECK-NEXT:    [[TMP38:%.*]] = icmp sgt i32 [[TMP37]], [[TMP34]]
; CHECK-NEXT:    [[TMP39:%.*]] = select i1 [[TMP38]], i32 [[TMP34]], i32 [[TMP37]]
; CHECK-NEXT:    [[TMP41:%.*]] = icmp sgt i32 undef, undef
; CHECK-NEXT:    [[TMP42:%.*]] = select i1 [[TMP41]], i32 undef, i32 undef
; CHECK-NEXT:    [[TMP43:%.*]] = icmp sgt i32 [[TMP42]], [[TMP39]]
; CHECK-NEXT:    [[RDX_SHUF:%.*]] = shufflevector <4 x i32> [[TMP9]], <4 x i32> undef, <4 x i32> <i32 2, i32 3, i32 undef, i32 undef>
; CHECK-NEXT:    [[RDX_MINMAX_CMP:%.*]] = icmp slt <4 x i32> [[TMP9]], [[RDX_SHUF]]
; CHECK-NEXT:    [[RDX_MINMAX_SELECT:%.*]] = select <4 x i1> [[RDX_MINMAX_CMP]], <4 x i32> [[TMP9]], <4 x i32> [[RDX_SHUF]]
; CHECK-NEXT:    [[RDX_SHUF1:%.*]] = shufflevector <4 x i32> [[RDX_MINMAX_SELECT]], <4 x i32> undef, <4 x i32> <i32 1, i32 undef, i32 undef, i32 undef>
; CHECK-NEXT:    [[RDX_MINMAX_CMP2:%.*]] = icmp slt <4 x i32> [[RDX_MINMAX_SELECT]], [[RDX_SHUF1]]
; CHECK-NEXT:    [[RDX_MINMAX_SELECT3:%.*]] = select <4 x i1> [[RDX_MINMAX_CMP2]], <4 x i32> [[RDX_MINMAX_SELECT]], <4 x i32> [[RDX_SHUF1]]
; CHECK-NEXT:    [[TMP10:%.*]] = extractelement <4 x i32> [[RDX_MINMAX_SELECT3]], i32 0
; CHECK-NEXT:    [[TMP11:%.*]] = icmp slt i32 [[TMP10]], undef
; CHECK-NEXT:    [[OP_EXTRA:%.*]] = select i1 [[TMP11]], i32 [[TMP10]], i32 undef
; CHECK-NEXT:    [[TMP12:%.*]] = icmp slt i32 [[OP_EXTRA]], undef
; CHECK-NEXT:    [[OP_EXTRA4:%.*]] = select i1 [[TMP12]], i32 [[OP_EXTRA]], i32 undef
; CHECK-NEXT:    [[TMP13:%.*]] = icmp slt i32 [[OP_EXTRA4]], undef
; CHECK-NEXT:    [[OP_EXTRA5:%.*]] = select i1 [[TMP13]], i32 [[OP_EXTRA4]], i32 undef
; CHECK-NEXT:    [[TMP14:%.*]] = icmp slt i32 [[OP_EXTRA5]], undef
; CHECK-NEXT:    [[OP_EXTRA6:%.*]] = select i1 [[TMP14]], i32 [[OP_EXTRA5]], i32 undef
; CHECK-NEXT:    [[TMP15:%.*]] = icmp slt i32 [[OP_EXTRA6]], undef
; CHECK-NEXT:    [[OP_EXTRA7:%.*]] = select i1 [[TMP15]], i32 [[OP_EXTRA6]], i32 undef
; CHECK-NEXT:    [[TMP44:%.*]] = select i1 [[TMP43]], i32 [[TMP39]], i32 [[TMP42]]
; CHECK-NEXT:    [[TMP45:%.*]] = icmp sgt i32 undef, [[OP_EXTRA7]]
; CHECK-NEXT:    unreachable
;
bb:
  br i1 undef, label %bb1, label %bb2

bb1:                                              ; preds = %bb
  ret void

bb2:                                              ; preds = %bb
  %tmp = select i1 undef, i16 undef, i16 15
  %tmp3 = sext i16 undef to i32
  %tmp4 = sext i16 %tmp to i32
  %tmp5 = sub nsw i32 undef, %tmp4
  %tmp6 = sub i32 %tmp5, undef
  %tmp7 = sub nsw i32 63, %tmp3
  %tmp8 = sub i32 %tmp7, undef
  %tmp9 = add i32 %tmp8, undef
  %tmp10 = add nsw i32 %tmp6, 15
  %tmp11 = icmp sgt i32 %tmp9, %tmp10
  %tmp12 = select i1 %tmp11, i32 %tmp9, i32 %tmp10
  %tmp13 = add nsw i32 %tmp6, 31
  %tmp14 = icmp sgt i32 %tmp12, %tmp13
  %tmp15 = select i1 %tmp14, i32 %tmp12, i32 %tmp13
  %tmp16 = add nsw i32 %tmp6, 47
  %tmp17 = icmp sgt i32 %tmp15, %tmp16
  %tmp18 = select i1 %tmp17, i32 %tmp15, i32 %tmp16
  %tmp19 = select i1 undef, i32 %tmp18, i32 undef
  %tmp20 = icmp sgt i32 %tmp19, 63
  %tmp21 = sub nsw i32 undef, %tmp3
  %tmp22 = sub i32 %tmp21, undef
  %tmp23 = sub nsw i32 undef, %tmp4
  %tmp24 = sub i32 %tmp23, undef
  %tmp25 = add nsw i32 %tmp24, -49
  %tmp26 = icmp sgt i32 %tmp25, undef
  %tmp27 = select i1 %tmp26, i32 undef, i32 %tmp25
  %tmp28 = icmp sgt i32 %tmp27, undef
  %tmp29 = select i1 %tmp28, i32 undef, i32 %tmp27
  %tmp30 = add nsw i32 %tmp22, -33
  %tmp31 = icmp sgt i32 %tmp30, undef
  %tmp32 = select i1 %tmp31, i32 undef, i32 %tmp30
  %tmp33 = icmp sgt i32 %tmp32, %tmp29
  %tmp34 = select i1 %tmp33, i32 %tmp29, i32 %tmp32
  %tmp35 = add nsw i32 %tmp24, -33
  %tmp36 = icmp sgt i32 %tmp35, undef
  %tmp37 = select i1 %tmp36, i32 undef, i32 %tmp35
  %tmp38 = icmp sgt i32 %tmp37, %tmp34
  %tmp39 = select i1 %tmp38, i32 %tmp34, i32 %tmp37
  %tmp40 = add nsw i32 %tmp22, -17
  %tmp41 = icmp sgt i32 %tmp40, undef
  %tmp42 = select i1 %tmp41, i32 undef, i32 %tmp40
  %tmp43 = icmp sgt i32 %tmp42, %tmp39
  %tmp44 = select i1 %tmp43, i32 %tmp39, i32 %tmp42
  %tmp45 = icmp sgt i32 undef, %tmp44
  unreachable
}

