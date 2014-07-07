; RUN: llvm-dis < %s.bc| FileCheck %s
; RUN: verify-uselistorder < %s.bc

; memOperations.3.2.ll.bc was generated by passing this file to llvm-as-3.2.
; The test checks that LLVM does not misread memory related instructions of
; older bitcode files.

define void @alloca(){
entry:
; CHECK: %res1 = alloca i8
  %res1 = alloca i8

; CHECK-NEXT: %res2 = alloca i8, i32 2
  %res2 = alloca i8, i32 2

; CHECK-NEXT: %res3 = alloca i8, i32 2, align 4
  %res3 = alloca i8, i32 2, align 4

; CHECK-NEXT: %res4 = alloca i8, align 4
  %res4 = alloca i8, align 4

  ret void
}

define void @load(){
entry:
  %ptr1 = alloca i8
  store i8 2, i8* %ptr1

; CHECK: %res1 = load i8, i8* %ptr1
  %res1 = load i8, i8* %ptr1

; CHECK-NEXT: %res2 = load volatile i8, i8* %ptr1
  %res2 = load volatile i8, i8* %ptr1

; CHECK-NEXT: %res3 = load i8, i8* %ptr1, align 1
  %res3 = load i8, i8* %ptr1, align 1

; CHECK-NEXT: %res4 = load volatile i8, i8* %ptr1, align 1
  %res4 = load volatile i8, i8* %ptr1, align 1

; CHECK-NEXT: %res5 = load i8, i8* %ptr1, !nontemporal !0
  %res5 = load i8, i8* %ptr1, !nontemporal !0

; CHECK-NEXT: %res6 = load volatile i8, i8* %ptr1, !nontemporal !0
  %res6 = load volatile i8, i8* %ptr1, !nontemporal !0

; CHECK-NEXT: %res7 = load i8, i8* %ptr1, align 1, !nontemporal !0
  %res7 = load i8, i8* %ptr1, align 1, !nontemporal !0

; CHECK-NEXT: %res8 = load volatile i8, i8* %ptr1, align 1, !nontemporal !0
  %res8 = load volatile i8, i8* %ptr1, align 1, !nontemporal !0

; CHECK-NEXT: %res9 = load i8, i8* %ptr1, !invariant.load !1
  %res9 = load i8, i8* %ptr1, !invariant.load !1

; CHECK-NEXT: %res10 = load volatile i8, i8* %ptr1, !invariant.load !1
  %res10 = load volatile i8, i8* %ptr1, !invariant.load !1

; CHECK-NEXT: %res11 = load i8, i8* %ptr1, align 1, !invariant.load !1
  %res11 = load i8, i8* %ptr1, align 1, !invariant.load !1

; CHECK-NEXT: %res12 = load volatile i8, i8* %ptr1, align 1, !invariant.load !1
  %res12 = load volatile i8, i8* %ptr1, align 1, !invariant.load !1

; CHECK-NEXT: %res13 = load i8, i8* %ptr1, {{[(!nontemporal !0, !invariant.load !1) | (!invariant.load !1, !nontemporal !0)]}}
  %res13 = load i8, i8* %ptr1, !nontemporal !0, !invariant.load !1

; CHECK-NEXT: %res14 = load volatile i8, i8* %ptr1, {{[(!nontemporal !0, !invariant.load !1) | (!invariant.load !1, !nontemporal !0)]}}
  %res14 = load volatile i8, i8* %ptr1, !nontemporal !0, !invariant.load !1

; CHECK-NEXT: %res15 = load i8, i8* %ptr1, align 1, {{[(!nontemporal !0, !invariant.load !1) | (!invariant.load !1, !nontemporal !0)]}}
  %res15 = load i8, i8* %ptr1, align 1, !nontemporal !0, !invariant.load !1

; CHECK-NEXT: %res16 = load volatile i8, i8* %ptr1, align 1, {{[(!nontemporal !0, !invariant.load !1) | (!invariant.load !1, !nontemporal !0)]}}
  %res16 = load volatile i8, i8* %ptr1, align 1, !nontemporal !0, !invariant.load !1

  ret void
}

define void @loadAtomic(){
entry:
  %ptr1 = alloca i8
  store i8 2, i8* %ptr1

; CHECK: %res1 = load atomic i8, i8* %ptr1 unordered, align 1
  %res1 = load atomic i8, i8* %ptr1 unordered, align 1

; CHECK-NEXT: %res2 = load atomic i8, i8* %ptr1 monotonic, align 1
  %res2 = load atomic i8, i8* %ptr1 monotonic, align 1

; CHECK-NEXT: %res3 = load atomic i8, i8* %ptr1 acquire, align 1
  %res3 = load atomic i8, i8* %ptr1 acquire, align 1

; CHECK-NEXT: %res4 = load atomic i8, i8* %ptr1 seq_cst, align 1
  %res4 = load atomic i8, i8* %ptr1 seq_cst, align 1

; CHECK-NEXT: %res5 = load atomic volatile i8, i8* %ptr1 unordered, align 1
  %res5 = load atomic volatile i8, i8* %ptr1 unordered, align 1

; CHECK-NEXT: %res6 = load atomic volatile i8, i8* %ptr1 monotonic, align 1
  %res6 = load atomic volatile i8, i8* %ptr1 monotonic, align 1

; CHECK-NEXT: %res7 = load atomic volatile i8, i8* %ptr1 acquire, align 1
  %res7 = load atomic volatile i8, i8* %ptr1 acquire, align 1

; CHECK-NEXT: %res8 = load atomic volatile i8, i8* %ptr1 seq_cst, align 1
  %res8 = load atomic volatile i8, i8* %ptr1 seq_cst, align 1

; CHECK-NEXT: %res9 = load atomic i8, i8* %ptr1 syncscope("singlethread") unordered, align 1
  %res9 = load atomic i8, i8* %ptr1 syncscope("singlethread") unordered, align 1

; CHECK-NEXT: %res10 = load atomic i8, i8* %ptr1 syncscope("singlethread") monotonic, align 1
  %res10 = load atomic i8, i8* %ptr1 syncscope("singlethread") monotonic, align 1

; CHECK-NEXT: %res11 = load atomic i8, i8* %ptr1 syncscope("singlethread") acquire, align 1
  %res11 = load atomic i8, i8* %ptr1 syncscope("singlethread") acquire, align 1

; CHECK-NEXT: %res12 = load atomic i8, i8* %ptr1 syncscope("singlethread") seq_cst, align 1
  %res12 = load atomic i8, i8* %ptr1 syncscope("singlethread") seq_cst, align 1

; CHECK-NEXT: %res13 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") unordered, align 1
  %res13 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") unordered, align 1

; CHECK-NEXT: %res14 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") monotonic, align 1
  %res14 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") monotonic, align 1

; CHECK-NEXT: %res15 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") acquire, align 1
  %res15 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") acquire, align 1

; CHECK-NEXT: %res16 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") seq_cst, align 1
  %res16 = load atomic volatile i8, i8* %ptr1 syncscope("singlethread") seq_cst, align 1

  ret void
}

define void @store(){
entry:
  %ptr1 = alloca i8

; CHECK: store i8 2, i8* %ptr1
  store i8 2, i8* %ptr1

; CHECK-NEXT: store volatile i8 2, i8* %ptr1
  store volatile i8 2, i8* %ptr1

; CHECK-NEXT: store i8 2, i8* %ptr1, align 1
  store i8 2, i8* %ptr1, align 1

; CHECK-NEXT: store volatile i8 2, i8* %ptr1, align 1
  store volatile i8 2, i8* %ptr1, align 1

; CHECK-NEXT: store i8 2, i8* %ptr1, !nontemporal !0
  store i8 2, i8* %ptr1, !nontemporal !0

; CHECK-NEXT: store volatile i8 2, i8* %ptr1, !nontemporal !0
  store volatile i8 2, i8* %ptr1, !nontemporal !0

; CHECK-NEXT: store i8 2, i8* %ptr1, align 1, !nontemporal !0
  store i8 2, i8* %ptr1, align 1, !nontemporal !0

; CHECK-NEXT: store volatile i8 2, i8* %ptr1, align 1, !nontemporal !0
  store volatile i8 2, i8* %ptr1, align 1, !nontemporal !0

  ret void
}

define void @storeAtomic(){
entry:
  %ptr1 = alloca i8

; CHECK: store atomic i8 2, i8* %ptr1 unordered, align 1
  store atomic i8 2, i8* %ptr1 unordered, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 monotonic, align 1
  store atomic i8 2, i8* %ptr1 monotonic, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 release, align 1
  store atomic i8 2, i8* %ptr1 release, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 seq_cst, align 1
  store atomic i8 2, i8* %ptr1 seq_cst, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 unordered, align 1
  store atomic volatile i8 2, i8* %ptr1 unordered, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 monotonic, align 1
  store atomic volatile i8 2, i8* %ptr1 monotonic, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 release, align 1
  store atomic volatile i8 2, i8* %ptr1 release, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 seq_cst, align 1
  store atomic volatile i8 2, i8* %ptr1 seq_cst, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 syncscope("singlethread") unordered, align 1
  store atomic i8 2, i8* %ptr1 syncscope("singlethread") unordered, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 syncscope("singlethread") monotonic, align 1
  store atomic i8 2, i8* %ptr1 syncscope("singlethread") monotonic, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 syncscope("singlethread") release, align 1
  store atomic i8 2, i8* %ptr1 syncscope("singlethread") release, align 1

; CHECK-NEXT: store atomic i8 2, i8* %ptr1 syncscope("singlethread") seq_cst, align 1
  store atomic i8 2, i8* %ptr1 syncscope("singlethread") seq_cst, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") unordered, align 1
  store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") unordered, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") monotonic, align 1
  store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") monotonic, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") release, align 1
  store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") release, align 1

; CHECK-NEXT: store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") seq_cst, align 1
  store atomic volatile i8 2, i8* %ptr1 syncscope("singlethread") seq_cst, align 1

  ret void
}

define void @cmpxchg(i32* %ptr,i32 %cmp,i32 %new){
entry:
  ;cmpxchg [volatile] <ty>* <pointer>, <ty> <cmp>, <ty> <new> [singlethread] <ordering>

; CHECK: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new monotonic monotonic
  %res1 = cmpxchg i32* %ptr, i32 %cmp, i32 %new monotonic monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new monotonic monotonic
  %res2 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new monotonic monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") monotonic monotonic
; CHECK-NEXT: %res3 = extractvalue { i32, i1 } [[TMP]], 0
  %res3 = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") monotonic monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") monotonic monotonic
; CHECK-NEXT: %res4 = extractvalue { i32, i1 } [[TMP]], 0
  %res4 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") monotonic monotonic


; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new acquire acquire
  %res5 = cmpxchg i32* %ptr, i32 %cmp, i32 %new acquire acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new acquire acquire
  %res6 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new acquire acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acquire acquire
; CHECK-NEXT: %res7 = extractvalue { i32, i1 } [[TMP]], 0
  %res7 = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acquire acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acquire acquire
; CHECK-NEXT: %res8 = extractvalue { i32, i1 } [[TMP]], 0
  %res8 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acquire acquire


; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new release monotonic
  %res9 = cmpxchg i32* %ptr, i32 %cmp, i32 %new release monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new release monotonic
  %res10 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new release monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") release monotonic
; CHECK-NEXT: %res11 = extractvalue { i32, i1 } [[TMP]], 0
  %res11 = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") release monotonic

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") release monotonic
; CHECK-NEXT: %res12 = extractvalue { i32, i1 } [[TMP]], 0
  %res12 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") release monotonic


; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new acq_rel acquire
  %res13 = cmpxchg i32* %ptr, i32 %cmp, i32 %new acq_rel acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new acq_rel acquire
  %res14 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new acq_rel acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acq_rel acquire
; CHECK-NEXT: %res15 = extractvalue { i32, i1 } [[TMP]], 0
  %res15 = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acq_rel acquire

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acq_rel acquire
; CHECK-NEXT: %res16 = extractvalue { i32, i1 } [[TMP]], 0
  %res16 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") acq_rel acquire


; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new seq_cst seq_cst
  %res17 = cmpxchg i32* %ptr, i32 %cmp, i32 %new seq_cst seq_cst

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new seq_cst seq_cst
  %res18 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new seq_cst seq_cst

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") seq_cst seq_cst
; CHECK-NEXT: %res19 = extractvalue { i32, i1 } [[TMP]], 0
  %res19 = cmpxchg i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") seq_cst seq_cst

; CHECK-NEXT: [[TMP:%[a-z0-9]+]] = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") seq_cst seq_cst
; CHECK-NEXT: %res20 = extractvalue { i32, i1 } [[TMP]], 0
  %res20 = cmpxchg volatile i32* %ptr, i32 %cmp, i32 %new syncscope("singlethread") seq_cst seq_cst

  ret void
}

define void @getelementptr({i8, i8}, {i8, i8}* %s, <4 x i8*> %ptrs, <4 x i64> %offsets ){
entry:
; CHECK: %res1 = getelementptr { i8, i8 }, { i8, i8 }* %s, i32 1, i32 1
  %res1 = getelementptr {i8, i8}, {i8, i8}* %s, i32 1, i32 1

; CHECK-NEXT: %res2 = getelementptr inbounds { i8, i8 }, { i8, i8 }* %s, i32 1, i32 1
  %res2 = getelementptr inbounds {i8, i8}, {i8, i8}* %s, i32 1, i32 1

; CHECK-NEXT: %res3 = getelementptr i8, <4 x i8*> %ptrs, <4 x i64> %offsets
  %res3 = getelementptr i8, <4 x i8*> %ptrs, <4 x i64> %offsets

  ret void
}

!0 = !{ i32 1 }
!1 = !{}
