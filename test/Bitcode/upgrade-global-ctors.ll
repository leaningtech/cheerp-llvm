; RUN:  llvm-dis < %s.bc

; Global constructors should no longer be upgraded when reading bitcode.
; CHECK: @llvm.global_ctors = appending global [0 x { i32, void ()* }] zeroinitializer
