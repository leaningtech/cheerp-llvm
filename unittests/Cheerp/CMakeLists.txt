set(LLVM_LINK_COMPONENTS
  CheerpWriter
  Core
  IRReader
  )

add_llvm_unittest(CheerpTests
  CheerpPointerAnalyzerTest.cpp
  )

configure_file( test1.ll ${CMAKE_CURRENT_BINARY_DIR}/test1.ll COPYONLY )
