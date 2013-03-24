set(LLVM_LINK_COMPONENTS ${LLVM_TARGETS_TO_BUILD} all)

add_llvm_tool(duetto
  duetto.cpp
  )
