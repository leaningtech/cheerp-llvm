set(LLVM_LINK_COMPONENTS ${LLVM_TARGETS_TO_BUILD} bitreader bitwriter asmparser)

add_llvm_tool(duetto
  duetto.cpp
  )
