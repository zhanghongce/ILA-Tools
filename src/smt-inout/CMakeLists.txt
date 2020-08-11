# ---------------------------------------------------------------------------- #
# source 
# ---------------------------------------------------------------------------- #
target_sources(${ILANG_LIB_NAME} PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/smt_ast.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/yosys_smt_parser.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/chc_inv_callback_fn.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/chc_inv_in.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/chc_inv_in_wrapper.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/smt-to-ila/smtlib2parser.cc
  ${CMAKE_CURRENT_SOURCE_DIR}/smt-to-ila/smtlib2parser_callback_fn.cc
)

