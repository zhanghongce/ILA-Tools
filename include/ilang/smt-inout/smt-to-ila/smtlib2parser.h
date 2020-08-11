/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the ilang2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SMT-LIB2 expression parser
 **
 ** 
 **/


#ifndef ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_H__
#define ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_H__

#include "ilang/ila/instr_lvl_abs.h"
#include "ilang/ila/ast/expr.h"

extern "C" {
#include "smtparser/smtlib2abstractparser.h"
#include "smtparser/smtlib2abstractparser_private.h"
}

namespace ilang {
namespace smt2ila {

class Smtlib2Parser;


/// \brief the class for parsing a smt-lib2 expr
/// an instance must be kept alive while using the term
class Smtlib2Parser {

public:
  typedef size_t TermPtrT;
  typedef size_t SortPtrT;
  typedef std::unordered_map<std::string, ExprPtr> symbol_table_t;
  typedef std::unordered_map<std::string, TermPtrT> symbol_pointer_table_t;
  typedef std::vector<symbol_pointer_table_t> symbols_stack_t;
  typedef std::vector<std::string> sort_name_table_t;
  typedef std::unordered_map<std::string, std::pair<SortPtr, size_t> > sort_table_t;

protected:
  InstrLvlAbs & ila_;

  smtlib2_abstract_parser* parser_wrapper;
  // actually we maybe don't need to cache terms

  // quantifier term stack
  symbols_stack_t quantifier_def_stack;
  sort_name_table_t sort_names;
  sort_table_t sort_table;
  std::vector<ExprPtr> term_allocation_table;

  TermPtrT parse_result_term;
  std::string error_msg_;

  SortPtr get_sort(SortPtrT);
  ExprPtr get_term(TermPtrT);

public:
  Smtlib2Parser(InstrLvlAbs & ila_in_);
    
  virtual ~Smtlib2Parser();
  // no copy constructor
  Smtlib2Parser(const Smtlib2Parser&) = delete;
  // no assignment
  Smtlib2Parser& operator=(const Smtlib2Parser&) = delete;
  
  // if unsat --> add the (assert ...)
  ExprPtr ParseSmtFromFile(const std::string& fname);
  // parse from a string: assume we have the (assert ...) there
  ExprPtr ParseSmtFromString(const std::string& text);

  std::string GetParserErrorMessage() const { return error_msg_; }

  // ------------------------------------------------------------------------
  
  // we probably don't need to make sort
  SortPtrT virtual make_bv_sort(uint64_t w);
  SortPtrT virtual make_sort(const std::string& name, const std::vector<int>& idx);
  SortPtrT virtual make_parametric_sort(const std::string& name, const std::vector<SortPtrT>& tpargs);

  void virtual declare_quantified_variable(const std::string& name, SortPtrT sort);

  virtual void * push_quantifier_scope();
  virtual void * pop_quantifier_scope();
  
  ExprPtr search_symbol_table(const std::string& name) const;
  TermPtrT search_quantified_var_stack(const std::string& name) const;

  TermPtrT virtual make_function(const std::string& name, SortPtrT sort,
    const std::vector<int>& idx, const std::vector<TermPtrT>& args );
  
  TermPtrT virtual make_number(const std::string& rep, int width, int base);

  // this function receives the final assert result
  void virtual assert_formula(TermPtrT term);
  // this function receives the final result
  void virtual define_function(const std::string& func_name,
                       const std::vector<TermPtrT> & args,
                       SortPtrT ret_type, TermPtrT func_body);


#define DECLARE_OPERATOR(name)                                                 \
  TermPtrT virtual mk_##name(const std::string& symbol, SortPtrT sort,       \
                        const std::vector<int> & idx,                     \
                        const std::vector<TermPtrT> & args)


  // I hope it will expand lexically
  DECLARE_OPERATOR(true);
  DECLARE_OPERATOR(false);

  DECLARE_OPERATOR(and);
  DECLARE_OPERATOR(or);
  DECLARE_OPERATOR(not);
  DECLARE_OPERATOR(implies);
  DECLARE_OPERATOR(eq);
  DECLARE_OPERATOR(ite);
  DECLARE_OPERATOR(xor);
  DECLARE_OPERATOR(nand);
  DECLARE_OPERATOR(nor);
  DECLARE_OPERATOR(concat);
  DECLARE_OPERATOR(bvnot);
  DECLARE_OPERATOR(bvand);
  DECLARE_OPERATOR(bvnand);
  DECLARE_OPERATOR(bvor);
  DECLARE_OPERATOR(bvnor);
  DECLARE_OPERATOR(bvxor);
  DECLARE_OPERATOR(bvxnor);
  DECLARE_OPERATOR(bvult);
  DECLARE_OPERATOR(bvslt);
  DECLARE_OPERATOR(bvule);
  DECLARE_OPERATOR(bvsle);
  DECLARE_OPERATOR(bvugt);
  DECLARE_OPERATOR(bvsgt);
  DECLARE_OPERATOR(bvuge);
  DECLARE_OPERATOR(bvsge);
  DECLARE_OPERATOR(bvcomp);
  DECLARE_OPERATOR(bvneg);
  DECLARE_OPERATOR(bvadd);
  DECLARE_OPERATOR(bvsub);
  DECLARE_OPERATOR(bvmul);
  DECLARE_OPERATOR(bvudiv);
  DECLARE_OPERATOR(bvsdiv);
  DECLARE_OPERATOR(bvsmod);
  DECLARE_OPERATOR(bvurem);
  DECLARE_OPERATOR(bvsrem);
  DECLARE_OPERATOR(bvshl);
  DECLARE_OPERATOR(bvlshr);
  DECLARE_OPERATOR(bvashr);
  DECLARE_OPERATOR(extract);
  DECLARE_OPERATOR(bit2bool);
  DECLARE_OPERATOR(repeat);
  DECLARE_OPERATOR(zero_extend);
  DECLARE_OPERATOR(sign_extend);
  DECLARE_OPERATOR(rotate_left);
  DECLARE_OPERATOR(rotate_right);

#undef DECLARE_OPERATOR

}; // class Smtlib2Parser

} // namespace smt2ila
} // namespace ilang

#endif // ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_H__
