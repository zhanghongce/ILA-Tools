/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SMT-LIB2 callback functions
 **
 ** 
 **/
 
#include <ilang/smt-inout/smt-to-ila/smtlib2parser.h>
#include <ilang/smt-inout/smt-to-ila/smtlib2parser_callback_fn.h>

#include <ilang/util/log.h>

#include <vector>

namespace ilang {
namespace smt2ila {

typedef Smtlib2Parser::TermPtrT TermPtrT;
typedef Smtlib2Parser::SortPtrT SortPtrT;

// make vector
template <class T> std::vector<T> make_vector(smtlib2_vector* iv) {
  std::vector<T> ret;
  if (!iv)
    return ret;

  auto l = SMTLIB2_VECTOR_SIZE(iv);
  intptr_t* ptr = SMTLIB2_VECTOR_ARRAY(iv);
  for (decltype(l) idx = 0; idx < l; ++idx)
    ret.push_back((T)(ptr[idx]));
  return ret;
}

// ------------------ CALL BACK FUNCTIONS ------------- //

#define PARSER(x) ((Smtlib2Parser *)(((smtlib2_abstract_parser*)x)->termparser_->ctx_))

smtlib2_term proxy_push_quantifier_scope(smtlib2_parser_interface* p) {
  return (smtlib2_term)(PARSER(p)->push_quantifier_scope());
}

smtlib2_term proxy_pop_quantifier_scope(smtlib2_parser_interface* p) {
  return (smtlib2_term)(PARSER(p)->pop_quantifier_scope());
}

// we will treat everything as an assert, although it does nothing
void proxy_assert_formula(smtlib2_parser_interface* parser, smtlib2_term term) {
  // here it should be where we get our result
  PARSER(parser)->assert_formula((TermPtrT) term);
}

void proxy_define_func(smtlib2_parser_interface* parser, const char* name,
                       smtlib2_vector* params, smtlib2_sort sort,
                       smtlib2_term term) {

  auto idxv = make_vector<size_t>(params);
  PARSER(parser)->define_function(name, idxv, (SortPtrT) sort, (TermPtrT) term );
  // check the idxv (params) type
}

// the special function dealing with the final term in a forall term
smtlib2_term proxy_make_forall_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term) {
  ILA_CHECK(false) << ("forall in smt-lib2 parsing is not supported yet.");
  return term;
}

// the special function dealing with the final term in an exists term
smtlib2_term proxy_make_exists_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term) {
  ILA_CHECK(false) << ("exists in smt-lib2 parsing is not supported yet.");
  return term;
}

/*

a_sort :
  SYMBOL
  {
      $$ = parser->make_sort(parser, $1, NULL);
      free($1);
  }
| '(' TK_UNDERSCORE SYMBOL int_list ')'
  {
      $$ = parser->make_sort(parser, $3, $4);
      smtlib2_vector_delete($4);
      free($3);
  }
| '(' SYMBOL sort_list ')'
  {
      $$ = parser->make_parametric_sort(parser, $2, $3);
      smtlib2_vector_delete($3);
      free($2);
  }
;

*/

smtlib2_sort proxy_make_sort(smtlib2_parser_interface* p, const char* sortname,
                             smtlib2_vector* index) {
  auto idxv = make_vector<int>(index);
  smtlib2_sort ret =
      (smtlib2_sort)(PARSER(p)->make_sort(sortname, idxv));
  return ret;
  // free((void *)sortname);
  // if(index)
  //   smtlib2_vector_delete(index);
  // free the content?
}

smtlib2_sort proxy_make_parametric_sort(smtlib2_parser_interface *p,
                                      const char *sortname, smtlib2_vector *tps) {

  auto tpargs = make_vector<SortPtrT>(tps);
  smtlib2_sort ret =
      (smtlib2_sort)(PARSER(p)->make_parametric_sort(sortname, tpargs));
  return ret;
}

void proxy_declare_variable(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort) {
  PARSER(p)->declare_quantified_variable(name, (SortPtrT)sort);
  // free((void *)name);
}

void proxy_declare_function(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort) {
  ILA_CHECK(false) << ("declare-fun in smt-lib2 parsing is not supported yet.");
}

void proxy_check_sat(smtlib2_parser_interface* p) {
  // do nothing
}

smtlib2_term proxy_mk_function(smtlib2_context ctx, const char* symbol,
                               smtlib2_sort sort, smtlib2_vector* index,
                               smtlib2_vector* args) {
  auto idxv = make_vector<int>(index);
  auto argsv = make_vector<TermPtrT>(args);

  smtlib2_term ret = (smtlib2_term)(
      ((Smtlib2Parser*)ctx)->make_function(symbol, (SortPtrT)sort, idxv, argsv));
  // free(symbol);
  // if(index)
  //   smtlib2_vector_delete(index);
  // if(args)
  //   smtlib2_vector_delete(args);
  return ret;
}

smtlib2_term proxy_mk_number(smtlib2_context ctx, const char* rep,
                             unsigned int width, unsigned int base) {
  smtlib2_term ret =
      (smtlib2_term)( (smtlib2_term)(((Smtlib2Parser*)ctx)->make_number(rep, width, base)));
  // free(rep);
  return ret;
}

// ------------------ OPERATORS ------------- //

#define SMT2ILA_DEFHANDLER(name)                                       \
  smtlib2_term smt_mk_##name(smtlib2_context ctx, const char* symbol,   \
                                    smtlib2_sort sort, smtlib2_vector* idx,    \
                                    smtlib2_vector* args) {                    \
    auto idxv = make_vector<int>(idx);                                         \
    auto argsv = make_vector<TermPtrT>(args);                         \
    smtlib2_term ret = (smtlib2_term)(                                         \
        ((Smtlib2Parser*)ctx)->mk_##name(symbol, (SortPtrT)sort, idxv, argsv));    \
    return ret;                                                                \
  }

// handle the operators
SMT2ILA_DEFHANDLER(true);
SMT2ILA_DEFHANDLER(false);

SMT2ILA_DEFHANDLER(and);
SMT2ILA_DEFHANDLER(or);
SMT2ILA_DEFHANDLER(not);
SMT2ILA_DEFHANDLER(implies);
SMT2ILA_DEFHANDLER(eq);
SMT2ILA_DEFHANDLER(ite);
SMT2ILA_DEFHANDLER(xor);
SMT2ILA_DEFHANDLER(nand);
SMT2ILA_DEFHANDLER(nor);
SMT2ILA_DEFHANDLER(concat);
SMT2ILA_DEFHANDLER(bvnot);
SMT2ILA_DEFHANDLER(bvand);
SMT2ILA_DEFHANDLER(bvnand);
SMT2ILA_DEFHANDLER(bvor);
SMT2ILA_DEFHANDLER(bvnor);
SMT2ILA_DEFHANDLER(bvxor);
SMT2ILA_DEFHANDLER(bvxnor);
SMT2ILA_DEFHANDLER(bvult);
SMT2ILA_DEFHANDLER(bvslt);
SMT2ILA_DEFHANDLER(bvule);
SMT2ILA_DEFHANDLER(bvsle);
SMT2ILA_DEFHANDLER(bvugt);
SMT2ILA_DEFHANDLER(bvsgt);
SMT2ILA_DEFHANDLER(bvuge);
SMT2ILA_DEFHANDLER(bvsge);
SMT2ILA_DEFHANDLER(bvcomp);
SMT2ILA_DEFHANDLER(bvneg);
SMT2ILA_DEFHANDLER(bvadd);
SMT2ILA_DEFHANDLER(bvsub);
SMT2ILA_DEFHANDLER(bvmul);
SMT2ILA_DEFHANDLER(bvudiv);
SMT2ILA_DEFHANDLER(bvsdiv);
SMT2ILA_DEFHANDLER(bvsmod);
SMT2ILA_DEFHANDLER(bvurem);
SMT2ILA_DEFHANDLER(bvsrem);
SMT2ILA_DEFHANDLER(bvshl);
SMT2ILA_DEFHANDLER(bvlshr);
SMT2ILA_DEFHANDLER(bvashr);
SMT2ILA_DEFHANDLER(extract);
SMT2ILA_DEFHANDLER(bit2bool);
SMT2ILA_DEFHANDLER(repeat);
SMT2ILA_DEFHANDLER(zero_extend);
SMT2ILA_DEFHANDLER(sign_extend);
SMT2ILA_DEFHANDLER(rotate_left);
SMT2ILA_DEFHANDLER(rotate_right);

#undef SMT2ILA_DEFHANDLER

} // namespace smt2ila
} // namespace cosa


