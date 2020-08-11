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
 ** \brief SMT-LIB2 callback functions
 **
 ** 
 **/

#ifndef ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_CALLBACK_FN_H__
#define ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_CALLBACK_FN_H__

extern "C" {
#include "smtparser/smtlib2abstractparser.h"
#include "smtparser/smtlib2abstractparser_private.h"
}


namespace ilang {
namespace smt2ila {

//
// -------------- call back function declarations ---------------- //
//
// these are just proxy that forwards calls to the SmtlibInvariantParser
// member functions
// this is just because we can not pass function objects (lambda functions)
// to the legacy C code

// --- for abstract parser
// (forall
smtlib2_term proxy_push_quantifier_scope(smtlib2_parser_interface* p);

// ) ; end of forall
smtlib2_term proxy_pop_quantifier_scope(smtlib2_parser_interface* p);

// the special function dealing with the final term in a forall term
smtlib2_term proxy_make_forall_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term);

// the special function dealing with the final term in an exists term
smtlib2_term proxy_make_exists_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term);

// we will treat everything as an assert, although it does nothing
void proxy_assert_formula(smtlib2_parser_interface* parser, smtlib2_term term);

// in the case of CVC4 output, it will be a define-fun
void proxy_define_func(smtlib2_parser_interface* parser, const char* name,
                       smtlib2_vector* params, smtlib2_sort sort,
                       smtlib2_term term);
//
smtlib2_sort proxy_make_sort(smtlib2_parser_interface* p, const char* sortname,
                             smtlib2_vector* index);

// (Array xx xx)
smtlib2_sort proxy_make_parametric_sort(smtlib2_parser_interface *p,
                                      const char *sortname, smtlib2_vector *tps);
//
void proxy_declare_variable(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort);

void proxy_declare_function(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort);

void proxy_check_sat(smtlib2_parser_interface* p);
// --- for term parser

smtlib2_term proxy_mk_function(smtlib2_context ctx, const char* symbol,
                               smtlib2_sort sort, smtlib2_vector* index,
                               smtlib2_vector* args);

smtlib2_term proxy_mk_number(smtlib2_context ctx, const char* rep,
                             unsigned int width, unsigned int base);
// handle the operators

#define SMT2ILA_DECLHANDLER(name)                                      \
  smtlib2_term smt_mk_##name(smtlib2_context ctx, const char* symbol,   \
                                    smtlib2_sort sort, smtlib2_vector* idx,    \
                                    smtlib2_vector* args)

SMT2ILA_DECLHANDLER(and);
SMT2ILA_DECLHANDLER(or);
SMT2ILA_DECLHANDLER(not);
SMT2ILA_DECLHANDLER(implies);
SMT2ILA_DECLHANDLER(eq);
SMT2ILA_DECLHANDLER(ite);
SMT2ILA_DECLHANDLER(xor);
SMT2ILA_DECLHANDLER(nand);
SMT2ILA_DECLHANDLER(nor);

SMT2ILA_DECLHANDLER(true);
SMT2ILA_DECLHANDLER(false);

SMT2ILA_DECLHANDLER(concat);
SMT2ILA_DECLHANDLER(bvnot);
SMT2ILA_DECLHANDLER(bvand);
SMT2ILA_DECLHANDLER(bvnand);
SMT2ILA_DECLHANDLER(bvor);
SMT2ILA_DECLHANDLER(bvnor);
SMT2ILA_DECLHANDLER(bvxor);
SMT2ILA_DECLHANDLER(bvxnor);
SMT2ILA_DECLHANDLER(bvult);
SMT2ILA_DECLHANDLER(bvslt);
SMT2ILA_DECLHANDLER(bvule);
SMT2ILA_DECLHANDLER(bvsle);
SMT2ILA_DECLHANDLER(bvugt);
SMT2ILA_DECLHANDLER(bvsgt);
SMT2ILA_DECLHANDLER(bvuge);
SMT2ILA_DECLHANDLER(bvsge);
SMT2ILA_DECLHANDLER(bvcomp);
SMT2ILA_DECLHANDLER(bvneg);
SMT2ILA_DECLHANDLER(bvadd);
SMT2ILA_DECLHANDLER(bvsub);
SMT2ILA_DECLHANDLER(bvmul);
SMT2ILA_DECLHANDLER(bvudiv);
SMT2ILA_DECLHANDLER(bvsdiv);
SMT2ILA_DECLHANDLER(bvsmod);
SMT2ILA_DECLHANDLER(bvurem);
SMT2ILA_DECLHANDLER(bvsrem);
SMT2ILA_DECLHANDLER(bvshl);
SMT2ILA_DECLHANDLER(bvlshr);
SMT2ILA_DECLHANDLER(bvashr);
SMT2ILA_DECLHANDLER(extract);
SMT2ILA_DECLHANDLER(bit2bool);
SMT2ILA_DECLHANDLER(repeat);
SMT2ILA_DECLHANDLER(zero_extend);
SMT2ILA_DECLHANDLER(sign_extend);
SMT2ILA_DECLHANDLER(rotate_left);
SMT2ILA_DECLHANDLER(rotate_right);

#undef SMT2ILA_DECLHANDLER
} // namespace smt2ila
} // namespace ilang

#endif // ILANG_SMTINOUT_SMT2ILA_SMTLIB2PARSER_CALLBACK_FN_H__
