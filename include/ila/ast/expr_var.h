/// \file
/// Header for the class ExprVar

#ifndef __EXPR_VAR_H__
#define __EXPR_VAR_H__

#include "ila/ast/expr.h"
#include <string>

/// \namespace ila
namespace ila {

/// \class ExprVar
/// Expression for variables (bool, bv, or mem). Variable should be the
/// terminating nodes in the AST.
class ExprVar : public Expr {
public:
  // ------------------------- CONSTRUCTOR/DESTRUCTOR ----------------------- //
  /// Default constructor. DO NOT USE.
  ExprVar();
  /// Constructor for Boolean variable.
  ExprVar(const std::string& name);
  /// Constructor for Bitvector variable.
  ExprVar(const std::string& name, const int& bit_width);
  /// Constructor for Memory variable.
  ExprVar(const std::string& name, const int& addr_width,
          const int& data_width);

  /// Default destructor.
  ~ExprVar();

  // ------------------------- ACCESSORS/MUTATORS --------------------------- //
  /// Return the prefix of the variable expression.
  const std::string& prefix() const { return k_prefix_var_; }

  // ------------------------- METHODS -------------------------------------- //
  /// Return true since this is a variable.
  bool IsVar() const { return true; }

  /// Return the z3 expression for the node.
  z3::expr GetZ3Expr(z3::context& z3_ctx, const Z3ExprVec& z3expr_vec,
                     const std::string& suffix) const;

  /// Output to stream.
  std::ostream& Print(std::ostream& out) const;

private:
  // ------------------------- MEMBERS -------------------------------------- //
  /// Static prefix for variable expression.
  static const std::string k_prefix_var_;

  // ------------------------- HELPERS -------------------------------------- //
  /// Print Boolean variable.
  std::ostream& PrintBool(std::ostream& out) const;
  /// Print Bitvector variable.
  std::ostream& PrintBv(std::ostream& out) const;
  /// Print Memory variable.
  std::ostream& PrintMem(std::ostream& out) const;

}; // class ExprVar

} // namespace ila

#endif // __EXPR_VAR_H__