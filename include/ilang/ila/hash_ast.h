/// \file
/// Header for the class ExprMngr and the corresponding hash

#ifndef ILANG_ILA_HASH_AST_H__
#define ILANG_ILA_HASH_AST_H__

#include <unordered_map>

#include <ilang/ila/expr_fuse.h>

/// \namespace ilang
namespace ilang {

class ExprMngrNodeHash {
public:
  size_t operator()(const ExprPtr &) const;
};

/// Node Equal Function: decides whether two nodes are equal if they have
/// the same hash (conflicts)
class ExprMngrNodeEqual {
public:
  bool operator()(const ExprPtr &, const ExprPtr &) const;
};

/// \brief Simplifier for AST trees by sharing nodes based on the hash value.
class ExprMngr {
  friend class ExprMngrNodeHash;
  friend class ExprMngrNodeEqual;
public:
  // ------------------------- CONSTRUCTOR/DESTRUCTOR ----------------------- //
  /// Default constructor.
  ExprMngr();
  /// Default destructor.
  ~ExprMngr();

  /// Pointer type for passing shared ast simplifier.
  typedef std::shared_ptr<ExprMngr> ExprMngrPtr;

  // ------------------------- HELPERS -------------------------------------- //
  /// \brief Create an object and return the pointer. Used for hiding
  /// implementation specific types.
  static ExprMngrPtr New();

  // ------------------------- ACCESSORS/MUTATORS --------------------------- //
  /// Reset the hash table
  void clear();

  // ------------------------- METHODS -------------------------------------- //
  /// Return the AST node representative.
  ExprPtr GetRep(const ExprPtr& node);
  /// Function object for sharing ast nodes.
  void operator()(const ExprPtr& node);

private:

  // ------------------------- HELPER FUNCTIONS ----------------------------- //
  /// Hash function.
  static size_t Hash(const ExprPtr& node);

  /// Type for cacheing the AST node hashing.
  typedef std::unordered_set<ExprPtr, ExprMngrNodeHash, ExprMngrNodeEqual> HashTable;

  // ------------------------- MEMBERS -------------------------------------- //
  /// The map for AST nodes.
  HashTable map_;

}; // class ExprMngr

/// Pointer type for passing shared ast simplifier.
typedef ExprMngr::ExprMngrPtr ExprMngrPtr;

} // namespace ilang

#endif // ILANG_ILA_HASH_AST_H__
