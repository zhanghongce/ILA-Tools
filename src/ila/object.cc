/// \file
/// Source for the class Object.

#include "ila/object.h"

/// \namespace ila
namespace ila {

Object::Object() {}

Object::Object(const std::string& name) : symbol_(name) {}

Object::~Object() {}

const Symbol& Object::Name() const { return symbol_; }

ObjType Object::GetObjType() const { return ObjType::OBJ_NONE; }

} // namespace ila
