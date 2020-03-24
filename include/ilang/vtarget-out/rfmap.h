/// \file Header for some data structures
/// used in refinement map
/// in the future, we can choose to 
/// parse refinement into this data structure
/// first as the parsing will be more difficult


#ifndef ILANG_VTARGET_OUT_RFMAP_H__
#define ILANG_VTARGET_OUT_RFMAP_H__

#include <list>
#include <map>
#include <unordered_map>
#include <vector>
#include <string>

#include "nlohmann/json.hpp"

namespace ilang {

namespace refinement {

struct ValueHolder {
    /// the name of the value holder
   std::string name;
   /// the value and condition
   std::vector<std::pair<std::string, std::string>> exprs;
   /// whether to auto determine the width
   bool auto_width;
   /// the width specified
   unsigned width;
   /// Default constructor
   ValueHolder(const std::string &n = "") : name(n), auto_width(false), width(0) {}   
}; // struct ValueHolder

typedef std::vector<ValueHolder> value_holder_list_t;
/// From Json
void CreateValueHolders(nlohmann::json& value_holder_section, value_holder_list_t& l);

struct RefinementVerilogVarmap {
    /// "value-holder" section
    value_holder_list_t value_holders;
    
    /// Default constructor
    RefinementVerilogVarmap() {}
    /// From Json
    RefinementVerilogVarmap(nlohmann::json& rf_vmap);
};

}; // namespace refinement

}; // namespace ilang

#endif // ILANG_VTARGET_OUT_RFMAP_H__
