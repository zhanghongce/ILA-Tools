/// \file Header for generating information to support
/// AQED --- the implementation, not to be exposed
// --- Hongce Zhang (hongcez@princeton.edu)

#ifndef ILANG_AQED_OUT_AQED_OUT_IMPL_H__
#define ILANG_AQED_OUT_AQED_OUT_IMPL_H__

#include "nlohmann/json.hpp"

#include <ilang/aqed-out/aqed_out.h>
#include <ilang/aqed-out/aqed_vlog_out.h>
#include <ilang/verilog-in/verilog_analysis_wrapper.h>
#include <ilang/vtarget-out/var_extract.h>

namespace ilang {


/// \brief the base class for info generator
/// will use a lot of other headers like
/// the verilog parser
class AQedInfoGeneratorImpl : public AQedInfoGeneratorBase {
protected:
  /// A pointer to create verilog analyzer
  VerilogInfo* vlg_info_ptr; // in case we want to share it
  /// store the vmap info
  nlohmann::json rf_vmap;
  /// store the condition
  nlohmann::json rf_cond;

public:
  // --------------------- CONSTRUCTOR ---------------------------- //
  AQedInfoGeneratorImpl(
    const std::vector<std::string>& implementation_include_path,
    const std::vector<std::string>& implementation_srcs,
    const std::string& implementation_top_module,
    const std::string& refinement_variable_mapping,
    const std::string& refinement_conditions
  );
  // --------------------- DESTRUCTOR ---------------------------- //
  virtual ~AQedInfoGeneratorImpl();
  /// Return true if it is in bad state
  bool in_bad_state(void) const { return _bad_state; }

protected:
  /// If it is bad state, return true and display a message
  bool bad_state_return(void);
  /// load json from a file name to the given j
  void load_json(const std::string& fname, nlohmann::json& j);

private:
  /// If it is in a bad state
  bool _bad_state;
  
}; // // 

}; // namespace ilang

#endif // ILANG_AQED_OUT_AQED_OUT_IMPL_H__