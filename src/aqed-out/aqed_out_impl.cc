/// \file Source for generating information to support
/// AQED -- implementation
// --- Hongce Zhang (hongcez@princeton.edu)

#include <ilang/util/log.h>
#include <ilang/aqed-out/aqed_out_impl.h>

namespace ilang {

AQedInfoGeneratorImpl::AQedInfoGeneratorImpl(
    const std::vector<std::string>& implementation_include_path,
    const std::vector<std::string>& implementation_srcs,
    const std::string& implementation_top_module,
    const std::string& refinement_variable_mapping,
    const std::string& refinement_conditions
  ): AQedInfoGeneratorBase(),
      _ila_ptr(ila_ptr), vlg_info_ptr(NULL)
      _bad_state(false) {

  load_json(_rf_var_map_name, rf_vmap);
  supplementary_info.FromJson(rf_vmap);
  load_json(_rf_cond_name, rf_cond);
  set_module_instantiation_name();
  
  if (_ila_ptr == nullptr) {
    ILA_ERROR << "ILA should not be none";
    _bad_state = true;
  }

} // AQedInfoGeneratorImpl

AQedInfoGeneratorImpl::~AQedInfoGeneratorImpl() {
  if (vlg_info_ptr)
    delete vlg_info_ptr;
}




} // namespace ilang
