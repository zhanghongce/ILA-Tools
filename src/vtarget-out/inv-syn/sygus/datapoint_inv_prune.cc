/// \file Invariant Pruner for SyGuS 
/// for sygus datapoint approach
// Hongce Zhang

#include <ilang/util/str_util.h>
#include <ilang/util/container_shortcut.h>
#include <ilang/util/log.h>

#include <ilang/vtarget-out/inv-syn/sygus/datapoint_inv_prune.h>

#include "z3++.h"

namespace ilang {

/// initially, you need to give the invariant and also the datapoint
DatapointInvariantPruner::DatapointInvariantPruner(InvariantObject & _invs, const TraceDataPoints & _dpts) :
  invs(_invs), dpts(_dpts)
{
  // do nothing
}
/// to prune using the last frame of pos example
void DatapointInvariantPruner::PruneByLastFramePosEx(const smt::YosysSmtParser & design_info,
    std::vector<std::string> var_name_vec,
    const std::map<std::string,int> & additional_width_info ) {

  if (dpts.pos_ex.empty()) {
    ILA_ERROR << "No positive example to use.";
    return;
  }
  ILA_INFO_IF(invs.NumInvariant() == 0) << "No invariant to prune.";

  const auto & var_idx = design_info.get_var_idx();
  auto & last_frame = dpts.pos_ex.back();

  // create (assert INV(#b.. #b..))
  std::vector<std::string> frame_vals;
  for (const auto & vname : var_name_vec ) {
    ILA_ASSERT(IN(vname, last_frame)) << vname << " is not in the datapoint frame!";
    
    smt::var_type tp;
    if (IN(vname,var_idx)) {
      tp = var_idx.at(vname)->_type;
    } else if (IN(vname,additional_width_info)) {
      tp._type = tp.BV;
      tp._width = additional_width_info.at(vname);
    } else
      ILA_ASSERT(false) << "statename:" << vname << " not found in design's smt / additional info!";
   
    auto width = tp._width;

    if (tp.is_bool())
      frame_vals.push_back( last_frame.at(vname).first.val == "0" ? "false" : "true"  );
    else
      frame_vals.push_back( smt::convert_to_binary(last_frame.at(vname).first.val,
        last_frame.at(vname).first.radix, width));
  }
  auto assertion = "(assert (INV " + Join(frame_vals, " ") + "))";

  std::vector<unsigned> prune_num;
  unsigned idx = 0;
  for(auto && smt_string : invs.GetSmtFormulae() ) {
    if (smt_string.empty()) { idx++; continue;}
    z3::context c;
    z3::solver s(c);
    auto check = smt_string + "\n" + assertion;
    s.from_string(check.c_str());
    auto res = s.check();
    if (res == z3::unsat) {
      // cannot make it true
      // prune this
      prune_num.push_back(idx);
    }
    idx ++;
  } // iterate over assertions

  ILA_INFO << "prune: " << prune_num.size() << "/" << invs.NumInvariant() ;

  unsigned removed_no = 0;
  for(auto ri : prune_num) {
    invs.RemoveInvByIdx(ri-removed_no);
    removed_no ++;
  }
}


}; // namespace ilang