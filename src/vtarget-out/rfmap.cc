/// \file Header for some data structures
/// used in refinement map
/// in the future, we can choose to 
/// parse refinement into this data structure
/// first as the parsing will be more difficult


#include <ilang/vtarget-out/rfmap.h>

#include <ilang/util/container_shortcut.h>
#include <ilang/util/log.h>
#include <ilang/util/str_util.h>

namespace ilang {

namespace refinement {

void CreateValueHolders(nlohmann::json& value_holder_section, value_holder_list_t& l) {

  if (!IN("post-value-holder", value_holder_section) && !IN("value-holder", value_holder_section))
    return; // no need for it
  ILA_WARN_IF(IN("post-value-holder", value_holder_section))
      << "The name `post-value-holder` will be deprecated in the future, "
      << "please use `value-holder` instead";
  auto& post_val_rec = IN("value-holder", value_holder_section)
                           ? value_holder_section["value-holder"]
                           : value_holder_section["post-value-holder"];
  if (!post_val_rec.is_object()) {
    ILA_ERROR << "Expect (post-)value-holder to be map-type";
    return;
  }
  for (auto&& item : post_val_rec.items()) {
    const auto& pv_name = item.key();
    auto& pv_cond_val = item.value();
    ILA_ERROR_IF(!(pv_cond_val.is_array() || pv_cond_val.is_object()))
        << "Expecting (post-)value-holder's content to be list or map type";

    l.push_back(ValueHolder(pv_name));
    ValueHolder &vh = l.back();

    if (pv_cond_val.is_array() &&
        (!pv_cond_val.empty() &&
         (pv_cond_val.begin()->is_object()))) { // multiple condition
      std::string cond = "1'b1";
      std::string val = "'hx";
      int width = 0;
      bool autodet = false;
      for (auto ptr = pv_cond_val.begin(); ptr != pv_cond_val.end(); ++ptr) {
        ILA_ERROR_IF(!ptr->is_object()) << "requiring each element in the array of  "
          << pv_name << "to be a map";
        for (auto&& cond_val_pair : ptr->items()) {
          if (cond_val_pair.key() == "cond")
             cond = cond_val_pair.value();
          else if (cond_val_pair.key() == "val")
              val = cond_val_pair.value();
          else if (cond_val_pair.key() == "width") {
            if (cond_val_pair.value().is_string()) {
              ILA_CHECK(cond_val_pair.value().get<std::string>() == "auto")
                  << "Expecting width to be unsigned int / auto";
              autodet = true;
            } else {
              ILA_ERROR_IF(width != 0) << "overwriting width for value-holder: " << pv_name;
              width = cond_val_pair.value().get<int>();
              ILA_ERROR_IF(width <= 0) << "width cannot <= 0";
            }
          }
        } // for val/cond/width
        ILA_ERROR_IF(S_IN('@',val) || S_IN('@',cond))
          << "val and cond for value-holder should be `@`-free";
        vh.exprs.push_back(std::make_pair(val, cond));
      } // end of each val-cond-pair
      ILA_WARN_IF(width == 0 && !autodet) << "Will auto-determine width for  value-holder: " << pv_name;
      vh.auto_width = (width == 0 || autodet);
      vh.width = width;
    } else { // it is just a single line
      std::string cond = "1'b1";
      std::string val = "'hx";
      int width = 0;
      bool autodet = false;
      for (auto&& cond_val_pair : pv_cond_val.items()) {
        if (cond_val_pair.key() == "cond")
           cond = cond_val_pair.value();
        else if (cond_val_pair.key() == "val")
            val = cond_val_pair.value();
        else if (cond_val_pair.key() == "width") {
          if (cond_val_pair.value().is_string()) {
            ILA_CHECK(cond_val_pair.value().get<std::string>() == "auto")
                << "Expecting width to be unsigned int / auto";
            autodet = true;
          } else {
            ILA_ERROR_IF(width != 0) << "overwriting width for value-holder: " << pv_name;
            width = cond_val_pair.value().get<int>();
            ILA_ERROR_IF(width <= 0) << "width cannot <= 0";
          }
        } else
          ILA_ERROR << "Unexpected key: " << cond_val_pair.key()
                    << " in post-value-holder, expecting cond/val/width";
      } // for val/cond/width
      ILA_ERROR_IF(S_IN('@',val) || S_IN('@',cond))
        << "val and cond for value-holder should be `@`-free";
      vh.exprs.push_back(std::make_pair(val, cond));
      ILA_WARN_IF(width == 0 && !autodet) << "Will auto-determine width for  value-holder: " << pv_name;
      vh.auto_width = (width == 0 || autodet);
      vh.width = width;
    } // if-else
  } // for item

} // CreateValueHolders


RefinementVerilogVarmap::RefinementVerilogVarmap(nlohmann::json& rf_vmap) {
  CreateValueHolders(rf_vmap, value_holders);
}


}; // namespace refinement

}; // namespace ilang
