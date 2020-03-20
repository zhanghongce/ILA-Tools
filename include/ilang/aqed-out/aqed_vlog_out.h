/// \file Header for generating decode for each instruction
// --- Hongce Zhang (hongcez@princeton.edu)

#ifndef ILANG_AQED_OUT_VLOG_OUT_H__
#define ILANG_AQED_OUT_VLOG_OUT_H__

#include <ilang/verilog-out/verilog_gen.h>

namespace ilang {

/// \brief Class of Verilog Decode AQed Generator
class VerilogDecodeForAQedGenerator : public VerilogGeneratorBase {
public:
  // --------------------- TYPE DEFINITIONS ---------------------------- //
  /// let the test class use this module
  friend class TestVerilogExport;
  /// Type of Verilog id names'
  using vlg_name_t = VerilogGeneratorBase::vlg_name_t;
  /// Type of Verilog statement
  using vlg_stmt_t = VerilogGeneratorBase::vlg_stmt_t;
  /// Type of Verilog address
  using vlg_addr_t = VerilogGeneratorBase::vlg_addr_t;
  /// Type of Verilog data
  using vlg_data_t = VerilogGeneratorBase::vlg_data_t;
  /// Type of Verilog statements (a vector)
  using vlg_stmts_t = VerilogGeneratorBase::vlg_stmts_t;
  /// Type of Verilog names (a vector)
  using vlg_names_t = VerilogGeneratorBase::vlg_names_t;
  /// Type of Verilog signal, name & bw
  using vlg_sig_t = VerilogGeneratorBase::vlg_sig_t;
  /// Type of Verilog signals (a vector)
  using vlg_sigs_t = VerilogGeneratorBase::vlg_sigs_t;
  /// Type of a map: name -> need to add keep?
  using vlg_sig_keep_t = VerilogGeneratorBase::vlg_sig_keep_t;
  /// Type of set of Verilog signals
  using vlg_sigs_set_t = VerilogGeneratorBase::vlg_sigs_set_t;
  /// Type of Verilog ITEs (IN sequential block)
  using vlg_ite_stmt_t = VerilogGeneratorBase::vlg_ite_stmt_t;
  /// Type of Verilog ITEs statements
  using vlg_ite_stmts_t = VerilogGeneratorBase::vlg_ite_stmts_t;
  /// Type of the memorys that are going to be created
  using vlg_mem_t = VerilogGeneratorBase::vlg_mem_t;
  /// Type of collection of memorys
  using vlg_mems_rec_t = VerilogGeneratorBase::vlg_mems_rec_t;
  /// This is type of an individual write.
  using mem_write_entry_t = VerilogGeneratorBase::mem_write_entry_t;
  /// This is type of a list of writes.
  using mem_write_entry_list_t = VerilogGeneratorBase::mem_write_entry_list_t;
  /// Type of a stack of writes use in visitMemNodes
  using mem_write_entry_list_stack_t =
      VerilogGeneratorBase::mem_write_entry_list_stack_t;
  /// This is the write and its associated condition.
  using mem_write_t = VerilogGeneratorBase::mem_write_t;
  /// List of writes w. associated conditions.
  using mem_write_list_t = VerilogGeneratorBase::mem_write_list_t;
  /// Type for caching the generated expressions.
  using ExprMap = VerilogGeneratorBase::ExprMap;
  // VerilogGen Configure
  /// the structure to configure the verilog generator
  using VlgGenConfig = VerilogGeneratorBase::VlgGenConfig;
  /// Type of function apply record
  using function_app_t = VerilogGeneratorBase::function_app_t;
  /// Type of func app vector record
  using function_app_vec_t = VerilogGeneratorBase::function_app_vec_t;

protected:
  // --------------------- MEMBERS ---------------------------- //
  vlg_names_t all_decode_signals;

private:
  // --------------------- HELPER FUNCTIONS ---------------------------- //
  /// handle a input variable (memvar/bool/bv)
  void insertInput(const ExprPtr& input);
  /// handle a state variable
  void insertState(const ExprPtr& state);

  // Here we are not using depthfirstSearch as we need to alternate between
  // root-first/root-last traversal
  /// traverse to the subtree, caller: ParseNonMemUpdateExpr
  void parseArg(const ExprPtr& e);
  /// After you parse a subtree, this can help you get the vlg name associated
  /// with it
  VerilogGenerator::vlg_name_t getVlgFromExpr(const ExprPtr& e);
  /// a short cut of calling getVlgFromExpr to find arg's vlg names
  VerilogGenerator::vlg_name_t getArg(const ExprPtr& e, const size_t& i);
  /// called by ParseNonMemUpdateExpr to deal with a boolop node
  vlg_name_t translateBoolOp(const std::shared_ptr<ExprOp>& e);
  /// called by ParseNonMemUpdateExpr to deal with a bvop node
  vlg_name_t translateBvOp(const std::shared_ptr<ExprOp>& e);
  /// travserse an expression, not used as mem-write subtree
  void ParseNonMemUpdateExpr(const ExprPtr& e);

public:
  // --------------------- CONSTRUCTOR ---------------------------- //
  /// \param[in] Configuration
  /// \param[in] Top module name, if empty, get it from instruction name
  /// \param[in] clock signal name
  /// \param[in] reset signal name
  VerilogDecodeForAQedGenerator(const VlgGenConfig& config = VlgGenConfig(),
                   const std::string& modName = "",
                   const std::string& clk = "clk",
                   const std::string& rst = "rst");
  /// Parse an ILA, will gen all its instructions
  void ExportIla(const InstrLvlAbsPtr& ila_ptr_);
  /// add a signel and assumption of the allowed sequences --- any single one is good
  void GenSequenceAssumtionsAny();
  void GenSequenceOneAtATime();
  /// add a signel and assumption of the allowed sequences --- give a bad state and
  /// try enumerate sequence with out reaching that state
  // Not implemented yet
  void GenSequenceAssumtionsNotBadState();
}; // class VerilogDecodeForAQedGenerator

}; // namespace ilang

#endif // ILANG_AQED_OUT_VLOG_OUT_H__