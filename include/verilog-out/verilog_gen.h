/// \file
/// Header for generating Verilog files
/// Currently not supported 
///  1. Load(Store) / Load(ITE) / Load(MemConst) or their combination
///  2. Function on memory
///
/// For 0-ary func, they will be treated as nondet
/// apply the same nondet func twice, will generate two variables
/// if you do want to share the nondet val, please reuse the sub-tree
///

#ifndef VERILOG_GEN_H__
#define VERILOG_GEN_H__

#include "ila/expr_fuse.h"
#include "z3++.h"
#include <map>
#include <unordered_map>
#include <vector>

/// \namespace ila
namespace ila {

  typedef ExprHash VerilogGenHash;


  /// \brief Class of Verilog Generator
  class VerilogGenerator
  { 
    // --------------------- TYPE DEFINITIONS ---------------------------- //
    /// Type of Verilog id names
    typedef std::string                 vlg_name_t;
    /// Type of Verilog statement
    typedef std::string                 vlg_stmt_t;
    /// Type of Verilog address
    typedef std::string                 vlg_addr_t;
    /// Type of Verilog data
    typedef std::string                 vlg_data_t;
    /// Type of Verilog statements (a vector)
    typedef std::vector<vlg_name_t>     vlg_stmts_t;
    /// Type of Verilog names (a vector)
    typedef std::vector<vlg_name_t>     vlg_names_t;
    /// Type of Verilog signal, name & bw
    typedef std::pair<vlg_name_t,int>   vlg_sig_t;
    /// Type of Verilog signals (a vector)
    typedef std::vector<vlg_sig_t>      vlg_sigs_t;
    /// Type of set of Verilog signals
    typedef std::set<vlg_sig_t>         vlg_sigs_set_t;
    /// Type of Verilog ITEs (IN sequential block)
    typedef std::tuple<vlg_stmt_t,vlg_stmt_t,vlg_stmt_t>  vlg_ite_stmt_t;
    /// Type of Verilog ITEs statements
    typedef std::vector<vlg_ite_stmt_t>             vlg_ite_stmts_t;
    /// Type of the memorys that are going to be created
    typedef std::tuple<vlg_name_t,int,int>          vlg_mem_t; // name addr_width data_width
    /// Type of collection of memorys
    typedef std::map< vlg_name_t, vlg_mem_t>        vlg_mems_rec_t;
    /// This is type of an individual write.
    struct mem_write_entry_t
    {
      ExprPtr addr;
      ExprPtr data;
    };
    /// This is type of a list of writes.
    typedef std::list<mem_write_entry_t> mem_write_entry_list_t;
    /// Type of a stack of writes use in visitMemNodes
    typedef std::list<mem_write_entry_list_t> mem_write_entry_list_stack_t;
    /// This is the write and its associated condition.
    struct mem_write_t 
    {
      ExprPtr cond;
      mem_write_entry_list_t writes;
    };
    /// List of writes w. associated conditions.
    typedef std::list<mem_write_t> mem_write_list_t;
    // VerilogGen Configure
    struct VlgGenConfig{
      bool extMem;   // whether to export as a verilog array or an interface to operate external memory
      enum funcOption { Internal, External } fcOpt;
      VlgGenConfig( // provide the default settings
        bool ExternalMem = false,
        funcOption funcOpt = funcOption::Internal ) : 
          extMem(ExternalMem), 
          fcOpt(funcOpt)
      {}
    };


    /// Type for caching the generated expressions.
    typedef std::unordered_map<const ExprPtr, vlg_name_t, VerilogGenHash> ExprMap;


    // --------------------- HELPER for DEBUG PURPOSE ---------------------------- //
    friend std::ostream& operator<<(
      std::ostream& out, const mem_write_entry_t& mwe);
    friend std::ostream& operator<<(
      std::ostream& out, const mem_write_entry_list_t& mwel);
    friend std::ostream& operator<<(
      std::ostream& out, const mem_write_entry_list_stack_t& mwel);        
    friend std::ostream& operator<<(
      std::ostream& out, const mem_write_t& mw);
    friend std::ostream& operator<<(
      std::ostream& out, const mem_write_list_t& mwl);

    // --------------------- MEMBERS ---------------------------- //
  private:
    // --------------------- Verilog  related ---------------------------- //
    /// Verilog Module Name
    vlg_name_t moduleName;
    /// Clock signal name
    vlg_name_t clkName;
    /// Reset signal name
    vlg_name_t rstName;
    /// Output signals that allows to determine if an instruction's decode is true,  not need for width
    vlg_names_t decodeNames;
    /// Output signals that allows to determine if an instruction's valid is true, not need for width
    vlg_name_t  validName;
    /// vector of input signals
    vlg_sigs_t inputs; 
    /// vector of output signals
    vlg_sigs_t outputs;
    /// vector of memory input signals
    vlg_sigs_t mem_i;
    /// vector of memory output signals
    vlg_sigs_t mem_o;
    /// vector of wires to be defined
    vlg_sigs_t wires;
    /// vector of regs to be defined
    vlg_sigs_t regs;
    /// vector of mems to be defined
    vlg_mems_rec_t mems_internal;
    /// vector of mems from outside (will not be defined)
    vlg_mems_rec_t mems_external;
    /// statements to be used when reset, for initial conditions, it will try to translate, but won't guarantee
    vlg_stmts_t init_stmts;
    /// The other part will be put into SVA assumptions, and the module will have a sparate counter to enforce the assumptions
    vlg_stmts_t init_assumpts;
    /// statements to be outside the always block
    vlg_stmts_t statements;
    /// statements to be used in the always block but out of the reset
    vlg_stmts_t always_stmts;
    /// statements to be used in the always block but out of the reset with ITE conditions
    vlg_ite_stmts_t ite_stmts; // this stmt is only used in sequential always block
    /// For auxiliary definitions
    vlg_stmt_t  preheader; 
    /// The map to cache the expression (we only need to store the name)
    ExprMap nmap;

    /// For traverse a mem expression
    mem_write_list_t current_writes;
    /// For traverse a mem expression, hold a pointer to the writes, so they will not be destroyed before used 
    mem_write_list_t past_writes; 

    /// to hold all valid names, a sanity check
    vlg_sigs_set_t all_valid_names;

    // --------------------- HELPER FUNCTIONS ---------------------------- //
    /// Check if a name is reserved (clk/rst/modulename/decodeName/ctrName)
    bool check_reserved_name(const vlg_name_t & n) const;
    /// Get the width of an ExprPtr, must be supported sort
    int static get_width(const ExprPtr &n) const;
    /// convert a widith to a verilog string
    std::string static WidthToRange(int w) const;
    /// get a new id
    vlg_name_t new_id();
    /// if the exprptr contains some meaning in its name, will try to incorporate that to the name;
    vlg_name_t new_id(const ExprPtr & e); 

    /// The id counter
    unsigned idCounter;
    /// The configuration
    const VlgGenConfig cfg_;
    /// reference name list
    std::map<std::string, std::string> reference_name_set;
    /// Set of functions that need to be translated, we will collect this while translating the exprs
    std::set<FuncPtr> func_ptr_set;

    // --------------------- HELPER FUNCTIONS ---------------------------- //
    /// record an input signal 
    void add_input  (const vlg_name_t & n,int w);
    /// record an output signal 
    void add_output (const vlg_name_t & n,int w);
    /// record a wire
    void add_wire   (const vlg_name_t & n,int w);
    /// record a register
    void add_reg    (const vlg_name_t & n,int w);
    /// record a stmt (outside the always block)
    void add_stmt   (const vlg_stmt_t & s);
    /// record an assignment stmt (outside the always block), will call add_stmt
    void add_assign_stmt (const vlg_name_t & l, const vlg_name_t & r);
    /// record an assignment in the always block (after the reset, in the else branch, guarded by the valid condition )
    void add_always_stmt (const vlg_stmt_t & s);
    /// record an assignemnt in the always block (in if(rst) branch )
    void add_init_stmt   (const vlg_stmt_t & s);
    /// record an ite assignment, (after the reset, in the else branch, guarded by the valid condition ), (if fstmt == "", will not generate its else block)
    void add_ite_stmt    (const vlg_stmt_t & cond, const vlg_stmt_t & tstmt, const vlg_stmt_t & fstmt);
    /// record an internal memory 
    void add_internal_mem(const vlg_name_t &mem_name, int addr_width,int data_width);
    /// record an external memory
    void add_external_mem(const vlg_name_t &mem_name, int addr_width,int data_width);

    /// handle a input variable (memvar/bool/bv)
    void insertInput( const ExprPtr & input );
    /// handle a state variable 
    void insertState( const ExprPtr & state );

    // Here we are not using depthfirstSearch as we need to alternate between root-first/root-last traversal
    /// traverse to the subtree, caller: ParseNonMemUpdateExpr
    void parseArg(const ExprPtr & e);
    /// After you parse a subtree, this can help you get the vlg name associated with it
    void getVlgFromExpr(const ExprPtr & e);
    /// a short cut of calling getVlgFromExpr to find arg's vlg names
    void getArg(const ExprPtr & e, const size_t & i );
    /// Handle function application , Caller: translateBoolOp, translateBvOp
    vlg_name_t translateApplyFunc( std::shared_ptr<ExprOpAppFunc> func_app_ptr_ );
    /// called by ParseNonMemUpdateExpr to deal with a boolop node
    vlg_name_t translateBoolOp( const ExprOp & e );
    /// called by ParseNonMemUpdateExpr to deal with a bvop node
    vlg_name_t translateBvOp( const ExprOp & e );
    /// travserse an expression, not used as mem-write subtree
    void ParseNonMemUpdateExpr( const ExprPtr & e );
    /// check if a mem-write subtree is what we can handle right now
    bool CheckMemUpdateNode( const ExprPtr & e , const std::string & mem_var_name );
    /// traverse the memory-write subtree of "e", its upper level has the condition "cond"
    void VisitMemNodes( const ExprPtr & e, const ExprPtr & cond, mem_write_entry_list_stack_t& writesStack );

    /// add signals & stmts for an internal counter to trace start (more not be useful)
    void addInternalCounter( vlg_name_t decode_sig_name , size_t width = 8 );
    /// use: func_ptr_set ;  affect: prehear, only export if func is internal 
    void ExportFuncDefs();

    /// generate the signals to write a memory (external/internal)
    void ExportCondWrites(const ExprPtr &mem_var, const mem_write_list_t & writeList);
    /// parse an expr used as the memory update, will affect: past_writes & current_writes
    void ParseMemUpdateNode( const ExprPtr & e , const std::string & mem_var_name);

  public:
    // --------------------- CONSTRUCTOR ---------------------------- //
    VerilogGenerator(
      const std::string &modName = "",
      const std::string &clk = "clk",
      const std::string &rst = "rst", 
      const VlgGenConfig & config = VlgGenConfig());
    /// Parse an ILA, will gen all its instructions
    void ExportIla( const InstrLvlAbsPtr & ila_ptr_ );
    /// Parse an instruction
    void ExportTopLevelInstr( const InstrPtr & instr_ptr_ );
    /// after parsing either the Instruction/ILA, use this function to dump to a file.
    void DumpToFile(ostream & fout) const;
  }; // class VerilogGenerator

}; // namespace ila

#endif // VERILOG_GEN_H__
