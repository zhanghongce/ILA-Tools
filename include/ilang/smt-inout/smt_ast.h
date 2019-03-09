/// \file SMT AST
/// used to hold parsed ast
/// --- Hongce Zhang (hongcez@princeton.edu)

#ifndef SMT_AST_H__
#define SMT_AST_H__

#include <string>
#include <vector>
#include <map>
#include <memory>

namespace ilang {

  /// string iterator
  struct str_iterator {
    /// the buffer
    const std::string buf;
    /// the pointer
    unsigned pnt;
    /// constructor 1
    str_iterator(const std::string &, unsigned p = 0);
    /// constructor 2
    str_iterator(const str_iterator &);
    
    // ------------- MEMBER FUNCTIONS ---------------- //
    /// jump to the start of symbol c
    void jump_to_next(const std::string &c);
    /// returns the next non space pos
    unsigned next_non_space_pos(const std::string &s = " \t\n\r") const;
    /// returns the next non space pos
    unsigned next_non_space_pos(const std::string &s, unsigned pos) const;
    /// skip some single charactor symbol
    void skip(const std::string &s = " \t\n\r");
    /// skip a symbol (w. blank also)
    void skip_m(const std::string &s);
    // return true if it is the end
    bool is_end() const;
    // return true if it is the end
    bool is_end(unsigned pos) const;
    /// return the first 
    char head() const;
    /// return the head_word (if it the end, then empty string)
    std::string head_word(const std::string &s = " \t\n\r") const;
    /// expect the head token to be 'c'
    void expect(const std::string &c) const;
    /// get the closest occurance of s from current point
    unsigned next(const std::string & s) const ;
    /// get the closest occurance of s from pos
    unsigned next(const std::string & s, unsigned pos) const ;
    /// accept a token (expect and skip)
    void accept(const std::string &s);
    /// extract from the current location, untill reaching
    /// one of the delimiter, (not checking the current delimiter)
    std::string accept_current_and_read_untill(const std::string & delimiter);
    /// read untill a  pos
    std::string read_till_pos(unsigned pos);
    /// read until the stack is empty
    std::string extract_untill_stack_empty(char push_symbol, char pop_symbol);
    /// read a line, consume all the \n\r but will not include them in the returned string
    std::string readline_no_eol();
    
  }; // struct str_iterator

  struct smt_item {
    /// output to string 
    virtual std::string toString() const = 0;
  }; // struct smt_item
  
  typedef std::shared_ptr<smt_item> smt_item_ptr;
  
  struct line_comment : public smt_item {
    /// the comment
    std::string comment;
    /// output to string 
    virtual std::string toString() const override;
  }; // struct line_comment
  

  /// the type Bool or (_ BitVec)
  struct var_type{
    /// type
    enum tp {Bool, BV, Datatype} _type;
    /// bitwidth
    unsigned _width;
    /// its datatype name (not including | _s|)
    std::string module_name;
    // ------------- FUNCTIONS ---------------- //
    /// contruct from 
    static var_type ParseFromString(str_iterator &); // will update the iterator
    /// convert to string
    std::string ToString() const;
  }; // struct var_type

  /// and item in declare-datatype
  struct state_var_t{
    /// |module_name|...
    std::string internal_name;
    /// module_name
    std::string module_name;
    /// verilog name (not including \)
    std::string verilog_name; 
    /// its type
    var_type    _type;
    // ------------- FUNCTIONS ---------------- //
    /// contruct from 
    static state_var_t ParseFromString(str_iterator &, const std::string & default_module_name); // will update the iterator
  }; // struct state_var_t
  
   // declaration of datatypes
  typedef std::map<std::string, std::vector<state_var_t>> datatypes_t;

  /// argument used in a function def
  struct arg_t{
    /// argument's name
    std::string arg_name;
    /// arg type
    var_type arg_type;
    // ------------- FUNCTIONS ---------------- //
    /// construct from input string
    static arg_t ParseFromString(str_iterator &);
  }; // struct arg_t

  /// a function
  struct func_def_t : public smt_item {
    /// func name
    std::string func_name;
    /// func_module
    std::string func_module;
    /// the initial args text, will be replaced by state_var_vec
    std::string args_text;
    /// arguments
    std::vector<arg_t> args;
    /// its return type
    var_type    ret_type;
    /// its content -- will be replaced
    std::string func_body;
    /// extra comment (optional)
    std::string extra_comment;
    // ------------- MEMBER FUNCTIONS ---------------- //
    /// output to string 
    virtual std::string toString() const override;
    /// parse from file, but will not return but use a reference
    static void ParseFromString(str_iterator &, func_def_t & ); // will update the iterator
  }; // struct func_def_t
  
  /// the class that holds the whole file
  struct smt_file {
    /// collection of smt_items
    std::vector<smt_item_ptr>  items;
    /// the data types include in the smt_file
    datatypes_t datatypes;
    // ------------- MEMBER FUNCTIONS ---------------- //
    /// output to string 
    std::string toString() const;
  }; // struct smt_file

  void ParseFromString(str_iterator & it, datatypes_t & dtype);
  void ParseFromString(str_iterator & it, smt_file & smt);

}; // namespace ilang
  
#endif // SMT_AST_H__

