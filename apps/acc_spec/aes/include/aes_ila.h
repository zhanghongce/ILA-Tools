/// \file the ila example of AES block encryption
///  Hongce Zhang (hongcez@princeton.edu)
///

#ifndef AES_ILA_H__
#define AES_ILA_H__

#include <ilang/cpp_api.h>

using namespace ilang;

/// \brief the class of AES ila
class AES {
  
constexpr AES_START = 0xff00;
constexpr AES_STATE = 0xff01;
constexpr AES_ADDR  = 0xff02;
constexpr AES_LEN   = 0xff04;
constexpr AES_KEY   = 0xff10;
constexpr AES_CNT   = 0xff20;

constexpr CMD_NOP   = 0;
constexpr CMD_READ  = 1;
constexpr CMD_WRITE = 2;

constexpr AES_STATE_IDLE       = 0;
constexpr AES_STATE_READ_DATA  = 1;
constexpr AES_STATE_OPERATE    = 2;
constexpr AES_STATE_WRITE_DATA = 3;

protected:
  // --------------- MEMBERS ----------- //
  /// the ila mode
  Ila model;
public:
  // --------------- CONSTRUCTOR ------ //
  /// add state, add instructions, add child
  AES();

private: 
  /// Called by the constructor to create the child-ILA
  /// for block encryption
  void AES::AddChild(InstrRef & inst)

protected:
  // --------------- HELPERS -------- //
  /// To get a slide from the expression: reg
  /// \param[in] reg: the register to slice
  /// \param[in] idx: the address/index to select the slice
  /// \param[in] base_addr: the address to be substracted from address
  /// \param[in] no_slice: the number of slices
  /// \param[in] slice_width: the width of slice
  /// \return  the resulted read expression
  static ExprRef slice_read(
      const ExprRef & reg, 
      const ExprRef & idx, 
      unsigned long base_addr, 
      unsigned no_slice, 
      unsigned slice_width);

  /// update only part (slices) of a register
  /// \param[in] reg: the register to slice
  /// \param[in] idx: the address/index to select the slice
  /// \param[in] input_slice: the slice used to update
  /// \param[in] base_addr: the address to be substracted from address
  /// \param[in] no_slice: the number of slices
  /// \param[in] slice_width: the width of slice
  /// \return  the resulted read expression
  /// it assumes:
  /// input_slice.width == slice_width
  /// no_slice * slice_width == reg.width
  static ExprRef slice_update(
    const ExprRef & reg, 
    const ExprRef & idx, 
    const ExprRef & input_slice,  
    unsigned long base_addr, 
    unsigned no_slice, 
    unsigned slice_width) ;

  /// specify a nondeterministic value within range [low,high]
  ExprRef unknown_range(unsigned low, unsigned high);
  /// a nondeterministic choice of a or b
  FuncRef AES::unknown_choice(const ExprRef & a, const ExprRef & b);
  /// a nondeterminstic bitvector const of width
  FuncRef AES::unknown(unsigned width);


protected:
  // ------------ STATE ------------ //
  // I/O interface: this is where the commands come from.
  ExprRef cmd     ;
  ExprRef cmdaddr ;
  ExprRef cmddata ;
  // internal arch state.
  ExprRef state   ;
  ExprRef opaddr  ;
  ExprRef oplen   ;
  ExprRef ctr     ;
  ExprRef key     ;
  // the memory
  ExprRef xram    ;
  // The encryption function : 
  // 128b plaintext x 128b key -> 128b ciphertext
  // FuncRef(name, range, domain1, domain2 )
  ExprRef aes128  ; 
  // the output
  ExprRef outdata ;

}; // class AES

#endif // AES_ILA_H__