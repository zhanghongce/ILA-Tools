/// \file Header for generating information to support
/// AQED
// --- Hongce Zhang (hongcez@princeton.edu)

#ifndef ILANG_AQED_OUT_AQED_OUT_H__
#define ILANG_AQED_OUT_AQED_OUT_H__

#include <ilang/ila/instr_lvl_abs.h>

namespace ilang {

/// \brief the base class for info generator
/// not intended to be used directly
/// just to hide the implementation details
class AQedInfoGeneratorBase {
public:
  // --------------------- CONSTRUCTOR ---------------------------- //
  AQedInfoGeneratorBase();
  // --------------------- DESTRUCTOR ---------------------------- //
  virtual ~AQedInfoGeneratorBase();
}; // class AQedInfoGeneratorBase

/// \brief Class for generating AQED support information
class AQedInfoGenerator {
  protected:
    // --------------------- MEMBERS  ---------------------------- //
    const InstrLvlAbsPtr& ila_ptr;
  public:
    // --------------------- CONSTRUCTOR ---------------------------- //
    /// \param[in] ILA the pointer to the ila model
    AQedInfoGenerator(const InstrLvlAbsPtr& ila_ptr_);

    // --------------------- MEMBER FUNCTIONS ---------------------------- //
    /// To export the decode functions to a file
    /// \param[in] ILA the pointer to the ila model
    void ExportInstructionAndDecode(const std::string& filename);

}; // class AQedInfoGenerator

}; // namespace ilang


#endif // ILANG_AQED_OUT_AQED_OUT_H__