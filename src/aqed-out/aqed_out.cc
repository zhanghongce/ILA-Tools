/// \file Source for generating information to support
/// AQED
// --- Hongce Zhang (hongcez@princeton.edu)

#include <ilang/util/log.h>
#include <ilang/aqed-out/aqed_out.h>
#include <ilang/aqed-out/aqed_out_impl.h>
// header of implementation is only included in cc,
// not in its header


namespace ilang{

AQedInfoGeneratorBase::AQedInfoGeneratorBase() {} // do nothing
AQedInfoGeneratorBase::~AQedInfoGeneratorBase() {} // do nothing

AQedInfoGenerator::AQedInfoGenerator(const InstrLvlAbsPtr& ila_ptr_) :
    ila_ptr(ila_ptr_) {}


void AQedInfoGenerator::ExportInstructionAndDecode(const std::string& filename) {
    VerilogDecodeForAQedGenerator vdout;
    vdout.ExportIla(ila_ptr);
    vdout.GenSequenceAssumtionsAny();
    vdout.GenSequenceOneAtATime();

    std::ofstream fout(filename);
    ILA_ERROR_IF(!fout.is_open()) << "Unable to write to " << filename;
    vdout.DumpToFile(fout);
}

}; // namespace ilang