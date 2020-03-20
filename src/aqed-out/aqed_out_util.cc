/// \file Utility for generating information to support
/// AQED -- implementation
// --- Hongce Zhang (hongcez@princeton.edu)

#include <ilang/util/log.h>
#include <ilang/aqed-out/aqed_out_impl.h>

namespace ilang {


bool AQedInfoGeneratorImpl::bad_state_return(void) {
  ILA_ERROR_IF(_bad_state)
      << "VlgVerifTgtGen is in a bad state, cannot proceed.";
  return _bad_state;
} // bad_state_return


// return npos if no comments in
static size_t find_comments(const std::string& line) {
  enum state_t { PLAIN, STR, LEFT } state, next_state;
  state = PLAIN;
  size_t ret = 0;
  for (const auto& c : line) {
    if (state == PLAIN) {
      if (c == '/')
        next_state = LEFT;
      else if (c == '"')
        next_state = STR;
      else
        next_state = PLAIN;
    } else if (state == STR) {
      if (c == '"' || c == '\n')
        next_state = PLAIN;
      // the '\n' case is in case we encounter some issue to find
      // the ending of a string
      else
        next_state = STR;
    } else if (state == LEFT) {
      if (c == '/') {
        ILA_CHECK(ret > 0);
        return ret - 1;
      } else
        next_state = PLAIN;
    }
    state = next_state;
    ++ret;
  }
  return std::string::npos;
}

void AQedInfoGeneratorImpl::load_json(const std::string& fname, nlohmann::json& j) {
  if (bad_state_return())
    return;
  std::ifstream fin(fname);

  if (!fin.is_open()) {
    ILA_ERROR << "Cannot read from file:" << fname;
    _bad_state = true;
    return;
  }

  // remove the comments
  std::string contents;
  std::string line;
  while (std::getline(fin, line)) {
    auto comment_begin = find_comments(line);
    if (comment_begin != std::string::npos)
      contents += line.substr(0, comment_begin);
    else
      contents += line;
    contents += "\n";
  }
  j = nlohmann::json::parse(contents);
} // load_json

} // namespace ilang