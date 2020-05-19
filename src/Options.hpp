/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#pragma once

#include <cstring>
#include "aux.hpp"
#include "quit.hpp"

struct Options {
  std::string formulaName;
  std::string proofLogName;
  bool printSol = false;
  enum OPTMODE { LINEAR, COREGUIDED, LAZYCOREGUIDED, HYBRID, LAZYHYBRID };
  std::vector<std::string> optModeMap = {"linear", "core-guided", "lazy-core-guided", "hybrid", "lazy-hybrid"};
  OPTMODE optMode = LINEAR;

  int verbosity = 1;
  bool clauseProp = true;
  bool cardProp = true;
  bool idxProp = true;
  bool supProp = true;
  float countingProp = 0.7;
  int resize_factor = 2;

  double rinc = 2;
  long long rfirst = 100;
  long long incReduceDB = 100;
  float v_vsids_decay = 0.95;
  float c_vsids_decay = 0.999;

  float lpPivotRatio = 1;
  long long lpPivotBudget = 1000;
  bool addGomoryCuts = false;
  bool addLearnedCuts = false;
  double intolerance = 1e-6;
  double maxCutCos = 0.1;
  int gomoryCutLimit = 100;

  bool maxdiv = false;
  bool weakenFull = false;

  std::vector<std::string> opts = {"help",          "print-sol",      "verbosity",      "var-decay",    "rinc",
                                   "rfirst",        "opt-mode",       "prop-counting",  "prop-clause",  "prop-card",
                                   "prop-idx",      "prop-sup",       "proof-log",      "lp",           "lp-budget",
                                   "lp-cut-gomory", "lp-cut-learned", "lp-intolerance", "lp-maxcutcos", "lp-gomcutlim",
                                   "ca-maxdiv",     "ca-weaken-full"};

  typedef bool (*func)(double);
  template <typename T>
  void getOptionNum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, func test,
                    T& val) {
    if (!opt_val.count(option)) return;
    double v = atof(opt_val.at(option).c_str());
    if (test(v))
      val = v;
    else
      quit::exit_ERROR({"Invalid value for ", option, ": ", opt_val.at(option), ".\nCheck usage with --help option."});
  }

  void getOptionStr(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option,
                    std::string& val) {
    if (!opt_val.count(option)) return;
    val = opt_val.at(option);
  }

  template <typename ENUM>
  void getOptionEnum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, ENUM& val,
                     const std::vector<std::string>& map) {
    if (!opt_val.count(option)) return;
    std::string s = opt_val.at(option);
    for (unsigned int i = 0; i < map.size(); ++i)
      if (map[i] == s) {
        val = static_cast<ENUM>(i);
        return;
      }
    quit::exit_ERROR({"Invalid value for ", option, ": ", opt_val.at(option), ".\nCheck usage with --help option."});
  }

  void parseCommandLine(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
      if (!strcmp(argv[i], "--help")) {
        usage(argv[0]);
        exit(0);
      }
    }

    std::unordered_map<std::string, std::string> opt_val;
    for (int i = 1; i < argc; i++) {
      if (std::string(argv[i]).substr(0, 2) != "--")
        formulaName = argv[i];
      else {
        bool found = false;
        for (std::string& key : opts) {
          if (std::string(argv[i]).substr(0, key.size() + 3) == "--" + key + "=") {
            found = true;
            opt_val[key] = std::string(argv[i]).substr(key.size() + 3);
          }
        }
        if (!found) quit::exit_ERROR({"Unknown option: ", argv[i], ".\nCheck usage with --help option."});
      }
    }
    getOptionNum(
        opt_val, opts[1], [](double x) -> bool { return x == 0 || x == 1; }, printSol);
    getOptionNum(
        opt_val, opts[2], [](double x) -> bool { return std::abs(x) == x && x >= 0; }, verbosity);
    getOptionNum(
        opt_val, opts[3], [](double x) -> bool { return x >= 0.5 && x < 1; }, v_vsids_decay);
    getOptionNum(
        opt_val, opts[4], [](double x) -> bool { return x >= 1; }, rinc);
    getOptionNum(
        opt_val, opts[5], [](double x) -> bool { return std::abs(x) == x && x >= 1; }, rfirst);
    getOptionEnum(opt_val, opts[6], optMode, optModeMap);
    getOptionNum(
        opt_val, opts[7], [](double x) -> bool { return x >= 0 || x <= 1; }, countingProp);
    getOptionNum(
        opt_val, opts[8], [](double x) -> bool { return x == 0 || x == 1; }, clauseProp);
    getOptionNum(
        opt_val, opts[9], [](double x) -> bool { return x == 0 || x == 1; }, cardProp);
    getOptionNum(
        opt_val, opts[10], [](double x) -> bool { return x == 0 || x == 1; }, idxProp);
    getOptionNum(
        opt_val, opts[11], [](double x) -> bool { return x == 0 || x == 1; }, supProp);
    getOptionStr(opt_val, opts[12], proofLogName);
    getOptionNum(
        opt_val, opts[13], [](double x) -> bool { return x >= -1; }, lpPivotRatio);
    getOptionNum(
        opt_val, opts[14], [](double x) -> bool { return std::abs(x) == x && x >= 1; }, lpPivotBudget);
    getOptionNum(
        opt_val, opts[15], [](double x) -> bool { return x == 0 || x == 1; }, addGomoryCuts);
    getOptionNum(
        opt_val, opts[16], [](double x) -> bool { return x == 0 || x == 1; }, addLearnedCuts);
    getOptionNum(
        opt_val, opts[17], [](double x) -> bool { return x > 0; }, intolerance);
    getOptionNum(
        opt_val, opts[18], [](double x) -> bool { return 1 >= x && x >= 0; }, maxCutCos);
    getOptionNum(
        opt_val, opts[19], [](double x) -> bool { return x >= 1; }, gomoryCutLimit);
    getOptionNum(
        opt_val, opts[20], [](double x) -> bool { return 1 >= x && x >= 0; }, maxdiv);
    getOptionNum(
        opt_val, opts[21], [](double x) -> bool { return 1 >= x && x >= 0; }, weakenFull);
  }

  constexpr static int colwidth = 14;

  void usageEnum(const std::string& option, const std::string& explanation, const std::vector<std::string>& optMap,
                 int def) {
    std::cout << " --" << option << "=? ";
    for (unsigned int i = option.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << explanation << " (";
    for (std::string s : optMap)
      std::cout << (s == optMap[def].c_str() ? "default=" : "") << s << (s == optMap.back() ? "" : ", ");
    std::cout << ")\n";
  }

  template <typename T>
  void usageVal(const std::string& option, const std::string& explanation, const std::string& bounds,
                const T& variable) {
    std::cout << " --" << option << "=? ";
    for (unsigned int i = option.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << explanation << " (" << bounds << "; default " << variable << ")\n";
  }

  void usageVoid(const std::string& option, const std::string& explanation) {
    std::cout << " --" << option << " ";
    for (unsigned int i = option.size(); i < colwidth + 2; ++i) std::cout << " ";
    std::cout << explanation << "\n";
  }

  void usage(char* name) {
    printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", name);
    printf("\n");
    printf("Options:\n");
    usageVoid(opts[0], "Print this help message");
    usageVal(opts[1], "Print the solution if found", "0 or 1", printSol);
    usageVal(opts[2], "Verbosity of the output", "int >= 0", verbosity);
    usageVal(opts[3], "VSIDS decay factor", "0.5 <= float < 1", v_vsids_decay);
    usageVal(opts[4], "Base of the Luby restart sequence", "float >= 1", rinc);
    usageVal(opts[5], "Interval of the Luby restart sequence", "int >= 1", rfirst);
    usageEnum(opts[6], "Optimization mode", optModeMap, optMode);
    usageVal(opts[7], "Counting propagation instead of watched propagation",
             "float between 0 (no counting) and 1 (always counting)", countingProp);
    usageVal(opts[8], "Optimized two-watched propagation for clauses", "0 or 1", clauseProp);
    usageVal(opts[9], "Optimized watched propagation for cardinalities", "0 or 1", cardProp);
    usageVal(opts[10], "Optimize index of watches during propagation", "0 or 1", idxProp);
    usageVal(opts[11], "Avoid superfluous watch checks", "0 or 1", supProp);
    usageVal(opts[12], "Filename for the proof logs", "filepath", "off");
    usageVal(opts[13], "Ratio of #pivots/#conflicts limiting LP calls (negative means infinite, 0 means no LP solving)",
             "float >= -1", lpPivotRatio);
    usageVal(opts[14], "Base LP call pivot budget", "int >= 1", lpPivotBudget);
    usageVal(opts[15], "Generate Gomory cuts", "0 or 1", addGomoryCuts);
    usageVal(opts[16], "Use learned constraints as cuts", "0 or 1", addLearnedCuts);
    usageVal(opts[17], "Intolerance for floating point artifacts", "float > 0", intolerance);
    usageVal(opts[18],
             "Upper bound on cosine of angle between cuts added in one round, higher means cuts can be more parallel",
             "float between 0 and 1", maxCutCos);
    usageVal(opts[19], "Max number of rows considered for Gomory cuts in one round", "int >= 1", gomoryCutLimit);
    usageVal(opts[20], "Use asserting coefficient as divisor for reason constraints", "0 or 1", maxdiv);
    usageVal(opts[21], "Weaken non-divisible non-falsified literals in reason constraints completely", "0 or 1",
             weakenFull);
  }
};