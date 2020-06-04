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
  bool weakenNonImplying = false;

  enum OPTIONS {
    HELP,
    PRINTSOL,
    VERBOSITY,
    VARDECAY,
    RINC,
    RFIRST,
    OPTMODE,
    PROPCOUNTING,
    PROPCLAUSE,
    PROPCARD,
    PROPIDX,
    PROPSUP,
    PROOFLOG,
    LP,
    LPBUDGET,
    LPCUTGOMORY,
    LPCUTLEARNED,
    LPINTOLERANCE,
    LPMAXCUTCOS,
    LPGOMCUTLIM,
    CAMAXDIV,
    CAWEAKENFULL,
    CAWEAKENNONIMPLYING
  };
  std::vector<std::string> opts = {"help",
                                   "print-sol",
                                   "verbosity",
                                   "var-decay",
                                   "rinc",
                                   "rfirst",
                                   "opt-mode",
                                   "prop-counting",
                                   "prop-clause",
                                   "prop-card",
                                   "prop-idx",
                                   "prop-sup",
                                   "proof-log",
                                   "lp",
                                   "lp-budget",
                                   "lp-cut-gomory",
                                   "lp-cut-learned",
                                   "lp-intolerance",
                                   "lp-maxcutcos",
                                   "lp-gomcutlim",
                                   "ca-maxdiv",
                                   "ca-weaken-full",
                                   "ca-weaken-nonimplying"};

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
        opt_val, opts[OPTIONS::PRINTSOL], [](double x) -> bool { return x == 0 || x == 1; }, printSol);
    getOptionNum(
        opt_val, opts[OPTIONS::VERBOSITY], [](double x) -> bool { return std::abs(x) == x && x >= 0; }, verbosity);
    getOptionNum(
        opt_val, opts[OPTIONS::VARDECAY], [](double x) -> bool { return x >= 0.5 && x < 1; }, v_vsids_decay);
    getOptionNum(
        opt_val, opts[OPTIONS::RINC], [](double x) -> bool { return x >= 1; }, rinc);
    getOptionNum(
        opt_val, opts[OPTIONS::RFIRST], [](double x) -> bool { return std::abs(x) == x && x >= 1; }, rfirst);
    getOptionEnum(opt_val, opts[OPTIONS::OPTMODE], optMode, optModeMap);
    getOptionNum(
        opt_val, opts[OPTIONS::PROPCOUNTING], [](double x) -> bool { return x >= 0 || x <= 1; }, countingProp);
    getOptionNum(
        opt_val, opts[OPTIONS::PROPCLAUSE], [](double x) -> bool { return x == 0 || x == 1; }, clauseProp);
    getOptionNum(
        opt_val, opts[OPTIONS::PROPCARD], [](double x) -> bool { return x == 0 || x == 1; }, cardProp);
    getOptionNum(
        opt_val, opts[OPTIONS::PROPIDX], [](double x) -> bool { return x == 0 || x == 1; }, idxProp);
    getOptionNum(
        opt_val, opts[OPTIONS::PROPSUP], [](double x) -> bool { return x == 0 || x == 1; }, supProp);
    getOptionStr(opt_val, opts[OPTIONS::PROOFLOG], proofLogName);
    getOptionNum(
        opt_val, opts[OPTIONS::LP], [](double x) -> bool { return x >= -1; }, lpPivotRatio);
    getOptionNum(
        opt_val, opts[OPTIONS::LPBUDGET], [](double x) -> bool { return std::abs(x) == x && x >= 1; }, lpPivotBudget);
    getOptionNum(
        opt_val, opts[OPTIONS::LPCUTGOMORY], [](double x) -> bool { return x == 0 || x == 1; }, addGomoryCuts);
    getOptionNum(
        opt_val, opts[OPTIONS::LPCUTLEARNED], [](double x) -> bool { return x == 0 || x == 1; }, addLearnedCuts);
    getOptionNum(
        opt_val, opts[OPTIONS::LPINTOLERANCE], [](double x) -> bool { return x > 0; }, intolerance);
    getOptionNum(
        opt_val, opts[OPTIONS::LPMAXCUTCOS], [](double x) -> bool { return 1 >= x && x >= 0; }, maxCutCos);
    getOptionNum(
        opt_val, opts[OPTIONS::LPGOMCUTLIM], [](double x) -> bool { return x >= 1; }, gomoryCutLimit);
    getOptionNum(
        opt_val, opts[OPTIONS::CAMAXDIV], [](double x) -> bool { return x == 0 || x == 1; }, maxdiv);
    getOptionNum(
        opt_val, opts[OPTIONS::CAWEAKENFULL], [](double x) -> bool { return x == 0 || x == 1; }, weakenFull);
    getOptionNum(
        opt_val, opts[OPTIONS::CAWEAKENNONIMPLYING], [](double x) -> bool { return x == 0 || x == 1; },
        weakenNonImplying);
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
    usageVoid(opts[OPTIONS::HELP], "Print this help message");
    usageVal(opts[OPTIONS::PRINTSOL], "Print the solution if found", "0 or 1", printSol);
    usageVal(opts[OPTIONS::VERBOSITY], "Verbosity of the output", "int >= 0", verbosity);
    usageVal(opts[OPTIONS::VARDECAY], "VSIDS decay factor", "0.5 <= float < 1", v_vsids_decay);
    usageVal(opts[OPTIONS::RINC], "Base of the Luby restart sequence", "float >= 1", rinc);
    usageVal(opts[OPTIONS::RFIRST], "Interval of the Luby restart sequence", "int >= 1", rfirst);
    usageEnum(opts[OPTIONS::OPTMODE], "Optimization mode", optModeMap, optMode);
    usageVal(opts[OPTIONS::PROPCOUNTING], "Counting propagation instead of watched propagation",
             "float between 0 (no counting) and 1 (always counting)", countingProp);
    usageVal(opts[OPTIONS::PROPCLAUSE], "Optimized two-watched propagation for clauses", "0 or 1", clauseProp);
    usageVal(opts[OPTIONS::PROPCARD], "Optimized watched propagation for cardinalities", "0 or 1", cardProp);
    usageVal(opts[OPTIONS::PROPIDX], "Optimize index of watches during propagation", "0 or 1", idxProp);
    usageVal(opts[OPTIONS::PROPSUP], "Avoid superfluous watch checks", "0 or 1", supProp);
    usageVal(opts[OPTIONS::PROOFLOG], "Filename for the proof logs", "filepath", "off");
    usageVal(opts[OPTIONS::LP],
             "Ratio of #pivots/#conflicts limiting LP calls (negative means infinite, 0 means no LP solving)",
             "float >= -1", lpPivotRatio);
    usageVal(opts[OPTIONS::LPBUDGET], "Base LP call pivot budget", "int >= 1", lpPivotBudget);
    usageVal(opts[OPTIONS::LPCUTGOMORY], "Generate Gomory cuts", "0 or 1", addGomoryCuts);
    usageVal(opts[OPTIONS::LPCUTLEARNED], "Use learned constraints as cuts", "0 or 1", addLearnedCuts);
    usageVal(opts[OPTIONS::LPINTOLERANCE], "Intolerance for floating point artifacts", "float > 0", intolerance);
    usageVal(opts[OPTIONS::LPMAXCUTCOS],
             "Upper bound on cosine of angle between cuts added in one round, higher means cuts can be more parallel",
             "float between 0 and 1", maxCutCos);
    usageVal(opts[OPTIONS::LPGOMCUTLIM], "Max number of rows considered for Gomory cuts in one round", "int >= 1",
             gomoryCutLimit);
    usageVal(opts[OPTIONS::CAMAXDIV], "Use asserting coefficient as divisor for reason constraints", "0 or 1", maxdiv);
    usageVal(opts[OPTIONS::CAWEAKENFULL],
             "Weaken non-divisible non-falsified literals in reason constraints completely", "0 or 1", weakenFull);
    usageVal(opts[OPTIONS::CAWEAKENNONIMPLYING], "Weaken non-implying falsified literals from reason constraints",
             "0 or 1", weakenNonImplying);
  }
};