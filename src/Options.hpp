/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt
Copyright (c) 2020, Stephan Gocht

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

namespace rs {

class Option {
 protected:
  std::string name = "";
  std::string description = "";

 public:
  Option(const std::string& n, const std::string& d) : name(n), description(d) {}

  virtual void printUsage(int colwidth) const = 0;
  virtual bool parse(const std::unordered_map<std::string, std::string>& optVals) = 0;  // TODO: string argument
};

class VoidOption : public Option {
  bool val = false;

 public:
  VoidOption(const std::string& n, const std::string& d) : Option{n, d} {}

  explicit operator bool() const { return val; }

  void printUsage(int colwidth) const override {
    std::cout << " --" << name;
    for (int i = name.size(); i < colwidth + 3; ++i) std::cout << " ";
    std::cout << description << "\n";
  }

  bool parse(const std::unordered_map<std::string, std::string>& optVals) override {
    val = true;
    return (optVals.count(name));
  }
};

class BoolOption : public Option {
  bool val = false;

 public:
  BoolOption(const std::string& n, const std::string& d, bool v) : Option{n, d}, val(v) {}

  explicit operator bool() const { return val; }

  void printUsage(int colwidth) const override {
    std::cout << " --" << name << "=? ";
    for (int i = name.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << description << " (0 or 1; default " << val << ")\n";
  }

  bool parse(const std::unordered_map<std::string, std::string>& optVals) override {
    if (!optVals.count(name)) return false;
    const std::string& v = optVals.at(name);
    try {
      val = std::stod(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (val != 0 && val != 1)
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    return true;
  }
};

class NumOption : public Option {
  double val;
  std::string checkDescription;
  std::function<bool(double)> check;

 public:
  NumOption(const std::string& n, const std::string& d, double v, const std::string& cd,
            const std::function<bool(double)>& c)
      : Option{n, d}, val(v), checkDescription(cd), check(c) {}

  double get() const { return val; }

  void printUsage(int colwidth) const override {
    std::cout << " --" << name << "=? ";
    for (int i = name.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << description << " (" << checkDescription << "; default " << val << ")\n";
  }

  bool parse(const std::unordered_map<std::string, std::string>& optVals) override {
    if (!optVals.count(name)) return false;
    const std::string& v = optVals.at(name);
    try {
      val = std::stod(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (!check(val)) quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    return true;
  }
};

class EnumOption : public Option {
  std::string val;
  std::vector<std::string> values;

 public:
  EnumOption(const std::string& n, const std::string& d, const std::string& v, const std::vector<std::string>& vs)
      : Option{n, d}, val(v), values(vs) {}

  void printUsage(int colwidth) const override {
    std::cout << " --" << name << "=? ";
    for (int i = name.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << description << " (";
    for (int i = 0; i < (int)values.size(); ++i) {
      if (i > 0) std::cout << ", ";
      if (values[i] == val) std::cout << "default=";
      std::cout << values[i];
    }
    std::cout << ")\n";
  }

  bool parse(const std::unordered_map<std::string, std::string>& optVals) override {
    if (!optVals.count(name)) return false;
    const std::string& v = optVals.at(name);
    if (std::find(std::begin(values), std::end(values), v) == std::end(values))
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    val = v;
    return true;
  }

  bool is(const std::string& v) const {
    assert(std::find(std::begin(values), std::end(values), v) != std::end(values));
    return val == v;
  }
};

class StringOption : public Option {
  std::string val;
  std::string checkDescription;
  std::function<bool(const std::string&)> check;

 public:
  StringOption(const std::string& n, const std::string& d, const std::string& v, const std::string& cd,
               const std::function<bool(const std::string&)>& c)
      : Option{n, d}, val(v), checkDescription(cd), check(c) {}

  void printUsage(int colwidth) const override {
    std::cout << " --" << name << "=? ";
    for (int i = name.size(); i < colwidth; ++i) std::cout << " ";
    std::cout << description << " (" << checkDescription << "; default " << val << ")\n";
  }

  bool parse(const std::unordered_map<std::string, std::string>& optVals) override {
    if (!optVals.count(name)) return false;
    val = optVals.at(name);
    if (!check(val)) quit::exit_ERROR({"Invalid value for ", name, ": ", val, ".\nCheck usage with --help option."});
    return true;
  }

  const std::string& get() const { return val; }
};

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
  CASLACKDIV,
  CAWEAKENFULL,
  CAWEAKENNONIMPLYING,
  BUMPONLYFALSE,
  BUMPCANCELING,
  BUMPLITS,
  BITSOVERFLOW,
  BITSREDUCED,
  BITSLEARNED,
};

struct Options {
  VoidOption help{"help", "Print this help message"};
  BoolOption printSol{"print-sol", "Print the solution if found", 0};
  NumOption verbosity{"verbosity", "Verbosity of the output", 1, "0 =< int",
                      [](double x) -> bool { return aux::abs(x) == x && x >= 0; }};
  NumOption varDecay{"var-decay", "VSIDS variable decay factor", 0.95, "0.5 <= float < 1",
                     [](double x) -> bool { return 0.5 <= x && x < 1; }};
  NumOption rinc{"rinc", "Base of the Luby restart sequence", 2, "1 =< float", [](double x) -> bool { return 1 <= x; }};
  NumOption rfirst{"rfirst", "Interval of the Luby restart sequence", 100, "1 =< int",
                   [](double x) -> bool { return aux::abs(x) == x && x >= 1; }};
  EnumOption optMode{"opt-mode",
                     "Optimization mode",
                     "lazy-hybrid",
                     {"linear", "core-guided", "lazy-core-guided", "hybrid", "lazy-hybrid"}};
  NumOption propCounting{"prop-counting", "Counting propagation instead of watched propagation", 0,
                         "0 (no counting) =< float =< 1 (always counting)",
                         [](double x) -> bool { return x >= 0 || x <= 1; }};
  BoolOption propClause{"prop-clause", "Optimized two-watched propagation for clauses", 1};
  BoolOption propCard{"prop-card", "Optimized two-watched propagation for clauses", 1};
  BoolOption propIdx{"prop-idx", "Optimize index of watches during propagation", 1};
  BoolOption propSup{"prop-sup", "Avoid superfluous watch checks", 1};
  StringOption proofLog{"proof-log", "Filename for the proof logs", "", "/path/to/file",
                        [](const std::string&) -> bool { return true; }};

  std::vector<Option*> options;

  Options() {
    options = {
        &help,         &printSol,   &verbosity, &varDecay, &rinc,    &rfirst,   &optMode,
        &propCounting, &propClause, &propCard,  &propIdx,  &propSup, &proofLog,
    };
  }

  std::string formulaName;

  int resize_factor = 2;

  long long incReduceDB = 100;
  float v_vsids_decay = 0.95;
  float c_vsids_decay = 0.999;

  float lpPivotRatio = 1;
  long long lpPivotBudget = 1000;
  bool addGomoryCuts = true;
  bool addLearnedCuts = true;
  double intolerance = 1e-6;
  double maxCutCos = 0.1;
  int gomoryCutLimit = 100;

  bool slackdiv = false;
  bool weakenFull = false;
  bool weakenNonImplying = false;

  bool bumpOnlyFalse = false;
  bool bumpCanceling = true;
  bool bumpLits = true;

  int bitsOverflow = 62;
  int bitsReduced = 29;
  int bitsLearned = 29;
  int bitsInput = 0;

  std::vector<std::string> opts = {
      "help",
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
      "ca-slackdiv",
      "ca-weaken-full",
      "ca-weaken-nonimplying",
      "bump-only-false",
      "bump-canceling",
      "bump-lits",
      "bits-overflow",
      "bits-reduced",
      "bits-learned",
  };

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

    for (Option* opt : options) opt->parse(opt_val);

    getOptionNum(
        opt_val, opts[OPTIONS::LP], [](double x) -> bool { return x >= -1; }, lpPivotRatio);
    getOptionNum(
        opt_val, opts[OPTIONS::LPBUDGET], [](double x) -> bool { return aux::abs(x) == x && x >= 1; }, lpPivotBudget);
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
        opt_val, opts[OPTIONS::CASLACKDIV], [](double x) -> bool { return x == 0 || x == 1; }, slackdiv);
    getOptionNum(
        opt_val, opts[OPTIONS::CAWEAKENFULL], [](double x) -> bool { return x == 0 || x == 1; }, weakenFull);
    getOptionNum(
        opt_val, opts[OPTIONS::CAWEAKENNONIMPLYING], [](double x) -> bool { return x == 0 || x == 1; },
        weakenNonImplying);
    getOptionNum(
        opt_val, opts[OPTIONS::BUMPONLYFALSE], [](double x) -> bool { return x == 0 || x == 1; }, bumpOnlyFalse);
    getOptionNum(
        opt_val, opts[OPTIONS::BUMPCANCELING], [](double x) -> bool { return x == 0 || x == 1; }, bumpCanceling);
    getOptionNum(
        opt_val, opts[OPTIONS::BUMPLITS], [](double x) -> bool { return x == 0 || x == 1; }, bumpLits);
    getOptionNum(
        opt_val, opts[OPTIONS::BITSOVERFLOW], [](double x) -> bool { return x >= 0; }, bitsOverflow);
    getOptionNum(
        opt_val, opts[OPTIONS::BITSREDUCED], [](double x) -> bool { return x >= 0; }, bitsReduced);
    getOptionNum(
        opt_val, opts[OPTIONS::BITSLEARNED], [](double x) -> bool { return x >= 0; }, bitsLearned);
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
    for (Option* opt : options) opt->printUsage(14);

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
    usageVal(opts[OPTIONS::CASLACKDIV],
             "Use slack+1 as divisor for reason constraints (instead of the asserting coefficient)", "0 or 1",
             slackdiv);
    usageVal(opts[OPTIONS::CAWEAKENFULL],
             "Weaken non-divisible non-falsified literals in reason constraints completely", "0 or 1", weakenFull);
    usageVal(opts[OPTIONS::CAWEAKENNONIMPLYING], "Weaken non-implying falsified literals from reason constraints",
             "0 or 1", weakenNonImplying);
    usageVal(opts[OPTIONS::BUMPONLYFALSE],
             "Bump activity of literals encountered during conflict analysis only when falsified", "0 or 1",
             bumpOnlyFalse);
    usageVal(opts[OPTIONS::BUMPCANCELING],
             "Bump activity of literals encountered during conflict analysis when canceling", "0 or 1", bumpCanceling);
    usageVal(opts[OPTIONS::BUMPLITS],
             "Bump activity of literals encountered during conflict analysis, twice when occurring with opposing sign",
             "0 or 1", bumpLits);
    usageVal(opts[OPTIONS::BITSOVERFLOW], "Bit width of maximum coefficient during conflict analysis calculations",
             "int >= 0", bitsOverflow);
    usageVal(opts[OPTIONS::BITSREDUCED],
             "Bit width of maximum coefficient after reduction when exceeding " + opts[OPTIONS::BITSOVERFLOW],
             "int >= 0", bitsReduced);
    usageVal(opts[OPTIONS::BITSLEARNED],
             "Bit width of maximum coefficient for learned constraints (0 is unlimited, 1 reduces to cardinalities)",
             "int >= 0", bitsLearned);
  }
};

}  // namespace rs
