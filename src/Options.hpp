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

#include <cmath>
#include <cstring>
#include <iostream>
#include <unordered_map>
#include "aux.hpp"
#include "quit.hpp"

struct Options {
  std::string formulaName;
  std::string proofLogName;
  bool printSol = false;
  enum OPTMODE { LINEAR, COREGUIDED, LAZYCOREGUIDED, HYBRID, LAZYHYBRID };
  std::vector<std::string> optModeMap = {"linear", "core-guided", "lazy-core-guided", "hybrid", "lazy-hybrid"};
  OPTMODE optMode = LAZYHYBRID;

  int verbosity = 1;
  bool originalRoundToOne = false;
  bool clauseProp = true;
  bool cardProp = true;
  bool idxProp = true;
  bool supProp = true;
  float countingProp = 0.7;
  int resize_factor = 2;
  bool eagerCA = true;

  double rinc = 2;
  long long rfirst = 100;
  long long incReduceDB = 300;
  float v_vsids_decay = 0.95;
  float c_vsids_decay = 0.999;

	float lpmulti = 0;

  void usageEnum(const std::string& option, const std::string& explanation, const std::vector<std::string>& optMap,
                 int def) {
    std::cout << "  --" << option << "=arg ";
    for (unsigned int i = option.size(); i < 10; ++i) std::cout << " ";
    std::cout << explanation << ": ";
    for (std::string s : optMap) std::cout << s << " ";
    std::cout << "(default " << optMap[def].c_str() << ")\n";
  }

  void usage(char* name) {
    printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", name);
    printf("\n");
    printf("Options:\n");
    printf("  --help           Prints this help message.\n");
    printf("  --print-sol=arg  Prints the solution if found (default %d).\n", printSol);
    printf("  --verbosity=arg  Set the verbosity of the output (default %d).\n", verbosity);
    printf("\n");
    printf("  --var-decay=arg  Set the VSIDS decay factor (0.5<=arg<1; default %lf).\n", v_vsids_decay);
    printf("  --rinc=arg       Set the base of the Luby restart sequence (float >=1; default %lf).\n", rinc);
    printf("  --rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %lld).\n", rfirst);
    printf(
        "  --original-rto=arg Set whether to use RoundingSat's original round-to-one conflict analysis (0 or 1; "
        "default %d).\n",
        originalRoundToOne);
    usageEnum("opt-mode", "Set optimization mode", optModeMap, optMode);
    printf(
        "  --prop-counting=arg Counting propagation instead of watched propagation (float between 0 (no counting) and "
        "1 (always counting)); default %lf).\n",
        countingProp);
    printf("  --prop-clause=arg Optimized two-watched propagation for clauses (0 or 1; default %d).\n", clauseProp);
    printf("  --prop-card=arg  Optimized watched propagation for cardinalities (0 or 1; default %d).\n", cardProp);
    printf("  --prop-idx=arg   Optimize index of watches during propagation (0 or 1; default %d).\n", idxProp);
    printf("  --prop-sup=arg   Avoid superfluous watch checks (0 or 1; default %d).\n", supProp);
    printf("  --eager-ca=arg   Terminate conflict analysis as soon as possible (0 or 1; default %d).\n", eagerCA);
    printf("  --proof-log=arg  Set a filename for the proof logs (string).\n");
    printf(
        "  --lp=arg         Set the ratio of #pivots/#conflicts to limiting the LP solver's calls (negative means "
        "infinite, 0 means no LP solving) (float >=-1; default %lf).\n",
        lpmulti);
  }

  typedef bool (*func)(double);

  template <class T>
  void getOptionNum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, func test,
                    T& val) {
    if (opt_val.count(option)) {
      double v = atof(opt_val.at(option).c_str());
      if (test(v))
        val = v;
      else
        quit::exit_ERROR(
            {"Invalid value for ", option, ": ", opt_val.at(option), ".\nCheck usage with --help option."});
    }
  }

  void getOptionStr(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option,
                    std::string& val) {
    if (opt_val.count(option)) val = opt_val.at(option);
  }

  template <typename ENUM>
  void getOptionEnum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, ENUM& val,
                     const std::vector<std::string>& map) {
    if (opt_val.count(option)) {
      std::string s = opt_val.at(option);
      for (unsigned int i = 0; i < map.size(); ++i)
        if (map[i] == s) {
          val = static_cast<ENUM>(i);
          return;
        }
      quit::exit_ERROR({"Invalid value for ", option, ": ", opt_val.at(option), ".\nCheck usage with --help option."});
    }
  }

  void parseCommandLine(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
      if (!strcmp(argv[i], "--help")) {
        usage(argv[0]);
        exit(0);
      }
    }
    std::vector<std::string> opts = {"print-sol",    "verbosity", "var-decay",     "rinc",        "rfirst",
                                     "original-rto", "opt-mode",  "prop-counting", "prop-clause", "prop-card",
                                     "prop-idx",     "prop-sup",  "eager-ca",      "proof-log",   "lp"};
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
    getOptionNum(opt_val, "print-sol", [](double x) -> bool { return x == 0 || x == 1; }, printSol);
    getOptionNum(opt_val, "verbosity", [](double) -> bool { return true; }, verbosity);
    getOptionNum(opt_val, "var-decay", [](double x) -> bool { return x >= 0.5 && x < 1; }, v_vsids_decay);
    getOptionNum(opt_val, "rinc", [](double x) -> bool { return x >= 1; }, rinc);
    getOptionNum(opt_val, "rfirst", [](double x) -> bool { return x >= 1; }, rfirst);
    getOptionNum(opt_val, "original-rto", [](double x) -> bool { return x == 0 || x == 1; }, originalRoundToOne);
    getOptionEnum(opt_val, "opt-mode", optMode, optModeMap);
    getOptionNum(opt_val, "prop-counting", [](double x) -> bool { return x >= 0 || x <= 1; }, countingProp);
    getOptionNum(opt_val, "prop-clause", [](double x) -> bool { return x == 0 || x == 1; }, clauseProp);
    getOptionNum(opt_val, "prop-card", [](double x) -> bool { return x == 0 || x == 1; }, cardProp);
    getOptionNum(opt_val, "prop-idx", [](double x) -> bool { return x == 0 || x == 1; }, idxProp);
    getOptionNum(opt_val, "prop-sup", [](double x) -> bool { return x == 0 || x == 1; }, supProp);
    getOptionNum(opt_val, "eager-ca", [](double x) -> bool { return x == 0 || x == 1; }, eagerCA);
    getOptionNum(opt_val, "lp", [](double x) -> bool { return x >= -1; }, lpmulti);
    getOptionStr(opt_val, "proof-log", proofLogName);
  }
};