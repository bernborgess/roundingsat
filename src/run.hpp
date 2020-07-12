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

#include "Solver.hpp"
#include "typedefs.hpp"

namespace rs {

namespace run {

extern std::vector<bool> solution;
extern BigVal upper_bound;
extern BigVal lower_bound;
extern Solver solver;

struct LazyVar {
  const BigVal mult;
  const int n;
  Var currentVar;
  ID atLeastID = ID_Undef;
  ID atMostID = ID_Undef;
  ConstrSimple32 atLeast;  // X >= k + y1 + ... + yi
  ConstrSimple32 atMost;   // X =< k + y1 + ... + yi-1 + (1+n-k-i)yi

  LazyVar(const Ce32 cardCore, Var startVar, const BigVal& m);
  ~LazyVar();

  int remainingVars();
  void addVar(Var v);
  void addAtLeastConstraint();
  void addAtMostConstraint();
  void addSymBreakingConstraint(Var prevvar) const;
};

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar> lv);

bool foundSolution();
void printObjBounds(const BigVal& lower, const BigVal& upper);

void checkLazyVariables(CeArb reformObj, std::vector<std::shared_ptr<LazyVar>>& lazyVars);
ID addLowerBound(const CeArb origObj, const BigVal& lower_bound, ID& lastLowerBound);
ID handleInconsistency(const CeArb origObj, CeArb reformObj, CeSuper core,
                       std::vector<std::shared_ptr<LazyVar>>& lazyVars, ID& lastLowerBound);
ID handleNewSolution(const CeArb origObj, ID& lastUpperBound);

void optimize(CeArb origObj);
void decide();
void run(CeArb objective);

}  // namespace run

}  // namespace rs
