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

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#include "soplex/headers/soplex.h"
#pragma GCC diagnostic pop

#include "SolverStructs.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

class LpSolver {
  soplex::SoPlex lp;
  Solver& solver;

  double tolerance = 1e-6; // TODO: add as option

  bool foundLpSolution = false;
  soplex::DVectorReal lpSolution;
  soplex::DVectorReal lpSlackSolution;
  soplex::DVectorReal lpMultipliers;
  soplex::DVectorReal upperBounds;
  soplex::DVectorReal lowerBounds;
  soplex::DSVectorReal lpRow;
  std::vector<int> datavec;

 public:
  LpSolver(Solver& solver, const intConstr& objective);

  void setNbVariables(int n);

  void run() {}

 private:
  void LP_addConstraints();
  void LP_convertConstraint(CRef cr, soplex::DSVectorReal& row, Val& rhs);

	// NOTE: if b is positive, the comparison is more relaxed. If b is negative, the comparison is more strict.
	inline bool relaxedLT(double a, double b){ return a <= b*(1+tolerance); }
// NOTE: if a is negative, the comparison is more relaxed. If a is positive, the comparison is more strict.
	inline bool strictLT(double a, double b){ return !relaxedLT(b,a); }

	inline double nonIntegrality(double a){ return abs(round(a)-a); }
	inline bool validCoeff(double a){ return round(a)==a && std::abs(a)<=1e9; }
	inline bool validRhs(double a){ return round(a)==a && a<=1e15 && a>=-1e15;} // NOTE: double type can only store ranges of integers up to ~9e15

	bool LP_pureCnf();
};
