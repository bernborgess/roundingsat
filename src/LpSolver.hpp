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
#pragma GCC diagnostic ignored "-Wstrict-overflow"
#pragma GCC diagnostic ignored "-Wdeprecated-copy"
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#include "soplex/soplex.h"
#pragma GCC diagnostic pop

#include "SimpleCons.hpp"
#include "SolverStructs.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

struct CandidateCut {
  SimpleConsInt simpcons;
  CRef cr = CRef_Undef;
  double norm = 1;
  double ratSlack = 0;

  CandidateCut(){};
  CandidateCut(int128Constr& in, const soplex::DVectorReal& sol);
  CandidateCut(const Constr& in, CRef cr, const soplex::DVectorReal& sol);
  double cosOfAngleTo(const CandidateCut& other) const;

 private:
  void initialize(const soplex::DVectorReal& sol);
};
std::ostream& operator<<(std::ostream& o, const CandidateCut& cc);

struct AdditionData {
  soplex::DSVectorReal lhs;
  Val rhs;
  bool removable;
};

struct RowData {
  ID id;
  bool removable;
  RowData(){};
  RowData(ID i, bool r) : id(i), removable(r){};
};

enum LpStatus { INFEASIBLE, OPTIMAL, PIVOTLIMIT, UNDETERMINED };

class LpSolver {
  soplex::SoPlex lp;
  Solver& solver;

  double lpPivotMult = 1;
  constexpr static double INFTY = 1e100;
  // NOTE: 2^59 is the maximum possible, given the 64 bits needed for other calculations
  constexpr static long long maxMult =
      36028797018963968;  // 2^50: 1125899906842624 | 2^55: 36028797018963968 | 2^59: 576460752303423488
  // TODO: properly decide for Gomory cuts

  soplex::DVectorReal lpSolution;
  soplex::DVectorReal lpSlackSolution;
  soplex::DVectorReal lpMultipliers;
  soplex::DVectorReal upperBounds;
  soplex::DVectorReal lowerBounds;
  soplex::DSVectorReal lpRow;

  std::unordered_map<ID, int> id2row;
  std::vector<RowData> row2data;
  std::unordered_set<ID> toRemove;
  std::unordered_map<ID, AdditionData> toAdd;

  std::vector<CandidateCut> candidateCuts;

  int128Constr lcc;
  intConstr ic;

 public:
  LpSolver(Solver& solver, const intConstr& objective);

  void setNbVariables(int n);
  int getNbVariables() const;
  int getNbRows() const;

  // @return: false if inconsistency detected, true otherwise
  // stores inconsistency in solver.conflConstraint
  LpStatus checkFeasibility(bool inProcessing = false);  // TODO: don't use objective function here?
  // @return: false if inconsistency detected, true otherwise
  void inProcess();

  void addConstraint(intConstr& c, bool removable);
  void addConstraint(CRef cr, bool removable);
  void removeConstraint(ID id);

 private:
  void flushConstraints();

  LpStatus _checkFeasibility(bool inProcessing);
  void _inProcess();

  void convertConstraint(intConstr& c, soplex::DSVectorReal& row, Val& rhs);
  void resetBasis();
  void createLinearCombinationFarkas(soplex::DVectorReal& mults);
  CandidateCut createLinearCombinationGomory(soplex::DVectorReal& mults);
  double getScaleFactor(soplex::DVectorReal& mults, bool removeNegatives);
  void rowToConstraint(int row);
  void constructGomoryCandidates();
  void constructLearnedCandidates();
  void addFilteredCuts();
  void pruneCuts();

  inline static double nonIntegrality(double a) { return std::abs(std::round(a) - a); }
  inline static bool validCoeff(double a) { return std::round(a) == a && std::abs(a) < INF; }
  inline static bool validRhs(double a) {
    return std::round(a) == a && a < INF_long && a > -INF_long;
  }  // NOTE: double type can only store ranges of integers up to ~9e15
};
