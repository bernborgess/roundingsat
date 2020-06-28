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

#include "ConstrSimple.hpp"
#include "SolverStructs.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

struct RowData {
  ID id;
  bool removable;
  RowData(){};
  RowData(ID i, bool r) : id(i), removable(r){};
};

enum LpStatus { INFEASIBLE, OPTIMAL, PIVOTLIMIT, UNDETERMINED };

#if WITHSOPLEX

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wstrict-overflow"
#pragma GCC diagnostic ignored "-Wdeprecated-copy"
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#include "soplex.h"
#pragma GCC diagnostic pop

struct AdditionData {
  ConstrSimple64 cs;
  bool removable;
};

class LpSolver;
struct CandidateCut {
  ConstrSimple64 simpcons;
  CRef cr = CRef_Undef;
  double norm = 1;
  double ratSlack = 0;

  CandidateCut(){};
  CandidateCut(ConstrExpArb& in, const std::vector<double>& sol, LpSolver& lpslvr);
  CandidateCut(const Constr& in, CRef cr, const std::vector<double>& sol, LpSolver& lpslvr);
  double cosOfAngleTo(const CandidateCut& other) const;

 private:
  void initialize(const std::vector<double>& sol);
};
std::ostream& operator<<(std::ostream& o, const CandidateCut& cc);

class Solver;
class LpSolver {
  friend class Solver;
  friend class CandidateCut;

  soplex::SoPlex lp;
  Solver& solver;

  double lpPivotMult = 1;
  constexpr static double INFTY = 1e100;
  constexpr static double maxMult = 1e15;  // sufficiently large to reduce rounding errors

  soplex::DVectorReal lpSol;
  std::vector<double> lpSolution;
  soplex::DVectorReal lpSlackSolution;
  soplex::DVectorReal lpMultipliers;
  soplex::DVectorReal upperBounds;
  soplex::DVectorReal lowerBounds;
  soplex::DSVectorReal lpRow;

  std::vector<RowData> row2data;
  std::unordered_set<int> toRemove;  // rows
  std::unordered_map<ID, AdditionData> toAdd;

  std::vector<CandidateCut> candidateCuts;

 public:
  LpSolver(Solver& solver, const ConstrExp32& objective);
  void setNbVariables(int n);

  LpStatus checkFeasibility(ConstrExpArb& confl,
                            bool inProcessing = false);  // TODO: don't use objective function here?
  void inProcess();

  void addConstraint(ConstrExpArb& c, bool removable, bool upperbound = false, bool lowerbound = false);
  void addConstraint(CRef cr, bool removable, bool upperbound = false, bool lowerbound = false);

 private:
  int getNbVariables() const;
  int getNbRows() const;

  void flushConstraints();
  void shrinkToFit(ConstrExpArb& c);

  LpStatus _checkFeasibility(ConstrExpArb& confl, bool inProcessing);
  void _inProcess();

  void convertConstraint(const ConstrSimple64& c, soplex::DSVectorReal& row, double& rhs);
  void resetBasis();
  void createLinearCombinationFarkas(ConstrExpArb& out, soplex::DVectorReal& mults);
  CandidateCut createLinearCombinationGomory(soplex::DVectorReal& mults);
  double getScaleFactor(soplex::DVectorReal& mults, bool removeNegatives);
  ConstrExp64& rowToConstraint(int row);
  void constructGomoryCandidates();
  void constructLearnedCandidates();
  void addFilteredCuts();
  void pruneCuts();

  inline static double nonIntegrality(double a) { return rs::abs(std::round(a) - a); }
  inline static bool validVal(double a) { return std::round(a) == a && std::abs(a) < INF_long; }
  // NOTE: double type can only store ranges of integers up to ~9e15
};

#else
// TODO: check correspondence to above
class LpSolver {
 public:
  LpSolver([[maybe_unused]] Solver& solver, [[maybe_unused]] const ConstrExp32& objective){};
  void setNbVariables([[maybe_unused]] int n){};

  LpStatus checkFeasibility([[maybe_unused]] ConstrExpArb& confl, [[maybe_unused]] bool inProcessing = false) {
    return LpStatus::UNDETERMINED;
  }
  void inProcess() {}

  void addConstraint([[maybe_unused]] ConstrExpArb& c, [[maybe_unused]] bool removable,
                     [[maybe_unused]] bool upperbound, [[maybe_unused]] bool lowerbound) {}
  void addConstraint([[maybe_unused]] CRef cr, [[maybe_unused]] bool removable, [[maybe_unused]] bool upperbound,
                     [[maybe_unused]] bool lowerbound) {}
};

#endif  // WITHSOPLEX
