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
extern Solver solver;

struct LazyVar {
  Solver& solver;
  const int n;
  Var currentVar;
  ID atLeastID = ID_Undef;
  ID atMostID = ID_Undef;
  ConstrSimple32 atLeast;  // X >= k + y1 + ... + yi
  ConstrSimple32 atMost;   // X =< k + y1 + ... + yi-1 + (1+n-k-i)yi

  LazyVar(Solver& slvr, const Ce32 cardCore, Var startVar);
  ~LazyVar();

  int remainingVars();
  void addVar(Var v);
  ID addAtLeastConstraint();
  ID addAtMostConstraint();
  ID addSymBreakingConstraint(Var prevvar) const;
};

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar> lv);

template <typename SMALL>
struct LvM {
  std::unique_ptr<LazyVar> lv;
  SMALL m;
};

template <typename SMALL, typename LARGE>
class Optimization {
  const CePtr<ConstrExp<SMALL, LARGE>> origObj;
  CePtr<ConstrExp<SMALL, LARGE>> reformObj;

  LARGE lower_bound;
  LARGE upper_bound;
  ID lastUpperBound = ID_Undef;
  ID lastUpperBoundUnprocessed = ID_Undef;
  ID lastLowerBound = ID_Undef;
  ID lastLowerBoundUnprocessed = ID_Undef;

  std::vector<LvM<SMALL>> lazyVars;
  IntSet assumps;

  bool foundSolution() { return run::solution.size() > 0; }

 public:
  Optimization(CePtr<ConstrExp<SMALL, LARGE>> obj) : origObj(obj) {
    assert(origObj->vars.size() > 0);
    // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
    lower_bound = -origObj->getDegree();
    upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

    reformObj = solver.cePools.take<SMALL, LARGE>();
    reformObj->stopLogging();
    origObj->copyTo(reformObj);
  };

  void printObjBounds() {
    if (options.verbosity.get() == 0) return;
    std::cout << "c bounds ";
    if (foundSolution()) {
      std::cout << bigint(upper_bound);  // TODO: remove bigint(...) hack
    } else {
      std::cout << "-";
    }
    std::cout << " >= " << bigint(lower_bound) << " @ " << stats.getTime() << "\n";  // TODO: remove bigint(...) hack
  }

  void checkLazyVariables() {
    for (int i = 0; i < (int)lazyVars.size(); ++i) {
      LazyVar& lv = *lazyVars[i].lv;
      if (reformObj->getLit(lv.currentVar) == 0) {
        // add auxiliary variable
        long long newN = solver.getNbVars() + 1;
        solver.setNbVars(newN);
        Var oldvar = lv.currentVar;
        lv.addVar(newN);
        // reformulate the objective
        reformObj->addLhs(lazyVars[i].m, newN);
        // add necessary lazy constraints
        if (lv.addAtLeastConstraint() == ID_Unsat || lv.addAtMostConstraint() == ID_Unsat ||
            lv.addSymBreakingConstraint(oldvar) == ID_Unsat) {
          quit::exit_UNSAT(solver.logger, solution, upper_bound);
        }
        if (lv.remainingVars() == 0) {  // fully expanded, no need to keep in memory
          aux::swapErase(lazyVars, i--);
          continue;
        }
      }
    }
  }

  void addLowerBound() {
    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->addRhs(lower_bound);
    solver.dropExternal(lastLowerBound, true, true);
    std::pair<ID, ID> res = solver.addConstraint(aux, Origin::LOWERBOUND);
    lastLowerBoundUnprocessed = res.first;
    lastLowerBound = res.second;
    if (lastLowerBound == ID_Unsat) quit::exit_UNSAT(solver.logger, solution, upper_bound);
  }

  void handleInconsistency(CeSuper core) {
    // take care of derived unit lits
    for (Var v : reformObj->vars) {
      if (isUnit(solver.getLevel(), v) || isUnit(solver.getLevel(), -v)) {
        assumps.remove(v);
        assumps.remove(-v);
      }
    }
    reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
    [[maybe_unused]] LARGE prev_lower = lower_bound;
    lower_bound = -reformObj->getDegree();
    assert(core);
    if (core->isTautology()) {  // only violated unit assumptions were derived
      assert(lower_bound > prev_lower);
      checkLazyVariables();
      addLowerBound();
      if (!options.cgIndCores) assumps.clear();
      return;
    }
    if (core->hasNegativeSlack(solver.getLevel())) {
      assert(solver.decisionLevel() == 0);
      if (solver.logger) core->logInconsistency(solver.getLevel(), solver.getPos(), stats);
      quit::exit_UNSAT(solver.logger, solution, upper_bound);
    }
    // figure out an appropriate core
    core->simplifyToCardinality(false);
    if (!core->isClause()) ++stats.NCORECARDINALITIES;
    Ce32 cardCore = solver.cePools.take32();
    core->copyTo(cardCore);
    assert(cardCore->hasNoZeroes());
    for (Var v : cardCore->vars) {
      assert(assumps.has(-cardCore->getLit(v)));
      assumps.remove(-cardCore->getLit(v));
    }

    // adjust the lower bound
    SMALL mult = 0;
    for (Var v : cardCore->vars) {
      assert(reformObj->getLit(v) != 0);
      if (mult == 0) {
        mult = aux::abs(reformObj->coefs[v]);
      } else if (mult == 1) {
        break;
      } else {
        mult = std::min(mult, aux::abs(reformObj->coefs[v]));
      }
    }
    assert(mult > 0);
    lower_bound += cardCore->getDegree() * mult;

    if (options.cgLazy && cardCore->vars.size() - cardCore->getDegree() > 1) {
      // add auxiliary variable
      long long newN = solver.getNbVars() + 1;
      solver.setNbVars(newN);
      // reformulate the objective
      cardCore->invert();
      reformObj->addUp(cardCore, mult);
      cardCore->invert();
      reformObj->addLhs(mult, newN);  // add only one variable for now
      assert(lower_bound == -reformObj->getDegree());
      // add first lazy constraint
      lazyVars.push_back({std::make_unique<LazyVar>(solver, cardCore, newN), mult});
      lazyVars.back().lv->addAtLeastConstraint();
      lazyVars.back().lv->addAtMostConstraint();
    } else {
      // add auxiliary variables
      long long oldN = solver.getNbVars();
      long long newN = oldN - static_cast<int>(cardCore->getDegree()) + cardCore->vars.size();
      solver.setNbVars(newN);
      // reformulate the objective
      for (Var v = oldN + 1; v <= newN; ++v) cardCore->addLhs(-1, v);
      cardCore->invert();
      reformObj->addUp(cardCore, mult);
      assert(lower_bound == -reformObj->getDegree());
      // add channeling constraints
      if (solver.addConstraint(cardCore, Origin::COREGUIDED).second == ID_Unsat)
        quit::exit_UNSAT(solver.logger, solution, upper_bound);
      cardCore->invert();
      if (solver.addConstraint(cardCore, Origin::COREGUIDED).second == ID_Unsat)
        quit::exit_UNSAT(solver.logger, solution, upper_bound);
      for (Var v = oldN + 1; v < newN; ++v) {  // add symmetry breaking constraints
        if (solver.addConstraint(ConstrSimple32({{1, v}, {1, -v - 1}}, 1), Origin::COREGUIDED).second == ID_Unsat)
          quit::exit_UNSAT(solver.logger, solution, upper_bound);
      }
    }
    checkLazyVariables();
    addLowerBound();
    if (!options.cgIndCores) assumps.clear();
  }

  void handleNewSolution() {
    [[maybe_unused]] LARGE prev_val = upper_bound;
    upper_bound = -origObj->getRhs();
    for (Var v : origObj->vars) upper_bound += origObj->coefs[v] * (int)solution[v];
    assert(upper_bound < prev_val);

    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->invert();
    aux->addRhs(-upper_bound + 1);
    solver.dropExternal(lastUpperBound, true, true);
    std::pair<ID, ID> res = solver.addConstraint(aux, Origin::UPPERBOUND);
    lastUpperBoundUnprocessed = res.first;
    lastUpperBound = res.second;
    if (lastUpperBound == ID_Unsat) quit::exit_UNSAT(solver.logger, solution, upper_bound);
  }

  void logProof() {
    if (!solver.logger) return;
    assert(lastUpperBound != ID_Undef);
    assert(lastUpperBound != ID_Unsat);
    assert(lastLowerBound != ID_Undef);
    assert(lastLowerBound != ID_Unsat);
    CePtr<ConstrExp<SMALL, LARGE>> coreAggregate = solver.cePools.take<SMALL, LARGE>();
    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->invert();
    aux->addRhs(1 - upper_bound);
    aux->resetBuffer(lastUpperBoundUnprocessed);
    coreAggregate->addUp(aux);
    aux->reset();
    origObj->copyTo(aux);
    aux->addRhs(lower_bound);
    aux->resetBuffer(lastLowerBoundUnprocessed);
    coreAggregate->addUp(aux);
    assert(coreAggregate->hasNegativeSlack(solver.getLevel()));
    assert(solver.decisionLevel() == 0);
    coreAggregate->logInconsistency(solver.getLevel(), solver.getPos(), stats);
  }

  void optimize() {
    size_t upper_time = 0, lower_time = 0;
    SolveState reply = SolveState::SAT;
    SMALL coeflim = options.cgStrat ? reformObj->getLargestCoef() : 0;
    int coefLimFlag = -1;
    while (true) {
      size_t current_time = stats.getDetTime();
      if (reply != SolveState::INPROCESSED && reply != SolveState::RESTARTED) printObjBounds();

      // NOTE: only if assumptions are empty will they be refilled
      if (assumps.isEmpty() &&
          (options.optMode.is("core-guided") ||
           (options.optMode.is("core-boosted") && stats.getRunTime() < options.cgBoosted.get()) ||
           (options.optMode.is("hybrid") && lower_time < upper_time))) {  // use core-guided step by setting assumptions
        reformObj->removeZeroes();
        if (coefLimFlag == 1) {
          SMALL oldCoeflim = coeflim;
          coeflim = 0;
          for (Var v : reformObj->vars) {
            SMALL cf = aux::abs(reformObj->coefs[v]);
            if (cf > coeflim && cf < oldCoeflim) coeflim = cf;
          }
        }
        std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than arbitrary
        litcoefs.reserve(reformObj->vars.size());
        for (Var v : reformObj->vars) {
          assert(reformObj->getLit(v) != 0);
          SMALL cf = aux::abs(reformObj->coefs[v]);
          if (cf >= coeflim) litcoefs.emplace_back(static_cast<double>(cf), v);
        }
        std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double>& t1, const Term<double>& t2) {
          return t1.c > t2.c || (t1.l < t2.l && t1.c == t2.c);
        });
        for (const Term<double>& t : litcoefs) assumps.add(-reformObj->getLit(t.l));
        coefLimFlag = 0;
      }
      assert(upper_bound > lower_bound);
      std::pair<SolveState, CeSuper> out = aux::timeCall<std::pair<SolveState, CeSuper>>(
          [&] { return solver.solve(assumps, solution); }, stats.SOLVETIME);
      reply = out.first;
      if (reply == SolveState::RESTARTED) continue;
      if (reply == SolveState::UNSAT) quit::exit_UNSAT(solver.logger, solution, upper_bound);
      assert(solver.decisionLevel() == 0);
      if (assumps.isEmpty()) {
        upper_time += stats.getDetTime() - current_time;
      } else {
        lower_time += stats.getDetTime() - current_time;
      }
      if (reply == SolveState::SAT) {
        assumps.clear();
        assert(foundSolution());
        ++stats.NSOLS;
        handleNewSolution();
        if (coefLimFlag == 0) coefLimFlag = 1;
      } else if (reply == SolveState::INCONSISTENT) {
        ++stats.NCORES;
        handleInconsistency(out.second);
        coefLimFlag = -1;
      } else {
        assert(reply == SolveState::INPROCESSED);  // keep looping
        if (coefLimFlag == 0) coefLimFlag = 1;
        assumps.clear();
      }
      if (lower_bound >= upper_bound) {
        printObjBounds();
        logProof();
        quit::exit_UNSAT(solver.logger, solution, upper_bound);
      }
    }
  }
};

void decide();
void run(CeArb objective);

}  // namespace run

}  // namespace rs
