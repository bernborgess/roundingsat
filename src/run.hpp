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

#include "Constraint.hpp"
#include "Solver.hpp"
#include "typedefs.hpp"

namespace run {
std::vector<bool> solution;
intConstr aux;
intConstr core;
Val upper_bound;
Val lower_bound;
Solver solver;
intConstr objective;

inline void printObjBounds(Val lower, Val upper) {
  if (upper < std::numeric_limits<Val>::max())
    printf("c bounds %10lld >= %10lld\n", upper, lower);
  else
    printf("c bounds          - >= %10lld\n", lower);
}

void handleNewSolution(const intConstr& origObj, ID& lastUpperBound) {
  Val prev_val = upper_bound;
  _unused(prev_val);
  upper_bound = -origObj.getRhs();
  for (Var v : origObj.vars) upper_bound += origObj.coefs[v] * solution[v];
  assert(upper_bound < prev_val);

  origObj.copyTo(aux);
  aux.invert();
  aux.addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  lastUpperBound = solver.addConstraint(aux, ConstraintType::EXTERNAL, true);
  aux.reset();
  if (lastUpperBound == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
}

struct LazyVar {
  int mult;  // TODO: add long long to int check?
  Val rhs;
  std::vector<Lit> lhs;  // TODO: refactor lhs and introducedVars to one Lit vector
  std::vector<Var> introducedVars;
  ID atLeastID = ID_Undef;
  ID atMostID = ID_Undef;

  LazyVar(intConstr& core, Var startvar, int m) : mult(m), rhs(core.getDegree()), introducedVars{startvar} {
    assert(core.isCardinality());
    lhs.reserve(core.vars.size());
    for (Var v : core.vars) lhs.push_back(core.getLit(v));
  }

  ~LazyVar() {
    solver.dropExternal(atLeastID, false, false);
    solver.dropExternal(atMostID, false, false);
  }

  Var getCurrentVar() const { return introducedVars.back(); }

  void addVar(Var v) { introducedVars.push_back(v); }

  void addAtLeastConstraint() {
    // X >= k + y1 + ... + yi
    SimpleCons sc;
    sc.rhs = rhs;
    sc.terms.reserve(lhs.size() + introducedVars.size());
    for (Lit l : lhs) sc.terms.push_back({1, l});
    for (Var v : introducedVars) sc.terms.push_back({-1, v});
    solver.dropExternal(atLeastID, false,
                        false);  // TODO: dropExternal(atLeastID,true)? Or treat them as learned/implied constraints?
    atLeastID = solver.addConstraint(sc, ConstraintType::EXTERNAL, false);
    if (atLeastID == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
  }

  void addAtMostConstraint() {
    // X =< k + y1 + ... + yi-1 + (1+n-k-i)yi
    assert(getCurrentVar() == introducedVars.back());
    SimpleCons sc;
    sc.rhs = -rhs;
    sc.terms.reserve(lhs.size() + introducedVars.size());
    for (Lit l : lhs) sc.terms.push_back({-1, l});
    for (Var v : introducedVars) sc.terms.push_back({1, v});
    sc.terms.push_back({(Coef)(lhs.size() - rhs - introducedVars.size()), getCurrentVar()});
    solver.dropExternal(atMostID, false,
                        false);  // TODO: dropExternal(atMostID,true)? Or treat them as learned/implied constraints?
    atMostID = solver.addConstraint(sc, ConstraintType::EXTERNAL, false);
    if (atMostID == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
  }

  void addSymBreakingConstraint(Var prevvar) const {
    assert(introducedVars.size() > 1);
    // y-- + ~y >= 1 (equivalent to y-- >= y)
    if (solver.addConstraint({{{1, prevvar}, {1, -getCurrentVar()}}, 1}, ConstraintType::AUXILIARY, false) == ID_Unsat)
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
  }
};

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar> lv) {
  for (Var v : lv->introducedVars) o << v << " ";
  o << "| ";
  for (Lit l : lv->lhs) o << "+x" << l << " ";
  o << ">= " << lv->rhs;
  return o;
}

void checkLazyVariables(longConstr& reformObj, std::vector<std::shared_ptr<LazyVar>>& lazyVars) {
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    std::shared_ptr<LazyVar> lv = lazyVars[i];
    if (reformObj.getLit(lv->getCurrentVar()) == 0) {
      // add auxiliary variable
      long long newN = solver.getNbVars() + 1;
      solver.setNbVars(newN);
      reformObj.resize(newN + 1);
      Var oldvar = lv->getCurrentVar();
      lv->addVar(newN);
      // reformulate the objective
      reformObj.addLhs(lv->mult, newN);
      // add necessary lazy constraints
      lv->addAtLeastConstraint();
      lv->addAtMostConstraint();
      lv->addSymBreakingConstraint(oldvar);
      if (lv->introducedVars.size() + lv->rhs == lv->lhs.size()) {
        aux::swapErase(lazyVars, i--);
        continue;
      }
    }
  }
}

void addLowerBound(const intConstr& origObj, Val lower_bound, ID& lastLowerBound) {
  origObj.copyTo(aux);
  aux.addRhs(lower_bound);
  solver.dropExternal(lastLowerBound, true, true);
  lastLowerBound = solver.addConstraint(aux, ConstraintType::EXTERNAL, true);
  aux.reset();
  if (lastLowerBound == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
}

void handleInconsistency(longConstr& reformObj, const intConstr& origObj,
                         std::vector<std::shared_ptr<LazyVar>>& lazyVars, ID& lastLowerBound) {
  // take care of derived unit lits and remove zeroes
  reformObj.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
  Val prev_lower = lower_bound;
  _unused(prev_lower);
  lower_bound = -reformObj.getDegree();
  if (core.getDegree() == 0) {  // apparently only unit assumptions were derived
    assert(lower_bound > prev_lower);
    checkLazyVariables(reformObj, lazyVars);
    addLowerBound(origObj, lower_bound, lastLowerBound);
    return;
  }
  // figure out an appropriate core
  core.simplifyToCardinality(false);

  // adjust the lower bound
  if (core.getDegree() > 1) ++stats.NCORECARDINALITIES;
  long long mult = INF;
  for (Var v : core.vars) {
    assert(reformObj.getLit(v) != 0);
    mult = std::min<long long>(mult, std::abs(reformObj.coefs[v]));
  }
  assert(mult < INF);
  assert(mult > 0);
  lower_bound += core.getDegree() * mult;

  if ((options.optMode == Options::LAZYCOREGUIDED || options.optMode == Options::LAZYHYBRID) &&
      core.vars.size() - core.getDegree() > 1) {
    // add auxiliary variable
    long long newN = solver.getNbVars() + 1;
    solver.setNbVars(newN);
    core.resize(newN + 1);
    reformObj.resize(newN + 1);
    // reformulate the objective
    core.invert();
    reformObj.addUp(solver.getLevel(), core, mult, 1, false);
    core.invert();
    reformObj.addLhs(mult, newN);  // add only one variable for now
    assert(lower_bound == -reformObj.getDegree());
    // add first lazy constraint
    std::shared_ptr<LazyVar> lv = std::make_shared<LazyVar>(core, newN, mult);
    lazyVars.push_back(lv);
    lv->addAtLeastConstraint();
    lv->addAtMostConstraint();
  } else {
    // add auxiliary variables
    long long oldN = solver.getNbVars();
    long long newN = oldN - core.getDegree() + core.vars.size();
    solver.setNbVars(newN);
    core.resize(newN + 1);
    reformObj.resize(newN + 1);
    // reformulate the objective
    for (Var v = oldN + 1; v <= newN; ++v) core.addLhs(-1, v);
    core.invert();
    reformObj.addUp(solver.getLevel(), core, mult, 1, false);
    assert(lower_bound == -reformObj.getDegree());
    // add channeling constraints
    if (solver.addConstraint(core, ConstraintType::AUXILIARY, false) == ID_Unsat)
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    core.invert();
    if (solver.addConstraint(core, ConstraintType::AUXILIARY, false) == ID_Unsat)
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    for (Var v = oldN + 1; v < newN; ++v) {  // add symmetry breaking constraints
      if (solver.addConstraint({{{1, v}, {1, -v - 1}}, 1}, ConstraintType::AUXILIARY, false) == ID_Unsat)
        quit::exit_UNSAT(solution, upper_bound, solver.logger);
    }
  }
  checkLazyVariables(reformObj, lazyVars);
  addLowerBound(origObj, lower_bound, lastLowerBound);
}

void optimize(intConstr& origObj) {
  assert(origObj.vars.size() > 0);
  // NOTE: -origObj.getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  origObj.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
  lower_bound = -origObj.getDegree();
  upper_bound = std::numeric_limits<Val>::max();
  core.initializeLogging(solver.logger);

  Val opt_coef_sum = 0;
  for (Var v : origObj.vars) opt_coef_sum += std::abs(origObj.coefs[v]);
  if (opt_coef_sum >= (Val)INF)
    quit::exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});  // TODO: remove restriction

  longConstr reformObj;
  origObj.copyTo(reformObj);
  ID lastUpperBound = ID_Undef;
  ID lastLowerBound = ID_Undef;

  IntSet assumps;
  std::vector<std::shared_ptr<LazyVar>> lazyVars;
  size_t upper_time = 0, lower_time = 0;
  SolveState reply = SolveState::SAT;
  while (true) {
    size_t current_time = stats.getDetTime();
    if (reply != SolveState::INPROCESSED && reply != SolveState::RESTARTED) printObjBounds(lower_bound, upper_bound);
    assumps.reset();
    if (options.optMode == Options::COREGUIDED || options.optMode == Options::LAZYCOREGUIDED ||
        ((options.optMode == Options::HYBRID || options.optMode == Options::LAZYHYBRID) &&
         lower_time < upper_time)) {  // use core-guided step
      reformObj.removeZeroes();
      for (Var v : reformObj.vars) {
        assert(reformObj.getLit(v) != 0);
        assumps.add(-reformObj.getLit(v));
      }
      std::sort(assumps.keys.begin(), assumps.keys.end(), [&](Lit l1, Lit l2) {
        return reformObj.getCoef(-l1) > reformObj.getCoef(-l2) ||
               (reformObj.getCoef(-l1) == reformObj.getCoef(-l2) && std::abs(l1) < std::abs(l2));
      });
    }
    assert(upper_bound > lower_bound);
    reply = solver.solve(assumps, core, solution);
    if (reply == SolveState::INTERRUPTED) quit::exit_INDETERMINATE(solution, solver.logger);
    if (reply == SolveState::RESTARTED) continue;
    if (reply == SolveState::UNSAT) quit::exit_UNSAT(solution, upper_bound, solver.logger);
    assert(solver.decisionLevel() == 0);
    if (assumps.size() == 0)
      upper_time += stats.getDetTime() - current_time;
    else
      lower_time += stats.getDetTime() - current_time;
    if (reply == SolveState::SAT) {
      assert(solution.size() > 0);
      ++stats.NSOLS;
      handleNewSolution(origObj, lastUpperBound);
      assert((options.optMode != Options::COREGUIDED && options.optMode != Options::LAZYCOREGUIDED) ||
             lower_bound == upper_bound);
    } else if (reply == SolveState::INCONSISTENT) {
      ++stats.NCORES;
      if (core.getSlack(solver.getLevel()) < 0) {
        if (solver.logger) core.logInconsistency(solver.getLevel(), solver.getPos(), stats);
        assert(solver.decisionLevel() == 0);
        quit::exit_UNSAT(solution, upper_bound, solver.logger);
      }
      handleInconsistency(reformObj, origObj, lazyVars, lastLowerBound);
      core.resize(solver.getNbVars() + 1);
    } else
      assert(reply == SolveState::INPROCESSED);  // keep looping
    if (lower_bound >= upper_bound) {
      printObjBounds(lower_bound, upper_bound);
      if (solver.logger) {
        assert(lastUpperBound != ID_Undef);
        assert(lastUpperBound != ID_Unsat);
        assert(lastLowerBound != ID_Undef);
        assert(lastLowerBound != ID_Unsat);
        aux.initializeLogging(solver.logger);
        longConstr coreAggregate;
        coreAggregate.initializeLogging(solver.logger);
        coreAggregate.resize(solver.getNbVars() + 1);
        origObj.copyTo(aux);
        aux.invert();
        aux.addRhs(1 - upper_bound);
        aux.resetBuffer(lastUpperBound - 1);  // -1 to get the unprocessed formula line
        coreAggregate.addUp(solver.getLevel(), aux, 1, 1, false);
        aux.reset();
        origObj.copyTo(aux);
        aux.addRhs(lower_bound);
        aux.resetBuffer(lastLowerBound - 1);  // -1 to get the unprocessed formula line
        coreAggregate.addUp(solver.getLevel(), aux, 1, 1, false);
        aux.reset();
        assert(coreAggregate.getSlack(solver.getLevel()) < 0);
        assert(solver.decisionLevel() == 0);
        coreAggregate.logInconsistency(solver.getLevel(), solver.getPos(), stats);
      }
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    }
  }
}

void decide() {
  while (true) {
    SolveState reply = solver.solve({}, core, solution);
    assert(reply != SolveState::INCONSISTENT);
    if (reply == SolveState::INTERRUPTED) quit::exit_INDETERMINATE({}, solver.logger);
    if (reply == SolveState::SAT)
      quit::exit_SAT(solution, solver.logger);
    else if (reply == SolveState::UNSAT)
      quit::exit_UNSAT({}, 0, solver.logger);
  }
}

void run() {
  std::cout << "c #variables=" << solver.getNbOrigVars() << " #constraints=" << solver.getNbConstraints() << std::endl;
  if (objective.vars.size() > 0)
    optimize(objective);
  else
    decide();
}
}  // namespace run