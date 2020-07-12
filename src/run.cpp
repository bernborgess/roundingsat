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

#include "run.hpp"
#include "ConstrExp.hpp"

std::vector<bool> run::solution;
BigVal run::upper_bound;
BigVal run::lower_bound;
Solver run::solver;

run::LazyVar::LazyVar(const Ce32 cardCore, Var startVar, const BigVal& m) : mult(m), n(cardCore->vars.size()) {
  assert(cardCore->isCardinality());
  cardCore->toSimple()->copyTo(atLeast);
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore->getDegree());
  atMost.rhs = -atLeast.rhs;
  atMost.terms.reserve(atLeast.terms.size());
  for (auto& t : atLeast.terms) {
    atMost.terms.emplace_back(-t.c, t.l);
  }
  addVar(startVar);
}

run::LazyVar::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

int run::LazyVar::remainingVars() { return n + n - atLeast.rhs - atLeast.terms.size(); }

void run::LazyVar::addVar(Var v) {
  currentVar = v;
  atLeast.terms.emplace_back(-1, v);
  atMost.terms.emplace_back(1, v);
}

void run::LazyVar::addAtLeastConstraint() {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, false, false);  // TODO: should be erasable
  atLeastID = solver.addConstraint(atLeast, Origin::COREGUIDED).second;
  if (atLeastID == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
}

void run::LazyVar::addAtMostConstraint() {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, false, false);  // TODO: should be erasable
  atMost.terms.back().c += remainingVars();
  atMostID = solver.addConstraint(atMost, Origin::COREGUIDED).second;
  atMost.terms.back().c = 1;
  if (atMostID == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
}

void run::LazyVar::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  if (solver.addConstraint(ConstrSimple32({{1, prevvar}, {1, -currentVar}}, 1), Origin::COREGUIDED).second == ID_Unsat)
    quit::exit_UNSAT(solution, upper_bound, solver.logger);
}

bool run::foundSolution() { return solution.size() > 0; }

void run::printObjBounds(const BigVal& lower, const BigVal& upper) {
  if (options.verbosity == 0) return;
  if (foundSolution()) {
    std::cout << "c bounds " << upper << " >= " << lower << "\n";
  } else {
    std::cout << "c bounds - >= " << lower << "\n";
  }
}

void run::checkLazyVariables(CeArb reformObj, std::vector<std::shared_ptr<LazyVar>>& lazyVars) {
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    std::shared_ptr<LazyVar> lv = lazyVars[i];
    if (reformObj->getLit(lv->currentVar) == 0) {
      // add auxiliary variable
      long long newN = solver.getNbVars() + 1;
      solver.setNbVars(newN);
      Var oldvar = lv->currentVar;
      lv->addVar(newN);
      // reformulate the objective
      reformObj->addLhs(lv->mult, newN);
      // add necessary lazy constraints
      lv->addAtLeastConstraint();
      lv->addAtMostConstraint();
      lv->addSymBreakingConstraint(oldvar);
      if (lv->remainingVars() == 0) {  // fully expanded, no need to keep in memory
        aux::swapErase(lazyVars, i--);
        continue;
      }
    }
  }
}

ID run::addLowerBound(const CeArb origObj, const BigVal& lower_bound, ID& lastLowerBound) {
  CeArb aux = solver.cePools.takeArb();
  origObj->copyTo(aux);
  aux->addRhs(lower_bound);
  solver.dropExternal(lastLowerBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::LOWERBOUND);
  lastLowerBound = res.second;
  if (lastLowerBound == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
  return res.first;
}

ID run::handleInconsistency(const CeArb origObj, CeArb reformObj, CeSuper core,
                            std::vector<std::shared_ptr<LazyVar>>& lazyVars, ID& lastLowerBound) {
  // take care of derived unit lits and remove zeroes
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
  [[maybe_unused]] BigVal prev_lower = lower_bound;
  lower_bound = -reformObj->getDegree();
  assert(core);
  if (core->isTautology()) {  // only violated unit assumptions were derived
    assert(lower_bound > prev_lower);
    checkLazyVariables(reformObj, lazyVars);
    return addLowerBound(origObj, lower_bound, lastLowerBound);
  }
  if (core->hasNegativeSlack(solver.getLevel())) {
    assert(solver.decisionLevel() == 0);
    if (solver.logger) core->logInconsistency(solver.getLevel(), solver.getPos(), stats);
    quit::exit_UNSAT(solution, upper_bound, solver.logger);
  }
  // figure out an appropriate core
  core->simplifyToCardinality(false);
  if (!core->isClause()) ++stats.NCORECARDINALITIES;
  Ce32 cardCore = solver.cePools.take32();
  core->copyTo(cardCore);

  // adjust the lower bound
  BigVal mult = 0;
  for (Var v : cardCore->vars) {
    assert(reformObj->getLit(v) != 0);
    if (mult == 0) {
      mult = aux::abs(reformObj->coefs[v]);
    } else {
      mult = std::min(mult, aux::abs(reformObj->coefs[v]));
    }
  }
  assert(mult > 0);
  lower_bound += cardCore->getDegree() * mult;

  if ((options.optMode == Options::LAZYCOREGUIDED || options.optMode == Options::LAZYHYBRID) &&
      cardCore->vars.size() - cardCore->getDegree() > 1) {
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
    std::shared_ptr<LazyVar> lv = std::make_shared<LazyVar>(cardCore, newN, mult);
    lazyVars.push_back(lv);
    lv->addAtLeastConstraint();
    lv->addAtMostConstraint();
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
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    cardCore->invert();
    if (solver.addConstraint(cardCore, Origin::COREGUIDED).second == ID_Unsat)
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    for (Var v = oldN + 1; v < newN; ++v) {  // add symmetry breaking constraints
      if (solver.addConstraint(ConstrSimple32({{1, v}, {1, -v - 1}}, 1), Origin::COREGUIDED).second == ID_Unsat)
        quit::exit_UNSAT(solution, upper_bound, solver.logger);
    }
  }
  checkLazyVariables(reformObj, lazyVars);
  return addLowerBound(origObj, lower_bound, lastLowerBound);
}

ID run::handleNewSolution(const CeArb origObj, ID& lastUpperBound) {
  [[maybe_unused]] BigVal prev_val = upper_bound;
  upper_bound = -origObj->getRhs();
  for (Var v : origObj->vars) upper_bound += origObj->coefs[v] * (int)solution[v];
  assert(upper_bound < prev_val);

  CeArb aux = solver.cePools.takeArb();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::UPPERBOUND);
  lastUpperBound = res.second;
  if (lastUpperBound == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger);
  return res.first;
}

void run::optimize(CeArb origObj) {
  assert(origObj->vars.size() > 0);
  // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  origObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
  origObj->stopLogging();
  lower_bound = -origObj->getDegree();
  upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

  CeArb reformObj = solver.cePools.takeArb();
  reformObj->stopLogging();
  origObj->copyTo(reformObj);
  ID lastUpperBound = ID_Undef;
  ID lastUpperBoundUnprocessed = ID_Undef;
  ID lastLowerBound = ID_Undef;
  ID lastLowerBoundUnprocessed = ID_Undef;

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
      reformObj->removeZeroes();
      for (Var v : reformObj->vars) {
        assert(reformObj->getLit(v) != 0);
        assumps.add(-reformObj->getLit(v));
      }
      std::sort(assumps.keys.begin(), assumps.keys.end(), [&](Lit l1, Lit l2) {
        return reformObj->getCoef(-l1) > reformObj->getCoef(-l2) ||
               (reformObj->getCoef(-l1) == reformObj->getCoef(-l2) && toVar(l1) < toVar(l2));
      });
    }
    assert(upper_bound > lower_bound);
    std::pair<SolveState, CeSuper> out = solver.solve(assumps, solution);
    reply = out.first;
    if (reply == SolveState::RESTARTED) continue;
    if (reply == SolveState::UNSAT) quit::exit_UNSAT(solution, upper_bound, solver.logger);
    assert(solver.decisionLevel() == 0);
    if (assumps.size() == 0)
      upper_time += stats.getDetTime() - current_time;
    else
      lower_time += stats.getDetTime() - current_time;
    if (reply == SolveState::SAT) {
      assert(foundSolution());
      ++stats.NSOLS;
      lastUpperBoundUnprocessed = handleNewSolution(origObj, lastUpperBound);
      assert((options.optMode != Options::COREGUIDED && options.optMode != Options::LAZYCOREGUIDED) ||
             lower_bound == upper_bound);
    } else if (reply == SolveState::INCONSISTENT) {
      ++stats.NCORES;
      lastLowerBoundUnprocessed = handleInconsistency(origObj, reformObj, out.second, lazyVars, lastLowerBound);
    } else {
      assert(reply == SolveState::INPROCESSED);  // keep looping
    }
    if (lower_bound >= upper_bound) {
      printObjBounds(lower_bound, upper_bound);
      if (solver.logger) {
        assert(lastUpperBound != ID_Undef);
        assert(lastUpperBound != ID_Unsat);
        assert(lastLowerBound != ID_Undef);
        assert(lastLowerBound != ID_Unsat);
        CeArb coreAggregate = solver.cePools.takeArb();
        CeArb aux = solver.cePools.takeArb();
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
      quit::exit_UNSAT(solution, upper_bound, solver.logger);
    }
  }
}

void run::decide() {
  while (true) {
    SolveState reply = solver.solve(IntSet(), solution).first;
    assert(reply != SolveState::INCONSISTENT);
    if (reply == SolveState::SAT)
      quit::exit_SAT(solution, solver.logger);
    else if (reply == SolveState::UNSAT)
      quit::exit_UNSAT({}, 0, solver.logger);
  }
}

void run::run(CeArb objective) {
  if (options.verbosity > 0)
    std::cout << "c #variables " << solver.getNbOrigVars() << " #constraints " << solver.getNbConstraints()
              << std::endl;
  try {
    if (objective->vars.size() > 0) {
      optimize(objective);
    } else {
      decide();
    }
  } catch (const AsynchronousInterrupt& ai) {
    std::cout << "c " << ai.what() << std::endl;
    quit::exit_INDETERMINATE(solution, solver.logger);
  }
}
