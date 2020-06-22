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

#if WITHSOPLEX

#include "LpSolver.hpp"
#include <queue>
#include "Solver.hpp"

CandidateCut::CandidateCut(ConstrExp96& in, const soplex::DVectorReal& sol) {
  assert(in.isSaturated());
  assert(in.getDegree() < INF);
  if (in.getDegree() <= 0) return;
  simpcons = in.toSimpleCons<Coef, Val>();
  // NOTE: simpcons is already in var-normal form
  initialize(sol);
}

CandidateCut::CandidateCut(const Constr& in, CRef cref, const soplex::DVectorReal& sol)
    : simpcons(in.toSimpleCons<Coef, Val>()), cr(cref) {
  assert(in.degree > 0);
  simpcons.toNormalFormVar();
  initialize(sol);
  assert(cr != CRef_Undef);
}

void CandidateCut::initialize(const soplex::DVectorReal& sol) {
  std::sort(simpcons.terms.begin(), simpcons.terms.end(),
            [](const Term<Coef>& t1, const Term<Coef>& t2) { return t1.l < t2.l; });
  assert(norm == 1);
  norm = 0;
  for (const auto& p : simpcons.terms) norm += (double)p.c * (double)p.c;
  norm = std::sqrt(norm);
  ratSlack = -simpcons.rhs;
  for (auto& p : simpcons.terms) ratSlack += (double)p.c * sol[p.l];
  assert(norm >= 0);
  if (norm == 0) norm = 1;
  ratSlack /= norm;
}

// @pre: simpcons is ordered and norm is calculated
double CandidateCut::cosOfAngleTo(const CandidateCut& other) const {
  assert(norm != 0);
  assert(other.norm != 0);
  double cos = 0;
  int i = 0;
  int j = 0;
  while (i < (int)simpcons.terms.size() && j < (int)other.simpcons.terms.size()) {
    int x = simpcons.terms[i].l;
    int y = other.simpcons.terms[j].l;
    if (x < y)
      ++i;
    else if (x > y)
      ++j;
    else {  // x==y
      cos += (double)simpcons.terms[i].c * (double)other.simpcons.terms[j].c;
      ++i;
      ++j;
    }
  }
  return cos / (norm * other.norm);
}

std::ostream& operator<<(std::ostream& o, const CandidateCut& cc) {
  return o << cc.simpcons << " norm " << cc.norm << " ratSlack " << cc.ratSlack;
}

LpSolver::LpSolver(Solver& slvr, const ConstrExp32& o) : solver(slvr) {
  assert(INFTY == lp.realParam(lp.INFTY));

  if (options.verbosity > 1) std::cout << "c Initializing LP" << std::endl;
  setNbVariables(solver.getNbVars() + 1);
  lp.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_ONLYREAL);
  lp.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_REAL);
  lp.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_REAL);
  lp.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_OFF);
  lp.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
  lp.setIntParam(soplex::SoPlex::VERBOSITY, options.verbosity);
  lp.setRandomSeed(0);

  setNbVariables(slvr.getNbVars());

  // add all formula constraints
  for (CRef cr : solver.constraints)
    if (solver.ca[cr].getOrigin() == Origin::FORMULA) addConstraint(cr, false);

  // How does RoundingSat perform branch-and-bound minimization?
  // - F is the objective function, with a trivial lower bound L and trivial upper bound U
  // - let the rescaled upper bound be UU = 2^ceil(lg(U-L))
  // - take a set of auxiliary variables such that an exponentially weighted sum (EWS) over the negative (!)
  // literals of these variables represents some value Y s.t. 0 <= Y <= UU
  // - let the dynamically changing upper bound of F be UB = UU-Y
  // - introduce the constraint F-L =< UB = UU-Y
  // - flip the inequality: -F+L >= -UU+Y
  // - put -F-Y >= -UU-L in normal form
  // Now, if all auxiliary variables are true, Y==0, so only the trivial upper bound UU+L is enforced on F.
  // If all auxiliary variables are false, Y==UU, so F is forced on its trivial lower bound L.
  soplex::DVectorReal objective;
  objective.reDim(getNbVariables());  // NOTE: automatically set to zero
  if (o.vars.size() > 0)
    for (Var v : o.vars) objective[v] = o.coefs[v];
  else
    for (int v = 1; v < getNbVariables(); ++v) objective[v] = 1;  // add default objective function
  lp.changeObjReal(objective);

  if (options.verbosity > 1) std::cout << "c Finished initializing LP" << std::endl;
  if (solver.logger) {
    ic.initializeLogging(solver.logger);
    lcc.initializeLogging(solver.logger);
  }
}

void LpSolver::setNbVariables(int n) {
  if (n <= getNbVariables()) return;
  soplex::LPColSetReal allCols;
  allCols.reMax(n - getNbVariables());
  soplex::DSVectorReal dummycol(0);
  for (Var v = getNbVariables(); v < n; ++v) {
    allCols.add(soplex::LPColReal(0, dummycol, 1, 0));
  }
  lp.addColsReal(allCols);

  lpSolution.reDim(n);
  lcc.resize(n);
  ic.resize(n);
  lowerBounds.reDim(n);
  upperBounds.reDim(n);
  assert(getNbVariables() == n);
}

int LpSolver::getNbVariables() const { return lp.numCols(); }
int LpSolver::getNbRows() const { return lp.numRows(); }

// BITWISE: -
void LpSolver::createLinearCombinationFarkas(soplex::DVectorReal& mults) {
  assert(lcc.isReset());
  assert(ic.isReset());
  double mult = getScaleFactor(mults, true);
  if (mult == 0) return;
  assert(mult > 0);

  for (int r = 0; r < mults.dim(); ++r) {
    __int128 factor = mults[r] * mult;
    assert(factor >= 0);
    if (factor == 0) continue;
    assert(lp.lhsReal(r) != INFTY);
    rowToConstraint(r);
    lcc.addUp(ic, factor);
    ic.reset();
  }
  lcc.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  assert(lcc.hasNoZeroes());
  lcc.weakenSmalls(lcc.absCoeffSum() / (double)lcc.vars.size() * options.intolerance);
  lcc.saturateAndFixOverflow(solver.getLevel(), options.weakenFull);
}

CandidateCut LpSolver::createLinearCombinationGomory(soplex::DVectorReal& mults) {
  assert(lcc.isReset());
  double mult = getScaleFactor(mults, false);
  if (mult == 0) return CandidateCut();

  std::vector<std::pair<__int128, int>> slacks;
  for (int r = 0; r < mults.dim(); ++r) {
    __int128 factor = mults[r] * mult;
    if (factor == 0) continue;
    rowToConstraint(r);
    if (factor < 0) ic.invert();
    lcc.addUp(ic, rs::abs(factor));
    ic.reset();
    slacks.emplace_back(-factor, r);
  }

  __int128 b = lcc.getRhs();
  for (Var v : lcc.vars)
    if (lpSolution[v] > 0.5) b -= lcc.coefs[v];
  if (b == 0) return CandidateCut();

  assert(mult > 0);
  __int128 divisor = mult;
  while ((b % divisor) == 0) ++divisor;
  lcc.applyMIR(divisor, [&](Var v) -> Lit { return lpSolution[v] <= 0.5 ? v : -v; });

  // round up the slack variables MIR style and cancel out the slack variables
  __int128 bmodd = aux::mod_safe(b, divisor);
  for (unsigned i = 0; i < slacks.size(); ++i) {
    __int128 factor =
        bmodd * aux::floordiv_safe(slacks[i].first, divisor) + std::min(aux::mod_safe(slacks[i].first, divisor), bmodd);
    if (factor == 0) continue;
    rowToConstraint(slacks[i].second);
    if (factor < 0) ic.invert();
    lcc.addUp(ic, rs::abs(factor));
    ic.reset();
  }
  if (lcc.plogger)
    lcc.logAsInput();
  else
    lcc.id = ++solver.crefID;
  // TODO: fix logging for Gomory cuts

  lcc.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  if (lcc.getDegree() <= 0)
    lcc.reset();
  else {
    assert(lcc.hasNoZeroes());
    lcc.weakenSmalls(lcc.absCoeffSum() / (double)lcc.vars.size() * options.intolerance);
    if (lcc.getDegree() >= INF) {
      divisor = aux::ceildiv<__int128>(lcc.getDegree(), INF - 1);
      for (Var v : lcc.vars) {
        __int128 rem = aux::mod_safe(lcc.coefs[v], divisor);
        if (rem == 0) continue;
        assert(rem > 0);
        if ((double)divisor * lpSolution[v] < rem)
          lcc.weaken(divisor - rem, v);
        else
          lcc.weaken(-rem, v);
      }
      lcc.divide(divisor);
      lcc.saturate();
    }
  }
  assert(lcc.getDegree() < INF);
  assert(lcc.isSaturated());
  return CandidateCut(lcc, lpSolution);
}

void LpSolver::constructGomoryCandidates() {
  std::vector<int> indices;
  indices.resize(getNbRows());
  lp.getBasisInd(indices.data());

  assert(lpSlackSolution.dim() == getNbRows());
  std::vector<std::pair<double, int>> fracrowvec;
  for (int row = 0; row < getNbRows(); ++row) {
    if (asynch_interrupt) return;
    double fractionality = 0;
    if (indices[row] >= 0) {  // basic original variable / column
      assert(indices[row] < lpSolution.dim());
      fractionality = nonIntegrality(lpSolution[indices[row]]);
    } else {  // basic slack variable / row
      assert(-indices[row] - 1 < lpSlackSolution.dim());
      fractionality = nonIntegrality(lpSlackSolution[-indices[row] - 1]);
    }
    assert(fractionality >= 0);
    if (fractionality > 0) fracrowvec.emplace_back(fractionality, row);
  }
  std::priority_queue<std::pair<double, int>> fracrows(std::less<std::pair<double, int>>(), fracrowvec);

  double last = 0.5;
  _unused(last);
  for (int i = 0; i < options.gomoryCutLimit && !fracrows.empty(); ++i) {
    assert(last >= fracrows.top().first);
    last = fracrows.top().first;
    int row = fracrows.top().second;
    fracrows.pop();

    assert(lpMultipliers.dim() == getNbRows());
    lpMultipliers.clear();
    lp.getBasisInverseRowReal(row, lpMultipliers.get_ptr());
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    lcc.reset();
    if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
    for (int i = 0; i < lpMultipliers.dim(); ++i) lpMultipliers[i] = -lpMultipliers[i];
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    lcc.reset();
    if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
  }
}

void LpSolver::constructLearnedCandidates() {
  for (CRef cr : solver.constraints) {
    if (asynch_interrupt) return;
    const Constr& c = solver.ca[cr];
    if (id2row.count(c.id) == 0) {
      candidateCuts.emplace_back(c, cr, lpSolution);
      if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
    }
  }
}

void LpSolver::addFilteredCuts() {
  for (const auto& cc : candidateCuts) {
    _unused(cc);
    assert(cc.norm != 0);
  }
  std::sort(candidateCuts.begin(), candidateCuts.end(), [](const CandidateCut& x1, const CandidateCut& x2) {
    return x1.ratSlack > x2.ratSlack ||
           (x1.ratSlack == x2.ratSlack && x1.simpcons.terms.size() < x2.simpcons.terms.size());
  });

  // filter the candidate cuts
  std::vector<int> keptCuts;  // indices
  for (unsigned int i = 0; i < candidateCuts.size(); ++i) {
    bool parallel = false;
    for (unsigned int j = 0; j < keptCuts.size() && !parallel; ++j) {
      if (asynch_interrupt) return;
      parallel = candidateCuts[keptCuts[j]].cosOfAngleTo(candidateCuts[i]) > options.maxCutCos;
    }
    if (!parallel) keptCuts.push_back(i);
  }

  for (int i : keptCuts) {
    auto& cc = candidateCuts[i];
    if (cc.cr == CRef_Undef) {  // Gomory cut
      ic.init(cc.simpcons);
      ic.postProcess(solver.getLevel(), solver.getPos(), true, stats);
      if (ic.getDegree() <= 0) continue;
      assert(ic.id != ID_Trivial);
      solver.learnConstraint(ic, Origin::GOMORY);
      // NOTE: learnConstraint fixes a unique ID for ic, needed to add cut as constraint
      // TODO: not the cleanest way to guarantee a unique ID for Gomory cuts
      assert(id2row.count(ic.id) == 0);
      addConstraint(ic, true);
      ic.reset();
    } else {  // learned cut
      ++stats.NLPLEARNEDCUTS;
      addConstraint(cc.cr, true);
    }
  }
}

void LpSolver::pruneCuts() {
  assert(getNbRows() == (int)row2data.size());
  lpMultipliers.clear();
  if (!lp.getDual(lpMultipliers)) return;
  for (int r = 0; r < getNbRows(); ++r)
    if (row2data[r].removable && lpMultipliers[r] == 0) {
      ++stats.NLPDELETEDCUTS;
      removeConstraint(row2data[r].id);
    }
}

// BITWISE: +log2(maxMult)+log2(1e9) // TODO: check BITWISE
// @return: multiplier fitting in positive bigint range, s.t. multiplier*largestV <= max128*INF/nbMults
// @post: no NaN or negative mults (if onlyPositive)
// NOTE: it is possible that mults are negative (e.g., when calculating Gomory cuts)
double LpSolver::getScaleFactor(soplex::DVectorReal& mults, bool removeNegatives) {
  const double max128 = 1e37;  // NOTE: std::numeric_limits<bigint>::max() // TODO: 1e38? Check bits, also for cuts
  int nbMults = 0;
  double largest = maxMult / max128;
  assert(maxMult / largest <= max128);
  for (int i = 0; i < mults.dim(); ++i) {
    if (std::isnan(mults[i]) || (removeNegatives && mults[i] < 0)) mults[i] = 0;  // TODO: report NaN to Ambros?
    if (mults[i] == 0) continue;
    ++nbMults;
    largest = std::max(rs::abs(mults[i]), largest);
  }
  if (nbMults == 0) return 0;
  assert(nbMults < INF);
  double mult = maxMult / largest / nbMults * INF;
  assert(mult > 0);
  assert(mult <= max128);
  return mult;
}

// BITWISE: -
void LpSolver::rowToConstraint(int row) {
  assert(ic.isReset());
  double rhs = lp.lhsReal(row);
  assert(rs::abs(rhs) != INFTY);
  assert(validRhs(rhs));
  ic.addRhs(rhs);

  lpRow.clear();
  lp.getRowVectorReal(row, lpRow);
  for (int i = 0; i < lpRow.size(); ++i) {
    const soplex::Nonzero<double>& el = lpRow.element(i);
    assert(validCoeff(el.val));
    assert(el.val != 0);
    ic.addLhs((Coef)el.val, el.idx);
  }
  ic.id = row2data[row].id;
  if (ic.plogger) ic.resetBuffer(ic.id);
}

LpStatus LpSolver::checkFeasibility(bool inProcessing) {
  double startTime = aux::cpuTime();
  LpStatus result = _checkFeasibility(inProcessing);
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
  return result;
}

void LpSolver::inProcess() {
  double startTime = aux::cpuTime();
  _inProcess();
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
}

LpStatus LpSolver::_checkFeasibility(bool inProcessing) {
  if (solver.logger) solver.logger->logComment("Checking LP", stats);
  if (options.lpPivotRatio < 0)
    lp.setIntParam(soplex::SoPlex::ITERLIMIT, -1);  // no pivot limit
  else if (options.lpPivotRatio * stats.NCONFL < (inProcessing ? stats.NLPPIVOTSROOT : stats.NLPPIVOTSINTERNAL))
    return PIVOTLIMIT;  // pivot ratio exceeded
  else
    lp.setIntParam(soplex::SoPlex::ITERLIMIT, options.lpPivotBudget * lpPivotMult);
  flushConstraints();

  // Set the  LP's bounds based on the current trail
  for (Var v = 1; v < getNbVariables(); ++v) {
    lowerBounds[v] = isTrue(solver.getLevel(), v);
    upperBounds[v] = !isFalse(solver.getLevel(), v);
  }
  lp.changeBoundsReal(lowerBounds, upperBounds);

  // Run the LP
  soplex::SPxSolver::Status stat;
  stat = lp.optimize();
  ++stats.NLPCALLS;
  if (inProcessing)
    stats.NLPPIVOTSROOT += lp.numIterations();
  else
    stats.NLPPIVOTSINTERNAL += lp.numIterations();
  stats.LPSOLVETIME += lp.solveTime();

  if (options.verbosity > 1)
    std::cout << "c " << (inProcessing ? "root" : "internal") << " LP status: " << stat << std::endl;
  assert(stat != soplex::SPxSolver::Status::NO_PROBLEM);
  assert(stat <= soplex::SPxSolver::Status::OPTIMAL_UNSCALED_VIOLATIONS);
  assert(stat >= soplex::SPxSolver::Status::ERROR);

  if (stat == soplex::SPxSolver::Status::ABORT_ITER) {
    lpPivotMult *= 2;  // increase pivot budget when calling the LP solver
    return PIVOTLIMIT;
  }

  if (stat == soplex::SPxSolver::Status::OPTIMAL) {
    ++stats.NLPOPTIMAL;
    if (!lp.hasSol()) {
      ++stats.NLPNOPRIMAL;
      resetBasis();
    }
    if (lp.numIterations() == 0) ++stats.NLPNOPIVOT;
    return OPTIMAL;
  }

  if (stat == soplex::SPxSolver::Status::ABORT_CYCLING) {
    ++stats.NLPCYCLING;
    resetBasis();
    return UNDETERMINED;
  }
  if (stat == soplex::SPxSolver::Status::SINGULAR) {
    ++stats.NLPSINGULAR;
    resetBasis();
    return UNDETERMINED;
  }
  if (stat != soplex::SPxSolver::Status::INFEASIBLE) {
    ++stats.NLPOTHER;
    resetBasis();
    return UNDETERMINED;
  }

  // Infeasible LP :)
  ++stats.NLPINFEAS;

  // To prove that we have an inconsistency, let's build the Farkas proof
  if (!lp.getDualFarkas(lpMultipliers)) {
    ++stats.NLPNOFARKAS;
    resetBasis();
    return UNDETERMINED;
  }

  createLinearCombinationFarkas(lpMultipliers);
  solver.learnConstraint(lcc, Origin::FARKAS);
  if (lcc.getSlack(solver.getLevel()) < 0) {
    lcc.copyTo(solver.conflConstraint);
    lcc.reset();
    return INFEASIBLE;
  }
  lcc.reset();
  return UNDETERMINED;
}

void LpSolver::_inProcess() {
  assert(solver.decisionLevel() == 0);
  LpStatus lpstat = checkFeasibility(true);
  if (lpstat == INFEASIBLE) {
    assert(solver.conflConstraint.getSlack(solver.getLevel()) < 0);
    solver.conflConstraint.reset();  // learned Farkas constraint is falsified and will trigger unsatisfiability
    return;
  } else if (lpstat != OPTIMAL)
    return;
  if (!lp.hasSol()) return;
  lp.getPrimal(lpSolution);
  lp.getSlacksReal(lpSlackSolution);
  assert((int)solver.phase.size() == getNbVariables());
  for (Var v = 1; v < getNbVariables(); ++v) solver.phase[v] = (lpSolution[v] <= 0.5) ? -v : v;
  if (options.verbosity > 0) std::cout << "c rational objective " << lp.objValueReal() << std::endl;
  candidateCuts.clear();
  if (solver.logger && (options.addGomoryCuts || options.addLearnedCuts)) solver.logger->logComment("cutting", stats);
  if (options.addGomoryCuts) constructGomoryCandidates();
  if (options.addLearnedCuts) constructLearnedCandidates();
  addFilteredCuts();
  pruneCuts();
}

void LpSolver::resetBasis() {
  ++stats.NLPRESETBASIS;
  lp.clearBasis();  // and hope next iteration works fine
}

void LpSolver::convertConstraint(ConstrExp32& c, soplex::DSVectorReal& row, Val& rhs) {
  assert(row.max() >= (int)c.vars.size());
  rhs = c.getRhs();
  for (Var v : c.vars) {
    Coef coef = c.coefs[v];
    if (coef == 0) continue;
    assert(v < lp.numColsReal());
    row.add(v, coef);
  }
  assert(validRhs(rhs));
}

void LpSolver::addConstraint(ConstrExp32& c, bool removable) {
  ID id = c.id;
  assert(id != ID_Trivial);
  toRemove.erase(id);
  if (!id2row.count(id) && !toAdd.count(id)) {
    soplex::DSVectorReal row(c.vars.size());
    Val rhs;
    convertConstraint(c, row, rhs);
    toAdd[id] = {row, rhs, removable};
  }
}

void LpSolver::addConstraint(CRef cr, bool removable) {
  assert(cr != CRef_Undef);
  assert(cr != CRef_Unsat);
  solver.ca[cr].toConstraint(ic);
  addConstraint(ic, removable);
  ic.reset();
}

void LpSolver::removeConstraint(ID id) {
  toAdd.erase(id);
  if (id2row.count(id)) toRemove.insert(id);
}

// TODO: exploit lp.changeRowReal for more efficiency, e.g. when replacing the upper and lower bound on the objective
void LpSolver::flushConstraints() {
  if (toRemove.size() > 0) {  // first remove rows
    std::vector<int> rowsToRemove(getNbRows(), 0);
    for (ID id : toRemove) {
      ++stats.NLPDELETEDROWS;
      rowsToRemove[id2row[id]] = -1;
      id2row.erase(id);
    }
    lp.removeRowsReal(rowsToRemove.data());  // TODO: use other removeRowsReal method?
    for (int r = 0; r < (int)rowsToRemove.size(); ++r) {
      int newrow = rowsToRemove[r];
      if (newrow < 0 || newrow == r) continue;
      row2data[newrow] = row2data[r];
      id2row[row2data[newrow].id] = newrow;
    }
    row2data.resize(getNbRows());
    toRemove.clear();
    assert((int)id2row.size() == getNbRows());
    for (int r = 0; r < (int)row2data.size(); ++r) assert(id2row[row2data[r].id] == r);
  }

  if (toAdd.size() > 0) {  // then add rows
    soplex::LPRowSetReal rowsToAdd;
    rowsToAdd.reMax(toAdd.size());
    row2data.reserve(row2data.size() + toAdd.size());
    id2row.reserve(id2row.size() + toAdd.size());
    for (auto& p : toAdd) {
      rowsToAdd.add(soplex::LPRowReal(p.second.lhs, soplex::LPRowReal::Type::GREATER_EQUAL, p.second.rhs));
      id2row[p.first] = row2data.size();
      row2data.emplace_back(p.first, p.second.removable);
      ++stats.NLPADDEDROWS;
    }
    lp.addRowsReal(rowsToAdd);
    toAdd.clear();
  }

  lpSlackSolution.reDim(getNbRows());
  lpMultipliers.reDim(getNbRows());
  assert((int)row2data.size() == getNbRows());
}

#endif  // WITHSOPLEX
