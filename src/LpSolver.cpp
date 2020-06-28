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

CandidateCut::CandidateCut(ConstrExpArb& in, const std::vector<double>& sol, LpSolver& lpslvr) {
  assert(in.isSaturated());
  lpslvr.shrinkToFit(in);
  simpcons = in.toSimpleCons<long long, int128>();
  // NOTE: simpcons is already in var-normal form
  initialize(sol);
}

CandidateCut::CandidateCut(const Constr& in, CRef cref, const std::vector<double>& sol, LpSolver& lpslvr) : cr(cref) {
  assert(in.degree() > 0);
  ConstrExpArb& tmp = lpslvr.solver.ceStore.takeArb();
  in.toConstraint(tmp);
  lpslvr.shrinkToFit(tmp);
  if (tmp.getDegree() <= 0) {
    lpslvr.solver.ceStore.leave(tmp);
    return;
  }
  simpcons = tmp.toSimpleCons<long long, int128>();
  // NOTE: simpcons is already in var-normal form
  lpslvr.solver.ceStore.leave(tmp);
  initialize(sol);
  assert(cr != CRef_Undef);
}

void CandidateCut::initialize(const std::vector<double>& sol) {
  std::sort(simpcons.terms.begin(), simpcons.terms.end(),
            [](const Term<long long>& t1, const Term<long long>& t2) { return t1.l < t2.l; });
  assert(norm == 1);
  norm = 0;
  for (const Term<long long>& p : simpcons.terms) norm += (double)p.c * (double)p.c;
  norm = std::sqrt(norm);
  ratSlack = -simpcons.rhs;
  for (Term<long long>& p : simpcons.terms) {
    assert(p.l > 0);  // simpcons is in var-normal form
    ratSlack += (double)p.c * sol[p.l];
  }
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

  // add two empty rows for objective bound constraints
  assert(ID_Trivial == 1);
  for (ID id = 0; id <= ID_Trivial; ++id) {
    soplex::DSVectorReal row(0);
    lp.addRowReal(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, 0));
    row2data.emplace_back(id, false);
  }

  // add all formula constraints
  for (CRef cr : solver.constraints)
    if (solver.ca[cr].getOrigin() == Origin::FORMULA) addConstraint(cr, false);

  soplex::DVectorReal objective;
  objective.reDim(getNbVariables());  // NOTE: automatically set to zero
  if (o.vars.size() > 0)
    for (Var v : o.vars) objective[v] = o.coefs[v];
  else
    for (int v = 1; v < getNbVariables(); ++v) objective[v] = 1;  // add default objective function
  lp.changeObjReal(objective);

  if (options.verbosity > 1) std::cout << "c Finished initializing LP" << std::endl;
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

  lpSol.reDim(n);
  lpSolution.resize(n, 0);
  lowerBounds.reDim(n);
  upperBounds.reDim(n);
  assert(getNbVariables() == n);
}

int LpSolver::getNbVariables() const { return lp.numCols(); }
int LpSolver::getNbRows() const { return lp.numRows(); }

void LpSolver::createLinearCombinationFarkas(ConstrExpArb& out, soplex::DVectorReal& mults) {
  assert(out.isReset());
  double scale = getScaleFactor(mults, true);
  if (scale == 0) return;
  assert(scale > 0);

  for (int r = 0; r < mults.dim(); ++r) {
    bigint factor = static_cast<bigint>(mults[r] * scale);
    if (factor <= 0) continue;
    assert(lp.lhsReal(r) != INFTY);
    ConstrExp64& ce = rowToConstraint(r);
    out.addUp(ce, factor);
    solver.ceStore.leave(ce);
  }
  out.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  assert(out.hasNoZeroes());
  out.weakenSmalls(out.absCoeffSum() / static_cast<bigint>((double)out.vars.size() / options.intolerance));
  out.saturateAndFixOverflow(solver.getLevel(), options.weakenFull);
}

CandidateCut LpSolver::createLinearCombinationGomory(soplex::DVectorReal& mults) {
  double mult = getScaleFactor(mults, false);
  if (mult == 0) return CandidateCut();
  ConstrExpArb& lcc = solver.ceStore.takeArb();

  std::vector<std::pair<bigint, int>> slacks;
  for (int r = 0; r < mults.dim(); ++r) {
    bigint factor = static_cast<bigint>(mults[r] * mult);
    if (factor == 0) continue;
    ConstrExp64& ce = rowToConstraint(r);
    if (factor < 0) ce.invert();
    lcc.addUp(ce, rs::abs(factor));
    solver.ceStore.leave(ce);
    slacks.emplace_back(-factor, r);
  }

  bigint b = lcc.getRhs();
  for (Var v : lcc.vars)
    if (lpSolution[v] > 0.5) b -= lcc.coefs[v];
  if (b == 0) {
    solver.ceStore.leave(lcc);
    return CandidateCut();
  }

  assert(mult > 0);
  bigint divisor = static_cast<bigint>(mult);
  while ((b % divisor) == 0) ++divisor;
  lcc.applyMIR(divisor, [&](Var v) -> Lit { return lpSolution[v] <= 0.5 ? v : -v; });

  // round up the slack variables MIR style and cancel out the slack variables
  bigint bmodd = aux::mod_safe(b, divisor);
  for (unsigned i = 0; i < slacks.size(); ++i) {
    bigint factor =
        bmodd * aux::floordiv_safe(slacks[i].first, divisor) + std::min(aux::mod_safe(slacks[i].first, divisor), bmodd);
    if (factor == 0) continue;
    ConstrExp64& ce = rowToConstraint(slacks[i].second);
    if (factor < 0) ce.invert();
    lcc.addUp(ce, rs::abs(factor));
    solver.ceStore.leave(ce);
  }
  if (lcc.plogger) lcc.logAsInput();
  // TODO: fix logging for Gomory cuts

  lcc.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  if (lcc.getDegree() <= 0)
    lcc.reset();
  else {
    assert(lcc.hasNoZeroes());
    lcc.weakenSmalls(lcc.absCoeffSum() / static_cast<bigint>((double)lcc.vars.size() / options.intolerance));
  }
  CandidateCut result(lcc, lpSolution, *this);
  solver.ceStore.leave(lcc);
  return result;
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
      assert(indices[row] < (int)lpSolution.size());
      fractionality = nonIntegrality(lpSolution[indices[row]]);
    } else {  // basic slack variable / row
      assert(-indices[row] - 1 < lpSlackSolution.dim());
      fractionality = nonIntegrality(lpSlackSolution[-indices[row] - 1]);
    }
    assert(fractionality >= 0);
    if (fractionality > 0) fracrowvec.emplace_back(fractionality, row);
  }
  std::priority_queue<std::pair<double, int>> fracrows(std::less<std::pair<double, int>>(), fracrowvec);

  [[maybe_unused]] double last = 0.5;
  for (int i = 0; i < options.gomoryCutLimit && !fracrows.empty(); ++i) {
    assert(last >= fracrows.top().first);
    last = fracrows.top().first;
    int row = fracrows.top().second;
    fracrows.pop();

    assert(lpMultipliers.dim() == getNbRows());
    lpMultipliers.clear();
    lp.getBasisInverseRowReal(row, lpMultipliers.get_ptr());
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
    for (int i = 0; i < lpMultipliers.dim(); ++i) lpMultipliers[i] = -lpMultipliers[i];
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
  }
}

void LpSolver::constructLearnedCandidates() {
  for (CRef cr : solver.constraints) {
    if (asynch_interrupt) return;
    const Constr& c = solver.ca[cr];
    if (c.getOrigin() == Origin::LEARNED || c.getOrigin() == Origin::LEARNEDFARKAS || c.getOrigin() == Origin::GOMORY) {
      bool containsNonOriginalVars = false;
      for (unsigned int i = 0; i < c.size() && !containsNonOriginalVars; ++i) {
        containsNonOriginalVars = rs::abs(c.lit(i)) > solver.getNbOrigVars();
      }
      if (containsNonOriginalVars) continue;
      candidateCuts.emplace_back(c, cr, lpSolution, *this);
      if (candidateCuts.back().ratSlack >= -options.intolerance) candidateCuts.pop_back();
    }
  }
}

void LpSolver::addFilteredCuts() {
  for ([[maybe_unused]] const CandidateCut& cc : candidateCuts) {
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
    CandidateCut& cc = candidateCuts[i];
    ConstrExpArb& ce = solver.ceStore.takeArb();
    ce.init(cc.simpcons);
    ce.postProcess(solver.getLevel(), solver.getPos(), true, stats);
    assert(ce.getDegree() < INF_long);
    assert(ce.getRhs() < INF_long);
    assert(ce.isSaturated());
    assert(ce.getDegree() > 0);
    if (cc.cr == CRef_Undef) {  // Gomory cut
      solver.learnConstraint(ce, Origin::GOMORY);
    } else {  // learned cut
      ++stats.NLPLEARNEDCUTS;
    }
    addConstraint(ce, true);
    solver.ceStore.leave(ce);
  }
}

void LpSolver::pruneCuts() {
  assert(getNbRows() == (int)row2data.size());
  lpMultipliers.clear();
  if (!lp.getDual(lpMultipliers)) return;
  for (int r = 0; r < getNbRows(); ++r)
    if (row2data[r].removable && lpMultipliers[r] == 0) {
      ++stats.NLPDELETEDCUTS;
      toRemove.insert(r);
    }
}

// NOTE: it is possible that mults are negative (e.g., when calculating Gomory cuts)
double LpSolver::getScaleFactor(soplex::DVectorReal& mults, bool removeNegatives) {
  double largest = 0;
  for (int i = 0; i < mults.dim(); ++i) {
    if (std::isnan(mults[i]) || std::isinf(mults[i]) || (removeNegatives && mults[i] < 0)) mults[i] = 0;
    largest = std::max(rs::abs(mults[i]), largest);
  }
  if (largest == 0) return 0;
  return maxMult / largest;
}

ConstrExp64& LpSolver::rowToConstraint(int row) {
  ConstrExp64& ce = solver.ceStore.take64();
  double rhs = lp.lhsReal(row);
  assert(rs::abs(rhs) != INFTY);
  assert(validVal(rhs));
  ce.addRhs(rhs);

  lpRow.clear();
  lp.getRowVectorReal(row, lpRow);
  for (int i = 0; i < lpRow.size(); ++i) {
    const soplex::Nonzero<double>& el = lpRow.element(i);
    assert(validVal(el.val));
    assert(el.val != 0);
    ce.addLhs((long long)el.val, el.idx);
  }
  if (ce.plogger) ce.resetBuffer(row2data[row].id);
  return ce;
}

LpStatus LpSolver::checkFeasibility(ConstrExpArb& confl, bool inProcessing) {
  double startTime = aux::cpuTime();
  LpStatus result = _checkFeasibility(confl, inProcessing);
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
  return result;
}

void LpSolver::inProcess() {
  double startTime = aux::cpuTime();
  _inProcess();
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
}

LpStatus LpSolver::_checkFeasibility(ConstrExpArb& confl, bool inProcessing) {
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

  createLinearCombinationFarkas(confl, lpMultipliers);
  solver.learnConstraint(confl, Origin::FARKAS);
  if (confl.getSlack(solver.getLevel()) < 0) return INFEASIBLE;
  confl.reset();
  return UNDETERMINED;
}

void LpSolver::_inProcess() {
  assert(solver.decisionLevel() == 0);
  ConstrExpArb& confl = solver.ceStore.takeArb();
  LpStatus lpstat = checkFeasibility(confl, true);
  assert(lpstat != INFEASIBLE || confl.getSlack(solver.getLevel()) < 0);
  solver.ceStore.leave(confl);  // in case of unsatisfiability, it will be triggered via the learned Farkas
  if (lpstat != OPTIMAL) return;
  if (!lp.hasSol()) return;
  lp.getPrimal(lpSol);
  assert(lpSol.dim() == (int)lpSolution.size());
  for (int i = 0; i < lpSol.dim(); ++i) lpSolution[i] = lpSol[i];
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

void LpSolver::convertConstraint(const ConstrSimple64& c, soplex::DSVectorReal& row, double& rhs) {
  assert(row.max() >= (int)c.terms.size());
  for (auto& t : c.terms) {
    if (t.c == 0) continue;
    assert(t.l > 0);
    assert(t.l < lp.numColsReal());
    assert(t.c < INF_long);
    row.add(t.l, t.c);
  }
  rhs = c.rhs;
  assert(validVal(rhs));
}

void LpSolver::addConstraint(ConstrExpArb& c, bool removable, bool upperbound, bool lowerbound) {
  shrinkToFit(c);
  ID id = c.plogger ? c.logProofLineWithInfo("LP", stats) : ++solver.crefID;
  if (upperbound || lowerbound) {
    assert(upperbound != lowerbound);
    double rhs;
    soplex::DSVectorReal row(c.vars.size());
    convertConstraint(c.toSimpleCons<long long, int128>(), row, rhs);
    lp.changeRowReal(lowerbound, soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs));
    row2data[lowerbound] = {id, false};  // so upper bound resides in row[0]
  } else {
    toAdd[id] = {c.toSimpleCons<long long, int128>(), removable};
  }
}

void LpSolver::addConstraint(CRef cr, bool removable, bool upperbound, bool lowerbound) {
  assert(cr != CRef_Undef);
  assert(cr != CRef_Unsat);
  ConstrExpArb& ce = solver.ceStore.takeArb();
  solver.ca[cr].toConstraint(ce);
  addConstraint(ce, removable, upperbound, lowerbound);
  solver.ceStore.leave(ce);
}

// TODO: exploit lp.changeRowReal for more efficiency, e.g. when replacing the upper and lower bound on the objective
void LpSolver::flushConstraints() {
  if (toRemove.size() > 0) {  // first remove rows
    std::vector<int> rowsToRemove(getNbRows(), 0);
    for (int row : toRemove) {
      ++stats.NLPDELETEDROWS;
      rowsToRemove[row] = -1;
    }
    lp.removeRowsReal(rowsToRemove.data());  // TODO: use other removeRowsReal method?
    for (int r = 0; r < (int)rowsToRemove.size(); ++r) {
      int newrow = rowsToRemove[r];
      if (newrow < 0 || newrow == r) continue;
      row2data[newrow] = row2data[r];
    }
    row2data.resize(getNbRows());
    toRemove.clear();
  }

  if (toAdd.size() > 0) {  // then add rows
    soplex::LPRowSetReal rowsToAdd;
    rowsToAdd.reMax(toAdd.size());
    row2data.reserve(row2data.size() + toAdd.size());
    for (auto& p : toAdd) {
      double rhs;
      soplex::DSVectorReal row(p.second.cs.terms.size());
      convertConstraint(p.second.cs, row, rhs);
      rowsToAdd.add(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs));
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

void LpSolver::shrinkToFit(ConstrExpArb& c) {
  bigint maxRhs = std::max(c.getDegree(), rs::abs(c.getRhs()));
  if (maxRhs >= INF_long) {
    c.weakenDivideRoundRational(lpSolution, aux::ceildiv<bigint>(maxRhs, INF_long - 1));
    assert(c.getDegree() < INF_long);
    assert(c.getRhs() < INF_long);
    assert(c.isSaturated());
  } else {
    c.saturate();
  }
  assert(c.getDegree() < INF_long);
  assert(c.getRhs() < INF_long);
  assert(c.isSaturated());
}

#endif  // WITHSOPLEX
