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

#include "LpSolver.hpp"
#include "Solver.hpp"

CandidateCut::CandidateCut(int128Constr& in, const soplex::DVectorReal& sol) {
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
  assert(norm == 0);
  for (const auto& p : simpcons.terms) norm += (double)p.c * (double)p.c;
  norm = std::sqrt(norm);
  ratSlack = -simpcons.rhs;
  for (auto& p : simpcons.terms) ratSlack += (double)p.c * sol[p.l];
  assert(norm != 0);
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

LpSolver::LpSolver(Solver& slvr, const intConstr& o) : solver(slvr) {
  assert(INFTY == lp.realParam(lp.INFTY));

  if (options.verbosity > 1) std::cout << "c Initializing LP" << std::endl;
  setNbVariables(solver.getNbVars() + 1);
  lp.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_ONLYREAL);
  lp.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_REAL);
  lp.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_REAL);
  lp.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_OFF);
  lp.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
  lp.setIntParam(soplex::SoPlex::VERBOSITY, options.verbosity);
  // NOTE: alternative "crash basis" only helps on few instances, according to Ambros, so we don't adjust that parameter

  setNbVariables(slvr.getNbVars());

  // add all formula constraints
  for (CRef cr : solver.constraints)
    if (solver.ca[cr].getType() == ConstraintType::FORMULA) addConstraint(cr, false);

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
  lcc_unlogged.resize(n);
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
  double mult = getScaleFactor(mults, true);

  for (int r = 0; r < mults.dim(); ++r) {
    if (mults[r] == 0) continue;
    assert(mults[r] > 0);
    assert(lp.lhsReal(r) != INFTY);
    rowToConstraint(r);
    lcc.addUp(ic, mults[r] * mult);
    ic.reset();
  }
  lcc.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  if (lcc.getDegree() >= INF) lcc.roundToOne(solver.getLevel(), aux::ceildiv<__int128>(lcc.getDegree(), INF - 1));
  assert(lcc.getDegree() < INF);
  assert(lcc.isSaturated());
}

void flipLits(int128Constr& ic, const soplex::DVectorReal& lpSol) {
  for (Var v : ic.vars) {
    if (lpSol[v] <= 0.5) continue;
    ic.coefs[v] = -ic.coefs[v];
    ic.addRhs(ic.coefs[v]);
  }
  ic.degree = ic._invalid_();
}

CandidateCut LpSolver::createLinearCombinationGomory(soplex::DVectorReal& mults) {
  assert(lcc_unlogged.isReset());
  double mult = getScaleFactor(mults, false);
  std::vector<std::pair<__int128, int>> slacks;

  for (int r = 0; r < mults.dim(); ++r) {
    __int128 factor = mults[r] * mult;
    if (factor == 0) continue;
    rowToConstraint(r);
    if (factor < 0) ic.invert();
    lcc_unlogged.addUp(ic, std::abs(factor));
    ic.reset();
    slacks.emplace_back(-factor, r);
  }

  flipLits(lcc_unlogged, lpSolution);

  __int128 b = lcc_unlogged.getRhs();
  if (b == 0) {
    lcc_unlogged.reset();
    return CandidateCut(lcc_unlogged, lpSolution);
  }

  assert(mult > 0);
  __int128 divisor = mult;
  while ((b % divisor) == 0) ++divisor;
  lcc_unlogged.applyMIR(divisor);

  flipLits(lcc_unlogged, lpSolution);

  // round up the slack variables MIR style and cancel out the slack variables
  for (unsigned i = 0; i < slacks.size(); ++i) {
    __int128 factor = mir_coeff(slacks[i].first, b, divisor);
    if (factor == 0) continue;
    rowToConstraint(slacks[i].second);
    if (factor < 0) ic.invert();
    lcc_unlogged.addUp(ic, std::abs(factor));
    ic.reset();
  }

  lcc_unlogged.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  if (lcc_unlogged.getDegree() <= 0) lcc_unlogged.reset();
  if (lcc_unlogged.getDegree() >= INF) {
    divisor = aux::ceildiv<__int128>(lcc_unlogged.getDegree(), INF - 1);
    for (Var v : lcc_unlogged.vars) {
      __int128 rem = aux::mod_safe(lcc_unlogged.coefs[v], divisor);
      if (rem == 0) continue;
      assert(rem > 0);
      if ((double)divisor * lpSolution[v] < rem)
        lcc_unlogged.weaken(divisor - rem, v);
      else
        lcc_unlogged.weaken(-rem, v);
    }
    lcc_unlogged.divide(divisor);
    lcc_unlogged.saturate();
  }
  assert(lcc_unlogged.getDegree() < INF);
  assert(lcc_unlogged.isSaturated());
  return CandidateCut(lcc_unlogged, lpSolution);
}

void LpSolver::constructGomoryCandidates() {
  std::vector<int> indices;
  indices.resize(getNbRows());
  lp.getBasisInd(indices.data());

  for (int row = 0; row < getNbRows(); ++row) {
    double fractionality = 0;
    if (indices[row] >= 0)  // basic original variable / column
      fractionality = nonIntegrality(lpSolution[indices[row]]);
    else  // basic slack variable / row
      fractionality = nonIntegrality(lpSlackSolution[-indices[row] - 1]);
    if (fractionality == 0) continue;

    lp.getBasisInverseRowReal(row, lpMultipliers.get_ptr());
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    lcc_unlogged.reset();
    if (candidateCuts.back().ratSlack >= -options.tolerance) candidateCuts.pop_back();
    for (int i = 0; i < lpMultipliers.dim(); ++i) lpMultipliers[i] = -lpMultipliers[i];
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    lcc_unlogged.reset();
    if (candidateCuts.back().ratSlack >= -options.tolerance) candidateCuts.pop_back();
  }
}

void LpSolver::constructLearnedCandidates() {
  for (CRef cr : solver.constraints) {
    const Constr& c = solver.ca[cr];
    if (id2row.count(c.id) == 0) {
      candidateCuts.emplace_back(c, cr, lpSolution);
      if (candidateCuts.back().ratSlack >= -options.tolerance) candidateCuts.pop_back();
    }
  }
}

bool LpSolver::addFilteredCuts() {
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
    for (unsigned int j = 0; j < keptCuts.size() && !parallel; ++j)
      parallel = candidateCuts[keptCuts[j]].cosOfAngleTo(candidateCuts[i]) > options.maxCutCos;
    if (!parallel) keptCuts.push_back(i);
  }

  for (int i : keptCuts) {
    auto& cc = candidateCuts[i];
    if (cc.cr == CRef_Undef) {
      solver.tmpConstraint.construct(cc.simpcons);
      if (solver.logger) solver.tmpConstraint.logAsInput();  // TODO: fix
      cc.cr = solver.learnConstraint();
      ++stats.NLPGOMORYCUTS;
    } else
      ++stats.NLPLEARNEDCUTS;
    assert(cc.cr != CRef_Undef);
    if (cc.cr == CRef_Unsat) return false;
    addConstraint(cc.cr, true);
  }
  candidateCuts.clear();
  return true;
}

void LpSolver::pruneCuts() {
  assert(getNbRows() == (int)row2data.size());
  lpMultipliers.clear();
  lp.getDual(lpMultipliers);
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
    // TODO: check opposite construction of Farkas constraint, inverting in case multiplier>0
    if (std::isnan(mults[i]) || (removeNegatives && mults[i] < 0)) mults[i] = 0;  // TODO: report NaN to Ambros?
    if (mults[i] == 0) continue;
    ++nbMults;
    largest = std::max(std::abs(mults[i]), largest);
  }
  assert(nbMults < INF);
  double mult = maxMult / largest / nbMults * INF;
  assert(mult > 0);
  assert(mult <= max128);
  return mult;
}

// BITWISE: -
bool LpSolver::rowToConstraint(int row) {
  assert(ic.isReset());
  double rhs = lp.lhsReal(row);
  assert(std::abs(rhs) != INFTY);
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
  if (ic.plogger) ic.resetBuffer(row2data[row].id);
  return true;
}

bool LpSolver::checkFeasibility(bool inProcessing) {
  if (solver.logger) solver.logger->logComment("checking LP", stats);
  double startTime = aux::cpuTime();
  bool result = _checkFeasibility(inProcessing);
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
  return result;
}

bool LpSolver::inProcess() {
  double startTime = aux::cpuTime();
  bool result = _inProcess();
  stats.LPTOTALTIME += aux::cpuTime() - startTime;
  return result;
}

bool LpSolver::_checkFeasibility(bool inProcessing) {
  if (options.lpPivotRatio < 0)
    lp.setIntParam(soplex::SoPlex::ITERLIMIT, -1);  // no pivot limit
  else if (options.lpPivotRatio * stats.NCONFL < (inProcessing ? stats.NLPPIVOTSROOT : stats.NLPPIVOTSINTERNAL))
    return true;  // pivot ratio exceeded
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
    return true;
  }

  if (stat == soplex::SPxSolver::Status::OPTIMAL) {
    ++stats.NLPOPTIMAL;
    if (!lp.hasSol()) {
      ++stats.NLPNOPRIMAL;
      LP_resetBasis();
    }
    if (lp.numIterations() == 0) ++stats.NLPNOPIVOT;
    return true;
  }

  if (stat == soplex::SPxSolver::Status::ABORT_CYCLING) {
    ++stats.NLPCYCLING;
    LP_resetBasis();
    return true;
  }
  if (stat == soplex::SPxSolver::Status::SINGULAR) {
    ++stats.NLPSINGULAR;
    LP_resetBasis();
    return true;
  }
  if (stat != soplex::SPxSolver::Status::INFEASIBLE) {
    ++stats.NLPOTHER;
    LP_resetBasis();
    return true;
  }

  // Infeasible LP :)
  ++stats.NLPINFEAS;

  // To prove that we have an inconsistency, let's build the Farkas proof
  if (!lp.getDualFarkas(lpMultipliers)) {
    ++stats.NLPNOFARKAS;
    LP_resetBasis();
    return true;
  }

  createLinearCombinationFarkas(lpMultipliers);
  // TODO: asserting case and postprocessing?
  if (lcc.getSlack(solver.getLevel()) >= 0) {
    lcc.copyTo(solver.tmpConstraint);
    lcc.reset();
    solver.learnConstraint();
    return true;
  } else {
    lcc.copyTo(solver.conflConstraint);
    lcc.reset();
    ++stats.NLPFARKAS;
    return false;
  }
}

bool LpSolver::_inProcess() {
  assert(solver.decisionLevel() == 0);
  if (!checkFeasibility(true)) {
    assert(solver.conflConstraint.getSlack(solver.getLevel()) < 0);
    solver.conflConstraint.logInconsistency(solver.getLevel(), solver.getPos(), stats);
    return false;
  }
  if (lp.hasSol()) {
    lp.getPrimal(lpSolution);
    lp.getSlacksReal(lpSlackSolution);
    assert((int)solver.phase.size() == getNbVariables());
    for (Var v = 1; v < getNbVariables(); ++v) solver.phase[v] = (lpSolution[v] <= 0.5) ? -v : v;
    std::cout << "c rational objective " << lp.objValueReal() << std::endl;
    assert(candidateCuts.size() == 0);
    if (solver.logger && (options.addGomoryCuts || options.addLearnedCuts)) solver.logger->logComment("cutting", stats);
    if (options.addGomoryCuts) constructGomoryCandidates();
    if (options.addLearnedCuts) constructLearnedCandidates();
    if (!addFilteredCuts()) return false;
    pruneCuts();
  }
  return true;
}

void LpSolver::LP_resetBasis() {
  ++stats.NLPRESETBASIS;
  lp.clearBasis();  // and hope next iteration works fine
}

void LpSolver::LP_convertConstraint(CRef cr, soplex::DSVectorReal& row, Val& rhs) {
  Constr& C = solver.ca[cr];
  assert(row.max() == (int)C.size());
  rhs = C.degree;
  for (unsigned int i = 0; i < C.size(); ++i) {
    int l = C.lit(i);
    int coef = C.coef(i);
    if (l < 0) {
      rhs -= coef;
      coef = -coef;
    }
    assert(std::abs(l) < lp.numColsReal());
    row.add(std::abs(l), coef);
  }
  assert(validRhs(rhs));
}

void LpSolver::addConstraint(CRef cr, bool removable) {
  ID id = solver.ca[cr].id;
  toRemove.erase(id);
  if (!id2row.count(id) && !toAdd.count(id)) {
    soplex::DSVectorReal row(solver.ca[cr].size());
    Val rhs;
    LP_convertConstraint(cr, row, rhs);
    toAdd[id] = {row, rhs, removable};
  }
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