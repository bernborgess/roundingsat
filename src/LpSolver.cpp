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

LpSolver::LpSolver(Solver& slvr, const intConstr& o) : solver(slvr) {
  assert(INFTY == lp.realParam(lp.INFTY));
  if (o.vars.size() == 0 && LP_pureCnf()) {
    if (options.verbosity > 1) std::cout << "c Problem is only clausal, disabling LP solving" << std::endl;
    options.lpmulti = 0;  // disables useless LP
    return;               // only clausal constraints
  }

  if (options.verbosity > 1) std::cout << "c Initializing LP" << std::endl;
  setNbVariables(solver.getNbVars() + 1);
  lp.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_ONLYREAL);
  lp.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_REAL);
  lp.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_REAL);
  lp.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_OFF);
  lp.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
  lp.setIntParam(soplex::SoPlex::VERBOSITY, options.verbosity);
  // NOTE: alternative "crash basis" only helps on few instances, according to Ambros, so we don't adjust that parameter

  // first add variables
  // NOTE: batch version is more efficient than adding them one by one
  soplex::LPColSetReal allCols;
  allCols.reMax(getNbVariables());
  soplex::DSVectorReal dummycol(0);
  for (Var v = 0; v < getNbVariables(); ++v) allCols.add(soplex::LPColReal(0, dummycol, 1, 0));
  lp.addColsReal(allCols);

  // NOTE: batch version is more efficient than adding them one by one
  LP_addConstraints();

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
  if (o.vars.size() > 0) {            // add objective function
    soplex::DSVectorReal objRow(o.vars.size());
    for (Var v : o.vars) {
      Coef c = std::abs(o.coefs[v]);
      objective[v] = c;
      objRow.add(v, c);
    }
    lp.changeObjReal(objective);
    lp.changeRowReal(0, soplex::LPRowReal(-soplex::infinity, objRow, soplex::infinity));
  } else {  // add default objective function
    for (int v = 1; v < getNbVariables(); ++v) objective[v] = 1;
    lp.changeObjReal(objective);
  }

  if (options.verbosity > 1) std::cout << "c Finished initializing LP" << std::endl;
  if (solver.logger) {
    ic.initializeLogging(solver.logger);
    lcc.initializeLogging(solver.logger);
  }
}

void LpSolver::setNbVariables(int n) {
  lpSolution = soplex::DVectorReal(n);
  lcc.resize(n);
  ic.resize(n);
  lowerBounds.reDim(n);
  upperBounds.reDim(n);
}
int LpSolver::getNbVariables() const { return lpSolution.dim(); }

// BITWISE: -
void LpSolver::createLinearCombinationFarkas(soplex::DVectorReal& mults) {
  assert(lcc.isReset());
  double mult = getScaleFactor(mults);

  for (int r = 0; r < mults.dim(); ++r) {
    if (mults[r] == 0) continue;
    rowToConstraint(r, mults[r] < 0);  // NOTE: negative values for upper bounded constraints (rhs)
    lcc.addUp(solver.getLevel(), ic, mults[r] * mult, 1, false);
    ic.reset();
  }
  lcc.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), true);
  if (lcc.getDegree() >= INF) lcc.roundToOne(solver.getLevel(), aux::ceildiv<__int128>(lcc.getDegree(), INF - 1), true);
  assert(lcc.getDegree() < INF);
  assert(lcc.isSaturated());
}

// BITWISE: +log2(maxMult)+log2(1e9) // TODO: check BITWISE
// @return: multiplier fitting in positive bigint range, s.t. multiplier*largestV <= max128*INF/nbMults
// @post: no NaN or negative mults (if onlyPositive)
// NOTE: it is possible that mults are negative (e.g., when calculating Gomory cuts)
double LpSolver::getScaleFactor(soplex::DVectorReal& mults) {
  const double max128 = 1e37;  // NOTE: std::numeric_limits<bigint>::max() // TODO: 1e38?
  int nbMults = 0;
  double largestV = maxMult / max128;
  assert(maxMult / largestV <= max128);
  for (int i = 0; i < mults.dim(); ++i) {
    // TODO: check opposite construction of Farkas constraint, inverting in case multiplier>0
    if (std::isnan(mults[i]) || (mults[i] < 0 && lp.rhsReal(i) == INFTY) || (mults[i] > 0 && lp.lhsReal(i) == -INFTY))
      mults[i] = 0;  // TODO: report NaN to Ambros?
    if (mults[i] != 0) {
      ++nbMults;
      if (std::abs(mults[i]) > largestV) largestV = std::abs(mults[i]);
    }
  }
  assert(nbMults < INF);
  double mult = maxMult / largestV / nbMults * INF;
  assert(mult > 0);
  assert(mult <= max128);
  return mult;
}

// BITWISE: -
bool LpSolver::rowToConstraint(int row, bool negated) {
  assert(ic.isReset());
  double rhs = negated ? lp.rhsReal(row) : lp.lhsReal(row);
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
  if (negated) ic.invert();
  if (ic.plogger) ic.resetBuffer(negated ? row2ids[row].second : row2ids[row].first);
  return true;
}

bool LpSolver::checkFeasibility(bool inProcessing) {
  if (!inProcessing && options.lpmulti >= 0) {
    // explanation of formula:
    // start at 1 to allow initial LP search
    // allow as many (total) pivots as weighted conflict count
    // subtract total pivots so far
    // each call to LP solver also counts as a pivot, to reduce number of feasibility calls (that have 0 pivot count)
    long long allowed = ceil(options.lpmulti * (1 + stats.NCONFL) - stats.NLPPIVOTS - stats.NLPCALLS);
    if (allowed <= 0)
      return true;  // no pivot budget available
    else
      lp.setIntParam(soplex::SoPlex::ITERLIMIT, allowed + 100);  // limit number of pivots
    // NOTE: when triggered, allow the LP at least 100 pivots to run.
    // This value is conservative: in benchmarks, SCIP has 382 (median) and 1391 (average) pivots / soplex call.
  }  // else, no pivot limit

  // Set the  LP's bounds based on the current trail
  for (Var v = 1; v < getNbVariables(); ++v) {
    lowerBounds[v] = 0;
    upperBounds[v] = 1;
    if (isTrue(solver.getLevel(), v)) lowerBounds[v] = 1;
    if (isTrue(solver.getLevel(), -v)) upperBounds[v] = 0;
  }
  lp.changeBoundsReal(lowerBounds, upperBounds);

  // Run the LP
  soplex::SPxSolver::Status stat;
	stat = lp.optimize();
  ++stats.NLPCALLS;
  stats.NLPPIVOTS += lp.numIterations();
  stats.LPSOLVETIME += lp.solveTime();

  if (options.verbosity > 1) std::cout << "c LP status: " << stat << std::endl;
  assert(stat != soplex::SPxSolver::Status::NO_PROBLEM);
  assert(stat <= soplex::SPxSolver::Status::OPTIMAL_UNSCALED_VIOLATIONS);
  assert(stat >= soplex::SPxSolver::Status::ERROR);

  if (stat == soplex::SPxSolver::Status::ABORT_ITER) return true;

  if (stat == soplex::SPxSolver::Status::OPTIMAL) {
    ++stats.NLPOPTIMAL;
    if (lp.numIterations() == 0) {
      ++stats.NLPNOPIVOT;
      return true;
    }  // no use calculating solution if it is not changed
    if (!lp.hasSol()) {
      ++stats.NLPNOPRIMAL;
      LP_resetBasis();
      return true;
    }
    if (inProcessing) {
      lp.getPrimalReal(lpSolution);
      foundLpSolution = true;
      assert((int)solver.phase.size() >= getNbVariables());
      for (Var v = 1; v < getNbVariables(); ++v) solver.phase[v] = (lpSolution[v] <= 0.5) ? -v : v;
      std::cout << "c rational objective " << lp.objValueReal() << std::endl;
    }
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
  if (!lp.hasDualFarkas()) {
    ++stats.NLPNOFARKAS;
    LP_resetBasis();
    return true;
  }

  lpMultipliers.reDim(lp.numRowsReal());
  lp.getDualFarkasReal(lpMultipliers);

  createLinearCombinationFarkas(lpMultipliers);
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

bool LpSolver::inProcess() {
  return checkFeasibility(true);
  // TODO: implement cut generation
}

void LpSolver::LP_resetBasis() {
  ++stats.NLPRESETBASIS;
  lp.clearBasis();  // and hope next iteration works fine
}

void LpSolver::LP_addConstraints() {
  if (solver.constraints.size() == 0) return;
  soplex::LPRowSetReal allRows;
  allRows.reMax(solver.constraints.size());
  row2ids.reserve(solver.constraints.size());
  for (CRef cr : solver.constraints) {  // all axioms
    assert(cr != CRef_Undef && cr != CRef_Unsat);
    assert(solver.ca[cr].size() > 0);
    soplex::DSVectorReal row(solver.ca[cr].size());
    Val rhs;
    LP_convertConstraint(cr, row, rhs);
    allRows.add(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs));
    row2ids.emplace_back(solver.ca[cr].id, ID_Undef);
  }
  lp.addRowsReal(allRows);
  stats.NLPCONSTRS += solver.constraints.size();
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
    row.add(std::abs(l), coef);
  }
  assert(validRhs(rhs));
}

bool LpSolver::LP_pureCnf() {
  for (CRef cr : solver.constraints)
    if (solver.ca[cr].isClause()) return false;
  return true;
}