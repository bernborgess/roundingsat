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

LpSolver::LpSolver(Solver& slvr, const intConstr& o):solver(slvr) {
  if (o.vars.size()==0 && LP_pureCnf()) {
    if (options.verbosity > 1) {
      std::cout << "c Problem is only clausal, disabling LP solving" << std::endl;
    }
    options.lpmulti = 0;  // disables useless LP
    return;               // only clausal constraints
  }

  if (options.verbosity > 1) {
    std::cout << "c Initializing LP" << std::endl;
  }
  lpSolution = soplex::DVectorReal(solver.getNbVars() + 1);
  lowerBounds.reDim(solver.getNbVars() + 1);
  upperBounds.reDim(solver.getNbVars() + 1);
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
  allCols.reMax(solver.getNbVars() + 1);
  soplex::DSVectorReal dummycol(0);
  for (int i = 0; i <= solver.getNbVars(); ++i) allCols.add(soplex::LPColReal(0, dummycol, 1, 0));
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
  objective.reDim(solver.getNbVars() + 1);  // NOTE: automatically set to zero
  if (o.vars.size() > 0) {                  // add objective function
    soplex::DSVectorReal objRow(o.vars.size());
    for (Var v : o.vars) {
      Coef c = std::abs(o.coefs[v]);
      objective[v] = c;
      objRow.add(v, c);
    }
    lp.changeObjReal(objective);
    lp.changeRowReal(0, soplex::LPRowReal(-soplex::infinity, objRow, soplex::infinity));
  } else {  // add default objective function
    for (int v = 1; v <= solver.getNbVars(); ++v) objective[v] = 1;
    lp.changeObjReal(objective);
  }

  if (options.verbosity > 1) std::cout << "c Finished initializing LP" << std::endl;
}

void LpSolver::setNbVariables(int n) {
  // TODO
}

void LpSolver::LP_addConstraints() {
  if (solver.constraints.size() == 0) return;
  soplex::LPRowSetReal allRows;
  allRows.reMax(solver.constraints.size());
  for (CRef cr : solver.constraints) {  // all axioms
    assert(cr != CRef_Undef && cr != CRef_Unsat);
    assert(solver.ca[cr].size() > 0);
    soplex::DSVectorReal row(solver.ca[cr].size());
    Val rhs;
    LP_convertConstraint(cr, row, rhs);
    allRows.add(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs, 0));
  }
  lp.addRowsReal(allRows);
  stats.NLPCONSTRS += solver.constraints.size();
}

void LpSolver::LP_convertConstraint(CRef cr, soplex::DSVectorReal& row, Val& rhs){
	Constr& C = solver.ca[cr];
	assert(row.max()==(int)C.size());
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

bool LpSolver::LP_pureCnf(){
	for(CRef cr: solver.constraints) if(solver.ca[cr].isClause()) return false;
	return true;
}