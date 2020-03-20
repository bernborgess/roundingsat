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

#include <algorithm>
#include <cassert>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <memory>
#include <unordered_map>
#include <vector>

#include "Constraint.hpp"
#include "IntSet.hpp"
#include "Options.hpp"
#include "SolverStructs.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

enum SolveState { SAT, UNSAT, INCONSISTENT, INTERRUPTED, INPROCESSED, RESTARTED };
enum WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };

class Solver {
  // ---------------------------------------------------------------------
  // Members
 private:
  int n;
  int orig_n;

  std::shared_ptr<Logger> logger;
  ID crefID = 0;

  ConstraintAllocator ca;
  IntSet tmpSet;
  IntSet actSet;
  intConstr tmpConstraint;
  longConstr conflConstraint;  // functions as old confl_data
  intConstr logConstraint;
  OrderHeap order_heap;

  std::vector<CRef> constraints;
  std::unordered_map<ID, CRef> external;
  std::vector<std::vector<Watch>> _adj = {{}};
  std::vector<std::vector<Watch>>::iterator adj;
  std::vector<int> _Level = {INF};
  IntVecIt Level;  // TODO: make Pos, Level, contiguous memory for better cache efficiency.
  std::vector<Lit> trail;
  std::vector<int> trail_lim, Pos;
  std::vector<CRef> Reason;
  int qhead = 0;  // for unit propagation
  std::vector<Lit> phase;
  std::vector<double> activity;

  long long nbconstrsbeforereduce = 2000;
  long long nconfl_to_restart = 0;
  double v_vsids_inc = 1.0;
  double c_vsids_inc = 1.0;

 public:
  Solver();
  void setLogger(std::shared_ptr<Logger> lgr);

  int getNbVars() const { return n; }
  void setNbVars(long long nvars);
  int getNbOrigVars() const { return orig_n; }
  void setNbOrigVars(int o_n) { orig_n = o_n; }

  const IntVecIt& getLevel() const { return Level; }
  const std::vector<int>& getPos() const { return Pos; }
  int decisionLevel() const { return trail_lim.size(); }

  ID addConstraint(const intConstr& c, ConstraintType type);
  ID addConstraint(const std::vector<Coef>& coefs, const std::vector<Lit>& lits, const Val rhs, ConstraintType type);
  void dropExternal(ID id, bool forceDelete);
  int getNbConstraints() const { return constraints.size(); }
  void getIthConstraint(int i, intConstr& out) const { return ca[constraints[i]].toConstraint(out); }

  /**
   * @return:
   * 	UNSAT if root inconsistency detected
   * 	SAT if satisfying assignment found
   * 	INCONSISTENT if no solution extending assumptions exists
   * 	INTERRUPTED if interrupted by external signal
   * 	INPROCESSING if solver just finished a cleanup phase
   * @param assumptions: set of assumptions
   * @param core: if INCONSISTENT, implied constraint falsified by assumptions, otherwise untouched
   * 	if core is the empty constraint, at least one assumption is falsified at root
   * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
   */
  SolveState solve(const IntSet& assumptions, intConstr& core, std::vector<bool>& solution);

 private:
  // ---------------------------------------------------------------------
  // VSIDS

  void vDecayActivity();
  void vBumpActivity(Var v);
  void cDecayActivity();
  void cBumpActivity(Constr& c);

  // ---------------------------------------------------------------------
  // Trail manipulation

  void uncheckedEnqueue(Lit p, CRef from);
  void undoOne();
  void backjumpTo(int level);
  void decide(Lit l);
  void propagate(Lit l, CRef reason);
  /**
   * Unit propagation with watched literals.
   * @post: all constraints have been checked for propagation under trail[0..qhead[
   */
  CRef runPropagation();
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  void recomputeLBD(Constr& C);
  bool analyze(CRef confl);
  template <class SMALL, class LARGE>
  LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core) {
    LARGE slack = -core.getRhs();
    for (Var v : core.vars)
      if (assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v] > 0)) slack += core.coefs[v];
    return slack;
  }
  bool extractCore(const IntSet& assumptions, CRef confl, intConstr& outCore, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  CRef attachConstraint(intConstr& constraint, ConstraintType type);
  bool learnConstraint(longConstr& confl);
  ID addInputConstraint(ConstraintType type);
  void removeConstraint(Constr& C);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect();
  void reduceDB();

  // ---------------------------------------------------------------------
  // Solving

  double luby(double y, int i);
  Val lhs(Constr& C, const std::vector<bool>& sol);
  bool checksol(const std::vector<bool>& sol);
  Lit pickBranchLit();
};