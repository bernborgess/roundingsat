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

#include <memory>
#include "IntSet.hpp"
#include "LpSolver.hpp"
#include "Options.hpp"
#include "SolverStructs.hpp"
#include "typedefs.hpp"

namespace rs {

class Logger;

enum SolveState { SAT, UNSAT, INCONSISTENT, INPROCESSED, RESTARTED };

class Solver {
  friend class LpSolver;
  friend class Constr;
  friend class Clause;
  friend class Cardinality;
  template <typename CF, typename DG>
  friend class Counting;
  template <typename CF, typename DG>
  friend class Watched;
  friend class Arbitrary;

  // ---------------------------------------------------------------------
  // Members

 public:
  std::shared_ptr<Logger> logger;
  ConstrExpPools cePools;

 private:
  int n;
  int orig_n;
  ID crefID = ID_Trivial;

  ConstraintAllocator ca;
  IntSet tmpSet;
  IntSet actSet;
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
  std::vector<ActValV> activity;

  long long nconfl_to_reduce = 2000;
  long long nconfl_to_restart = 0;
  ActValV v_vsids_inc = 1.0;
  ActValC c_vsids_inc = 1.0;

  bool firstRun = true;

  std::shared_ptr<LpSolver> lpSolver;
  std::vector<std::unique_ptr<ConstrSimpleSuper>> learnedStack;

 public:
  Solver();
  void init();  // call after having read options
  void initLP(const CeArb objective);

  int getNbVars() const { return n; }
  void setNbVars(long long nvars, bool orig = false);
  int getNbOrigVars() const { return orig_n; }

  const IntVecIt& getLevel() const { return Level; }
  const std::vector<int>& getPos() const { return Pos; }
  int decisionLevel() const { return trail_lim.size(); }

  std::pair<ID, ID> addConstraint(const CeSuper c, Origin orig);             // formula line id, processed id
  std::pair<ID, ID> addConstraint(const ConstrSimpleSuper& c, Origin orig);  // formula line id, processed id
  void dropExternal(ID id, bool erasable, bool forceDelete);
  int getNbConstraints() const { return constraints.size(); }
  CeSuper getIthConstraint(int i) { return ca[constraints[i]].toExpanded(cePools); }

  /**
   * @return 1:
   * 	UNSAT if root inconsistency detected
   * 	SAT if satisfying assignment found
   * 	INCONSISTENT if no solution extending assumptions exists
   * 	INPROCESSING if solver just finished a cleanup phase
   * @return 2:
   *    an implied constraint C if INCONSISTENT
   *        if C is a tautology, negated assumptions at root level exist
   *        if C is not a tautology, it is falsified by the assumptions
   * @param assumptions: set of assumptions
   * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
   */
  std::pair<SolveState, CeSuper> solve(const IntSet& assumptions, std::vector<bool>& solution);

 private:
  void presolve();

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
   * @return: true if inconsistency is detected, false otherwise. The inconsistency is stored in confl->
   */
  CeSuper runPropagation(bool onlyUnitPropagation);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  void recomputeLBD(Constr& C);
  CeSuper analyze(CeSuper confl);
  CeSuper extractCore(CeSuper confl, const IntSet& assumptions, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  CRef attachConstraint(CeSuper constraint, bool locked);
  void learnConstraint(const CeSuper c, Origin orig);
  CeSuper processLearnedStack();
  std::pair<ID, ID> addInputConstraint(CeSuper ce);
  void removeConstraint(Constr& C, bool override = false);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect();
  void reduceDB();

  // ---------------------------------------------------------------------
  // Solving

  double luby(double y, int i);
  BigVal lhs(Constr& C, const std::vector<bool>& sol);
  bool checksol(const std::vector<bool>& sol);
  Lit pickBranchLit();
};

}  // namespace rs
