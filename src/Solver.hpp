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

#include <vector>
#include <iostream>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <csignal>
#include <unordered_map>
#include <memory>

#include "aux.hpp"
#include "typedefs.hpp"
#include "IntSet.hpp"
#include "Constraint.hpp"
#include "Options.hpp"
#include "globals.hpp"
#include "SolverStructs.hpp"

struct Solver {
	// ---------------------------------------------------------------------
	// Members

	ConstraintAllocator ca;
	IntSet tmpSet;
	IntSet actSet;
	intConstr tmpConstraint;
	longConstr conflConstraint; // functions as old confl_data
	intConstr logConstraint;

	int heap_cap=0;
	std::vector<Var> heap_tree = {-1,-1};
	std::vector<CRef> constraints;
	std::unordered_map<ID,CRef> external;
	std::vector<std::vector<Watch>> _adj={{}}; std::vector<std::vector<Watch>>::iterator adj;
	std::vector<int> _Level={-1}; IntVecIt Level;
	std::vector<Lit> trail;
	std::vector<int> trail_lim, Pos;
	std::vector<CRef> Reason;
	int qhead=0; // for unit propagation
	std::vector<Lit> phase;
	std::vector<double> activity;
	inline int decisionLevel() { return trail_lim.size(); }

	long long nbconstrsbeforereduce=2000;
	long long nconfl_to_restart=0;
	double v_vsids_inc=1.0;
	double c_vsids_inc=1.0;

	// ---------------------------------------------------------------------
	// Initialization

	Solver();
	void setNbVariables(long long nvars);

	// ---------------------------------------------------------------------
	// VSIDS

	// segment tree (fast implementation of priority queue).
	void heap_resize(int newsize); // TODO: make this heap its own data structure
	void heap_percolateUp(Var x);
	bool heap_empty();
	bool heap_inHeap(Var x);
	void heap_insert(Var x);
	Var heap_removeMax();

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
 * @post: all watches up to trail[qhead] have been propagated
 */
	CRef runPropagation();

	// ---------------------------------------------------------------------
	// Conflict analysis

	void recomputeLBD(Constr& C);
	bool analyze(CRef confl);
	template<class SMALL, class LARGE>
	LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core){
		LARGE slack = -core.getRhs();
		for(Var v: core.vars) if(assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v]>0)) slack+=core.coefs[v];
		return slack;
	}
	bool extractCore(const IntSet& assumptions, CRef confl, intConstr& outCore, Lit l_assump=0);

	// ---------------------------------------------------------------------
	// Constraint management

	CRef attachConstraint(intConstr& constraint, ConstraintType type);
	bool learnConstraint(longConstr& confl);
	ID addInputConstraint(ConstraintType type);
	ID addConstraint(const intConstr& c, ConstraintType type);
	ID addConstraint(const std::vector<Coef>& coefs, const std::vector<Lit>& lits, const Val rhs, ConstraintType type);
	void removeConstraint(Constr& C);
	void dropExternal(ID id, bool forceDelete);

	// ---------------------------------------------------------------------
	// Garbage collection

	// We assume in the garbage collection method that reduceDB() is the
	// only place where constraints are deleted.
	void garbage_collect();
	void reduceDB();

	// ---------------------------------------------------------------------
	// Solving

	double luby(double y, int i);
	Val lhs(Constr& C, const std::vector<bool>& sol);
	bool checksol(const std::vector<bool>& sol);
	Lit pickBranchLit();
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

};