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

#include "Solver.hpp"
#include <cmath>
#include "Constr.hpp"
#include "aux.hpp"
#include "globals.hpp"

// ---------------------------------------------------------------------
// Initialization

Solver::Solver() : conflConstraint(cePools.takeArb()), order_heap(activity) {
  ca.capacity(1024 * 1024);  // 4MB
}

Solver::~Solver() { conflConstraint.release(); }

void Solver::setNbVars(long long nvars) {
  assert(nvars > 0);
  assert(nvars < INF);
  if (nvars <= n) return;
  aux::resizeIntMap(_adj, adj, nvars, options.resize_factor, {});
  aux::resizeIntMap(_Level, Level, nvars, options.resize_factor, INF);
  Pos.resize(nvars + 1, INF);
  Reason.resize(nvars + 1, CRef_Undef);
  activity.resize(nvars + 1, 1 / actLimitV);
  phase.resize(nvars + 1);
  cePools.resize(nvars + 1);
  assert(conflConstraint.coefs.size() == (size_t)nvars + 1);
  order_heap.resize(nvars + 1);
  for (Var v = n + 1; v <= nvars; ++v) phase[v] = -v, order_heap.insert(v);
  if (lpSolver) lpSolver->setNbVariables(nvars + 1);
  n = nvars;
  stats.NAUXVARS = n - orig_n;
}

void Solver::setNbOrigVars(int o_n) {
  orig_n = o_n;
  stats.NORIGVARS = n;
  stats.NAUXVARS = n - orig_n;
}

void Solver::init() {
  if (!options.proofLogName.empty()) logger = std::make_shared<Logger>(options.proofLogName);
  cePools.initializeLogging(logger);
}

void Solver::initLP(const ConstrExpArb& objective) {
  if (options.lpPivotRatio == 0) return;
  bool pureCNF = objective.vars.size() == 0;
  for (CRef cr : constraints) {
    if (!pureCNF) break;
    pureCNF = (ca[cr].degree() == 1);
  }
  if (pureCNF) return;
  lpSolver = std::make_shared<LpSolver>(*this, objective);
}

// ---------------------------------------------------------------------
// VSIDS

void Solver::vDecayActivity() { v_vsids_inc *= (1 / options.v_vsids_decay); }
void Solver::vBumpActivity(Var v) {
  assert(v > 0);
  if ((activity[v] += v_vsids_inc) > actLimitV) {  // Rescale
    for (Var x = 1; x <= n; ++x) {
      activity[x] /= actLimitV;
      activity[x] /= actLimitV;
    }
    v_vsids_inc /= actLimitV;
    v_vsids_inc /= actLimitV;
  }
  // Update heap with respect to new activity:
  if (order_heap.inHeap(v)) order_heap.percolateUp(v);
}

void Solver::cDecayActivity() { c_vsids_inc *= (1 / options.c_vsids_decay); }
void Solver::cBumpActivity(Constr& c) {
  c.act += c_vsids_inc;
  if (c.act > actLimitC) {  // Rescale:
    for (size_t i = 0; i < constraints.size(); i++) {
      ca[constraints[i]].act /= actLimitC;
      ca[constraints[i]].act /= actLimitC;
    }
    c_vsids_inc /= actLimitC;
    c_vsids_inc /= actLimitC;
  }
}

// ---------------------------------------------------------------------
// Assignment manipulation

void Solver::uncheckedEnqueue(Lit p, CRef from) {
  assert(!isTrue(Level, p));
  assert(!isFalse(Level, p));
  assert(isUnknown(Pos, p));
  Var v = toVar(p);
  Reason[v] = from;
  if (decisionLevel() == 0) {
    Reason[v] = CRef_Undef;  // no need to keep track of reasons for unit literals
    if (logger) {
      Constr& C = ca[from];
      ConstrExpSuper& logConstraint = C.toExpanded(cePools);
      logConstraint.logUnit(Level, Pos, v, stats);
      logConstraint.release();
      assert(logger->unitIDs.size() == trail.size() + 1);
    }
  }
  Level[p] = decisionLevel();
  Pos[v] = (int)trail.size();
  trail.push_back(p);
}

void Solver::undoOne() {
  assert(!trail.empty());
  ++stats.NTRAILPOPS;
  Lit l = trail.back();
  if (qhead == (int)trail.size()) {
    for (const Watch& w : adj[-l])
      if (w.idx >= INF) ca[w.cref].undoFalsified(w.idx);
    --qhead;
  }
  Var v = toVar(l);
  trail.pop_back();
  Level[l] = INF;
  Pos[v] = INF;
  phase[v] = l;
  if (!trail_lim.empty() && trail_lim.back() == (int)trail.size()) trail_lim.pop_back();
  order_heap.insert(v);
}

void Solver::backjumpTo(int level) {
  assert(level >= 0);
  while (decisionLevel() > level) undoOne();
}

void Solver::decide(Lit l) {
  ++stats.NDECIDE;
  trail_lim.push_back(trail.size());
  uncheckedEnqueue(l, CRef_Undef);
}

void Solver::propagate(Lit l, CRef reason) {
  assert(reason != CRef_Undef);
  ++stats.NPROP;
  uncheckedEnqueue(l, reason);
}

/**
 * Unit propagation with watched literals.
 * @post: all watches up to trail[qhead] have been propagated
 */
bool Solver::runPropagation(ConstrExpArb& confl, bool onlyUnitPropagation) {
  assert(confl.isReset());
  while (qhead < (int)trail.size()) {
    Lit p = trail[qhead++];
    std::vector<Watch>& ws = adj[-p];
    for (int it_ws = 0; it_ws < (int)ws.size(); ++it_ws) {
      int idx = ws[it_ws].idx;
      if (idx < 0 && isTrue(Level, idx + INF)) {
        assert(dynamic_cast<Clause*>(&(ca[ws[it_ws].cref])) != nullptr);
        continue;
      }  // blocked literal check
      CRef cr = ws[it_ws].cref;
      WatchStatus wstat = checkForPropagation(cr, ws[it_ws].idx, -p);
      if (wstat == WatchStatus::DROPWATCH)
        aux::swapErase(ws, it_ws--);
      else if (wstat == WatchStatus::CONFLICTING) {  // clean up current level and stop propagation
        ++stats.NTRAILPOPS;
        for (int i = 0; i <= it_ws; ++i) {
          const Watch& w = ws[i];
          if (w.idx >= INF) ca[w.cref].undoFalsified(w.idx);
        }
        --qhead;
        Constr& C = ca[cr];
        if (!C.isLocked()) {
          cBumpActivity(C);
          recomputeLBD(C);
        }
        ConstrExpSuper& tmp = C.toExpanded(cePools);
        tmp.copyTo(confl);
        tmp.release();
        return false;
      }
    }
  }
  if (onlyUnitPropagation) return true;
  if (lpSolver) {
    return lpSolver->checkFeasibility(confl) != INFEASIBLE;
  }
  return true;
}

WatchStatus Solver::checkForPropagation(CRef cr, int& idx, Lit p) {
  assert(isFalse(Level, p));
  Constr& C = ca[cr];
  if (C.isMarkedForDelete()) return WatchStatus::DROPWATCH;
  ++stats.NWATCHLOOKUPS;

  return C.checkForPropagation(cr, idx, p, *this);
}

// ---------------------------------------------------------------------
// Conflict analysis

void Solver::recomputeLBD(Constr& C) {
  if (C.lbd() > 2) {  // constraints with LBD <= 2 won't have score recomputed
    assert(tmpSet.size() == 0);
    for (int i = 0; i < (int)C.size(); i++)
      if (isFalse(Level, C.lit(i))) tmpSet.add(Level[-C.lit(i)]);
    if (C.lbd() > tmpSet.size() + 1) C.setLBD(tmpSet.size());  // simulate Glucose
    tmpSet.reset();
  }
}

ConstrExpSuper& getAnalysisCE(const ConstrExpSuper& conflict, int bitsOverflow, ConstrExpPools& cePools) {
  if (bitsOverflow <= conflLimit32) {
    ConstrExp32& confl = cePools.take32();
    conflict.copyTo(confl);
    return confl;
  } else if (options.bitsOverflow <= conflLimit64) {
    ConstrExp64& confl = cePools.take64();
    conflict.copyTo(confl);
    return confl;
  } else if (options.bitsOverflow <= conflLimit96) {
    ConstrExp96& confl = cePools.take96();
    conflict.copyTo(confl);
    return confl;
  } else {
    ConstrExpArb& confl = cePools.takeArb();
    conflict.copyTo(confl);
    return confl;
  }
}

bool Solver::analyze(ConstrExpArb& conflict) {
  if (logger) logger->logComment("Analyze", stats);
  assert(conflict.hasNegativeSlack(Level));
  stats.NADDEDLITERALS += conflict.vars.size();
  conflict.removeUnitsAndZeroes(Level, Pos);
  conflict.saturateAndFixOverflow(getLevel(), options.weakenFull, options.bitsOverflow, options.bitsReduced);

  ConstrExpSuper& confl = getAnalysisCE(conflict, options.bitsOverflow, cePools);
  conflict.reset();

  assert(actSet.size() == 0);  // will hold the literals that need their activity bumped
  for (Var v : confl.vars) {
    if (!options.bumpOnlyFalse || isFalse(Level, confl.getLit(v))) actSet.add(v);
  }
  while (decisionLevel() > 0) {
    if (asynch_interrupt) {
      confl.release();
      return false;
    }
    Lit l = trail.back();
    if (confl.hasLit(-l)) {
      assert(confl.hasNegativeSlack(Level));
      AssertionStatus status = confl.isAssertingBefore(Level, decisionLevel());
      if (status == AssertionStatus::ASSERTING)
        break;
      else if (status == AssertionStatus::FALSIFIED) {
        backjumpTo(decisionLevel() - 1);
        assert(confl.hasNegativeSlack(Level));
        continue;
      }
      assert(Reason[toVar(l)] != CRef_Undef);
      Constr& reasonC = ca[Reason[toVar(l)]];
      if (!reasonC.isLocked()) {
        cBumpActivity(reasonC);
        recomputeLBD(reasonC);
      }

      stats.NENCFORMULA += reasonC.getOrigin() == Origin::FORMULA;
      stats.NENCLEARNED += reasonC.getOrigin() == Origin::LEARNED;
      stats.NENCBOUND += reasonC.getOrigin() == Origin::BOUND;
      stats.NENCCOREGUIDED += reasonC.getOrigin() == Origin::COREGUIDED;
      stats.NLPENCGOMORY += reasonC.getOrigin() == Origin::GOMORY;
      stats.NLPENCLEARNEDFARKAS += reasonC.getOrigin() == Origin::LEARNEDFARKAS;
      stats.NLPENCFARKAS += reasonC.getOrigin() == Origin::FARKAS;
      ++stats.NRESOLVESTEPS;
      reasonC.resolveWith(confl, l, &actSet, *this);
    }
    undoOne();
  }
  assert(confl.hasNegativeSlack(Level));
  for (Lit l : actSet.keys)
    if (l != 0) vBumpActivity(toVar(l));
  actSet.reset();

  confl.copyTo(conflict);
  confl.release();
  return true;
}

bool Solver::extractCore(ConstrExpArb& conflict, const IntSet& assumptions, ConstrExpArb& outCore, Lit l_assump) {
  assert(!conflict.isReset());
  assert(outCore.isReset());

  if (l_assump != 0) {  // l_assump is an assumption propagated to the opposite value
    assert(assumptions.has(l_assump));
    assert(isFalse(Level, l_assump));
    int pos = Pos[toVar(l_assump)];
    while ((int)trail.size() > pos) undoOne();
    assert(isUnknown(Pos, l_assump));
    decide(l_assump);
  }

  // Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
  // For this, we first copy the trail, then backjump to 0, then rebuild the trail.
  // Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
  std::vector<Lit> decisions;  // holds the decisions
  decisions.reserve(decisionLevel());
  std::vector<Lit> props;  // holds the propagations
  props.reserve(trail.size());
  assert(trail_lim.size() > 0);
  for (int i = trail_lim[0]; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (assumptions.has(l))
      decisions.push_back(l);
    else
      props.push_back(l);
  }
  backjumpTo(0);

  for (Lit l : decisions) decide(l);
  for (Lit l : props) propagate(l, Reason[toVar(l)]);

  stats.NADDEDLITERALS += conflict.vars.size();
  conflict.removeUnitsAndZeroes(Level, Pos);
  conflict.saturateAndFixOverflow(getLevel(), options.weakenFull, options.bitsOverflow, options.bitsReduced);
  assert(conflict.hasNegativeSlack(Level));

  ConstrExpSuper& confl = getAnalysisCE(conflict, options.bitsOverflow, cePools);
  conflict.reset();

  // analyze conflict
  while (decisionLevel() > 0) {
    if (asynch_interrupt) return false;
    Lit l = trail.back();
    if (confl.hasLit(-l)) {
      if (confl.hasNegativeSlack(assumptions)) break;
      assert(Reason[toVar(l)] != CRef_Undef);
      Constr& reasonC = ca[Reason[toVar(l)]];
      // TODO: stats? activity?
      reasonC.resolveWith(confl, l, nullptr, *this);
    }
    undoOne();
  }
  assert(confl.hasNegativeSlack(assumptions));
  assert(!confl.isTautology());
  assert(confl.isSaturated());
  confl.copyTo(outCore);
  confl.release();

  // weaken non-falsifieds
  for (Var v : outCore.vars)
    if (!assumptions.has(-outCore.getLit(v))) outCore.weaken(-outCore.coefs[v], v);
  outCore.postProcess(Level, Pos, true, stats);
  assert(outCore.getSlack(assumptions) < 0);
  backjumpTo(0);
  return true;
}

// ---------------------------------------------------------------------
// Constraint management

CRef Solver::attachConstraint(ConstrExpSuper& constraint, bool locked) {
  assert(constraint.isSortedInDecreasingCoefOrder());
  assert(constraint.isSaturated());
  assert(constraint.hasNoZeroes());
  assert(constraint.hasNoUnits(getLevel()));
  assert(!constraint.isTautology());
  assert(constraint.vars.size() > 0);
  assert(!constraint.hasNegativeSlack(getLevel()));
  assert(constraint.orig != Origin::UNKNOWN);

  CRef cr = constraint.toConstr(ca, locked, logger ? constraint.logProofLineWithInfo("Attach", stats) : ++crefID);
  Constr& C = ca[cr];
  C.initializeWatches(cr, *this);
  constraints.push_back(cr);

  bool learned = (C.getOrigin() == Origin::LEARNED || C.getOrigin() == Origin::LEARNEDFARKAS ||
                  C.getOrigin() == Origin::FARKAS || C.getOrigin() == Origin::GOMORY);
  if (learned) {
    stats.LEARNEDLENGTHSUM += C.size();
    stats.LEARNEDDEGREESUM += C.degree();
  } else {
    stats.EXTERNLENGTHSUM += C.size();
    stats.EXTERNDEGREESUM += C.degree();
  }
  if (C.degree() == 1) {
    stats.NCLAUSESLEARNED += learned;
    stats.NCLAUSESEXTERN += !learned;
  } else if (C.largestCoef() == 1) {
    stats.NCARDINALITIESLEARNED += learned;
    stats.NCARDINALITIESEXTERN += !learned;
  } else {
    stats.NGENERALSLEARNED += learned;
    stats.NGENERALSEXTERN += !learned;
  }

  stats.NCONSFORMULA += C.getOrigin() == Origin::FORMULA;
  stats.NCONSLEARNED += C.getOrigin() == Origin::LEARNED;
  stats.NCONSBOUND += C.getOrigin() == Origin::BOUND;
  stats.NCONSCOREGUIDED += C.getOrigin() == Origin::COREGUIDED;
  stats.NLPGOMORYCUTS += C.getOrigin() == Origin::GOMORY;
  stats.NLPLEARNEDFARKAS += C.getOrigin() == Origin::LEARNEDFARKAS;
  stats.NLPFARKAS += C.getOrigin() == Origin::FARKAS;

  return cr;
}

void Solver::learnConstraint(const ConstrExpSuper& c, Origin orig) {
  assert(orig == Origin::LEARNED || orig == Origin::FARKAS || orig == Origin::LEARNEDFARKAS || orig == Origin::GOMORY);
  ConstrExpSuper& learned = c.reduce(cePools);
  learned.orig = orig;
  learned.saturateAndFixOverflow(getLevel(), options.weakenFull, options.bitsLearned, options.bitsLearned);
  learnedStack.push_back(learned.toSimple());
  learned.release();
}

// NOTE: backjumps to place where the constraint is not conflicting, as otherwise we might miss propagations
CRef Solver::processLearnedStack() {
  // loop back to front as the last constraint in the queue is a result of conflict analysis
  // and we want to first check this constraint to backjump.
  while (learnedStack.size() > 0) {
    ConstrExpSuper& learned = learnedStack.back()->toExpanded(cePools);
    learnedStack.pop_back();
    learned.removeUnitsAndZeroes(Level, Pos, true);
    learned.sortInDecreasingCoefOrder();
    int assertionLevel = learned.getAssertionLevel(Level, Pos);
    if (assertionLevel < 0) {
      backjumpTo(0);
      assert(learned.hasNegativeSlack(Level));
      if (logger) learned.logInconsistency(Level, Pos, stats);
      learned.release();
      return CRef_Unsat;
    }
    backjumpTo(assertionLevel);
    assert(!learned.hasNegativeSlack(Level));
    learned.heuristicWeakening(Level, Pos, stats);  // TODO: don't always weaken heuristically?
    learned.postProcess(Level, Pos, false, stats);
    assert(learned.isSaturated());
    if (learned.isTautology()) {
      learned.release();
      continue;
    }
    CRef cr = attachConstraint(learned, false);
    assert(cr != CRef_Unsat);
    Constr& C = ca[cr];
    if (assertionLevel < INF)
      recomputeLBD(C);
    else
      C.setLBD(C.size());  // the LBD of non-asserting constraints is undefined, so we take a safe upper bound
    learned.release();
  }
  return CRef_Undef;
}

std::pair<ID, ID> Solver::addInputConstraint(ConstrExpSuper& ce) {
  assert(ce.orig == Origin::FORMULA || ce.orig == Origin::UPPERBOUND || ce.orig == Origin::LOWERBOUND ||
         ce.orig == Origin::COREGUIDED);
  assert(decisionLevel() == 0);
  bool upperbound = ce.orig == Origin::UPPERBOUND;
  bool lowerbound = ce.orig == Origin::LOWERBOUND;
  if (upperbound || lowerbound) ce.orig = Origin::BOUND;
  ID input = ID_Undef;
  if (logger) input = ce.logAsInput();
  ce.postProcess(Level, Pos, true, stats);
  if (ce.isTautology()) {
    return {input, ID_Undef};  // already satisfied.
  }

  if (ce.hasNegativeSlack(Level)) {
    if (options.verbosity > 0) puts("c Inconsistent input constraint");
    if (logger) ce.logInconsistency(Level, Pos, stats);
    assert(decisionLevel() == 0);
    return {input, ID_Unsat};
  }  // TODO: don't check for this here, but just add the constraints to the learned stack?

  CRef cr = attachConstraint(ce, true);
  auto& confl = cePools.takeArb();
  if (!runPropagation(confl, true)) {
    if (options.verbosity > 0) puts("c Input conflict");
    if (logger) confl.logInconsistency(Level, Pos, stats);
    confl.release();
    assert(decisionLevel() == 0);
    return {input, ID_Unsat};
  }
  confl.release();
  ID id = ca[cr].id;
  Origin orig = ca[cr].getOrigin();
  if (orig != Origin::FORMULA) {
    external[id] = cr;
  }
  if (lpSolver && (orig == Origin::BOUND || orig == Origin::FORMULA)) {
    lpSolver->addConstraint(cr, false, upperbound, lowerbound);
  }
  return {input, id};
}

std::pair<ID, ID> Solver::addConstraint(const ConstrExpSuper& c, Origin orig) {
  // NOTE: copy to temporary constraint guarantees original constraint is not changed and does not need logger
  ConstrExpSuper& ce = c.reduce(cePools);
  ce.orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  ce.release();
  return result;
}

std::pair<ID, ID> Solver::addConstraint(const ConstrSimpleSuper& c, Origin orig) {
  ConstrExpSuper& ce = c.toExpanded(cePools);
  ce.orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  ce.release();
  return result;
}

void Solver::removeConstraint(Constr& C, [[maybe_unused]] bool override) {
  assert(override || !C.isLocked());
  assert(!C.isMarkedForDelete());
  assert(!external.count(C.id));
  C.markForDel();
  ca.wasted += C.getMemSize();
}

void Solver::dropExternal(ID id, bool erasable, bool forceDelete) {
  assert(erasable || !forceDelete);
  if (id == ID_Undef) return;
  auto old_it = external.find(id);
  assert(old_it != external.end());
  Constr& constr = ca[old_it->second];
  external.erase(old_it);
  constr.setLocked(!erasable);
  if (forceDelete) removeConstraint(constr);
}

// ---------------------------------------------------------------------
// Garbage collection

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are deleted.
void Solver::garbage_collect() {
  assert(decisionLevel() == 0);  // so we don't need to update the pointer of Reason<CRef>
  if (options.verbosity > 0) puts("c GARBAGE COLLECT");
  for (Lit l = -n; l <= n; ++l)
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (ca[adj[l][i].cref].isMarkedForDelete()) aux::swapErase(adj[l], i--);
    }

  ca.wasted = 0;
  ca.at = 0;
  std::unordered_map<uint32_t, CRef> crefmap;
  for (int i = 1; i < (int)constraints.size(); ++i) assert(constraints[i - 1].ofs < constraints[i].ofs);
  for (CRef& cr : constraints) {
    uint32_t offset = cr.ofs;
    size_t memSize = ca[cr].getMemSize();
    memmove(ca.memory + ca.at, ca.memory + cr.ofs, sizeof(uint32_t) * memSize);
    cr.ofs = ca.at;
    ca.at += memSize;
    crefmap[offset] = cr;
  }
#define update_ptr(cr) cr = crefmap[cr.ofs];
  for (Lit l = -n; l <= n; l++)
    for (size_t i = 0; i < adj[l].size(); i++) update_ptr(adj[l][i].cref);
  for (auto& ext : external) update_ptr(ext.second);
#undef update_ptr
}

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are removed from memory.
void Solver::reduceDB() {
  assert(decisionLevel() == 0);

  std::vector<CRef> learnts;
  learnts.reserve(constraints.size() / 2);

  size_t totalLearnts = 0;
  size_t promisingLearnts = 0;
  for (CRef& cr : constraints) {
    Constr& C = ca[cr];
    if (C.isMarkedForDelete() || external.count(C.id)) continue;
    BigVal eval = -C.degree();
    for (int j = 0; j < (int)C.size() && eval < 0; ++j)
      if (isUnit(Level, C.lit(j))) eval += C.coef(j);
    if (eval >= 0)
      removeConstraint(C, true);  // remove constraints satisfied at root
    else if (!C.isLocked()) {
      if (C.size() > 2 && C.lbd() > 2) learnts.push_back(cr);  // Keep all binary clauses and short LBDs
      if (C.size() <= 2 || C.lbd() <= 3) ++promisingLearnts;
      ++totalLearnts;
    }
  }

  if (promisingLearnts > totalLearnts / 2)
    nconfl_to_reduce += 10 * options.incReduceDB;
  else
    nconfl_to_reduce += options.incReduceDB;
  std::sort(learnts.begin(), learnts.end(), [&](CRef x, CRef y) {
    return ca[x].lbd() > ca[y].lbd() || (ca[x].lbd() == ca[y].lbd() && ca[x].act < ca[y].act);
  });
  for (size_t i = 0; i < std::min(totalLearnts / 2, learnts.size()); ++i) removeConstraint(ca[learnts[i]]);

  size_t i = 0;
  size_t j = 0;
  for (; i < constraints.size(); ++i)
    if (!ca[constraints[i]].isMarkedForDelete()) constraints[j++] = constraints[i];
  constraints.resize(j);
  if ((double)ca.wasted / (double)ca.at > 0.2) garbage_collect();
}

// ---------------------------------------------------------------------
// Solving

double Solver::luby(double y, int i) {
  // Find the finite subsequence that contains index 'i', and the
  // size of that subsequence:
  int size, seq;
  for (size = 1, seq = 0; size < i + 1; seq++, size = 2 * size + 1) {
  }
  while (size != i + 1) {
    size = (size - 1) >> 1;
    --seq;
    assert(size != 0);
    i = i % size;
  }
  return std::pow(y, seq);
}

BigVal Solver::lhs(Constr& C, const std::vector<bool>& sol) {
  BigVal result = 0;
  for (size_t j = 0; j < C.size(); ++j) {
    Lit l = C.lit(j);
    result += ((l > 0) == sol[toVar(l)]) * C.coef(j);
  }
  return result;
}
bool Solver::checksol(const std::vector<bool>& sol) {
  for (CRef cr : constraints) {
    Constr& C = ca[cr];
    if (C.getOrigin() == Origin::FORMULA && lhs(C, sol) < C.degree()) return false;
  }
  return true;
}

Lit Solver::pickBranchLit() {
  Var next = 0;
  // Activity based decision:
  while (next == 0 || !isUnknown(Pos, next)) {
    if (order_heap.empty())
      return 0;
    else
      next = order_heap.removeMax();
  }
  assert(phase[0] == 0);
  return phase[next];
}

void Solver::presolve() {
  firstRun = false;
  if (lpSolver) lpSolver->inProcess();
}

/**
 * @return:
 * 	UNSAT if root inconsistency detected
 * 	SAT if satisfying assignment found
 * 	INCONSISTENT if no solution extending assumptions exists
 * 	INTERRUPTED if interrupted by external signal
 * 	INRPOCESSED if solver just finished a cleanup phase
 * 	RESTARTED if solver just restarted
 * @param assumptions: set of assumptions
 * @param core: if INCONSISTENT, implied constraint falsified by assumptions, otherwise untouched
 * 	if core is the empty constraint, at least one assumption is falsified at root
 * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
 */
// TODO: use a coroutine / yield instead of a SolveState return value
SolveState Solver::solve(const IntSet& assumptions, ConstrExpArb& core, std::vector<bool>& solution) {
  assert(core.isReset());
  backjumpTo(0);  // ensures assumptions are reset
  if (firstRun) presolve();
  std::vector<int> assumptions_lim = {0};
  assumptions_lim.reserve((int)assumptions.size() + 1);
  bool allClear = false;
  while (true) {
    if (asynch_interrupt) return SolveState::INTERRUPTED;
    if (processLearnedStack() == CRef_Unsat) return SolveState::UNSAT;
    allClear = runPropagation(conflConstraint, allClear);
    if (!allClear) {
      assert(!conflConstraint.isReset());
      vDecayActivity();
      cDecayActivity();
      stats.NCONFL++;
      nconfl_to_restart--;
      if (stats.NCONFL % 1000 == 0 && options.verbosity > 0) {
        printf("c #Conflicts: %10lld | #Constraints: %10lld\n", stats.NCONFL, (long long)constraints.size());
        if (options.verbosity > 2) {
          // memory usage
          std::cout << "c total constraint space: " << ca.cap * 4 / 1024. / 1024. << "MB" << std::endl;
          std::cout << "c total #watches: ";
          long long cnt = 0;
          for (Lit l = -n; l <= n; l++) cnt += (long long)adj[l].size();
          std::cout << cnt << std::endl;
        }
      }
      if (decisionLevel() == 0) {
        if (logger) {
          conflConstraint.logInconsistency(Level, Pos, stats);
          conflConstraint.reset();
        }
        return SolveState::UNSAT;
      } else if (decisionLevel() >= (int)assumptions_lim.size()) {
        if (!analyze(conflConstraint)) return SolveState::INTERRUPTED;
        assert(!conflConstraint.isTautology());
        assert(conflConstraint.isSaturated());
        if (learnedStack.size() > 0 && learnedStack.back()->orig == Origin::FARKAS)
          learnConstraint(conflConstraint, Origin::LEARNEDFARKAS);  // TODO: ugly hack
        else
          learnConstraint(conflConstraint, Origin::LEARNED);
        conflConstraint.reset();
      } else {
        if (!extractCore(conflConstraint, assumptions, core)) return SolveState::INTERRUPTED;
        return SolveState::INCONSISTENT;
      }
    } else {  // no conflict
      if (nconfl_to_restart <= 0) {
        backjumpTo(0);
        if (stats.NCONFL >= (stats.NCLEANUP + 1) * nconfl_to_reduce) {
          ++stats.NCLEANUP;
          if (options.verbosity > 0) puts("c INPROCESSING");
          reduceDB();
          while (stats.NCONFL >= stats.NCLEANUP * nconfl_to_reduce) nconfl_to_reduce += options.incReduceDB;
          if (lpSolver) lpSolver->inProcess();
          return SolveState::INPROCESSED;
        }
        double rest_base = luby(options.rinc, ++stats.NRESTARTS);
        nconfl_to_restart = (long long)rest_base * options.rfirst;
        return SolveState::RESTARTED;
      }
      Lit next = 0;
      if ((int)assumptions_lim.size() > decisionLevel() + 1) assumptions_lim.resize(decisionLevel() + 1);
      if (assumptions_lim.back() < (int)assumptions.size()) {
        for (int i = (decisionLevel() == 0 ? 0 : trail_lim.back()); i < (int)trail.size(); ++i) {
          Lit l = trail[i];
          if (assumptions.has(-l)) {  // found conflicting assumption
            if (isUnit(Level, l))
              backjumpTo(0);  // negated assumption is unit
            else {
              ConstrExpSuper& tmp = ca[Reason[toVar(l)]].toExpanded(cePools);
              tmp.copyTo(conflConstraint);
              tmp.release();
              if (!extractCore(conflConstraint, assumptions, core, -l)) return SolveState::INTERRUPTED;
            }
            return SolveState::INCONSISTENT;
          }
        }
      }
      while (assumptions_lim.back() < (int)assumptions.size()) {
        assert(decisionLevel() == (int)assumptions_lim.size() - 1);
        Lit l_assump = assumptions.keys[assumptions_lim.back()];
        assert(!isFalse(Level, l_assump));  // otherwise above check should have caught this
        if (isTrue(Level, l_assump)) {      // assumption already propagated
          ++assumptions_lim.back();
        } else {  // unassigned assumption
          next = l_assump;
          assumptions_lim.push_back(assumptions_lim.back() + 1);
          break;
        }
      }
      if (next == 0) next = pickBranchLit();
      if (next == 0) {
        assert(order_heap.empty());
        assert((int)trail.size() == n);
        solution.clear();
        solution.resize(n + 1);
        solution[0] = false;
        for (Var v = 1; v <= n; ++v) solution[v] = isTrue(Level, v);
        backjumpTo(0);
        assert(checksol(solution));
        return SolveState::SAT;
      }
      decide(next);
    }
  }
}
