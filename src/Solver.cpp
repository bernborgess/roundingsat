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

#include "Solver.hpp"
#include <cmath>
#include "aux.hpp"
#include "globals.hpp"

// ---------------------------------------------------------------------
// Initialization

Solver::Solver() : order_heap(activity) {
  ca.memory = NULL;
  ca.at = 0;
  ca.cap = 0;
  ca.wasted = 0;
  ca.capacity(1024 * 1024);  // 4MB
  assert(sizeof(Constr) == 12 * sizeof(uint32_t));
}

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
  tmpConstraint.resize(nvars + 1);
  conflConstraint.resize(nvars + 1);
  logConstraint.resize(nvars + 1);
  order_heap.resize(nvars + 1);
  for (Var v = n + 1; v <= nvars; ++v) phase[v] = -v, order_heap.insert(v);
  if (lpSolver) lpSolver->setNbVariables(nvars + 1);
  n = nvars;
  stats.NAUXVARS = n - orig_n;
}

void Solver::setNbOrigVars(int o_n) {
  orig_n = o_n;
  stats.NAUXVARS = n - orig_n;
}

void Solver::init() {
  if (!options.proofLogName.empty()) logger = std::make_shared<Logger>(options.proofLogName);
  tmpConstraint.initializeLogging(logger);
  conflConstraint.initializeLogging(logger);
  logConstraint.initializeLogging(logger);
}

void Solver::initLP(intConstr& objective) {
  if (options.lpPivotRatio == 0) return;
  bool pureCNF = objective.vars.size() == 0;
  for (CRef cr : constraints) {
    if (!pureCNF) break;
    pureCNF = ca[cr].isClause();
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
      C.toConstraint(logConstraint);
      logConstraint.logUnit(Level, Pos, v, stats);
      logConstraint.reset();
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
      if (w.idx >= 0 && w.idx % 2 == 0) ca[w.cref].undoFalsified(w.idx);
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
bool Solver::runPropagation(bool onlyUnitPropagation) {
  while (qhead < (int)trail.size()) {
    Lit p = trail[qhead++];
    std::vector<Watch>& ws = adj[-p];
    for (int it_ws = 0; it_ws < (int)ws.size(); ++it_ws) {
      int idx = ws[it_ws].idx;
      if (idx < 0 && isTrue(Level, idx + INF)) {
        assert(ca[ws[it_ws].cref].isClause());
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
          if (w.idx >= 0 && w.idx % 2 == 0) ca[w.cref].undoFalsified(w.idx);
        }
        --qhead;
        Constr& C = ca[cr];
        if (C.getType() == ConstraintType::LEARNT) {
          cBumpActivity(C);
          recomputeLBD(C);
        }
        C.toConstraint(conflConstraint);
        return false;
      }
    }
  }
  if (onlyUnitPropagation) return true;
  if (lpSolver) return lpSolver->checkFeasibility() != INFEASIBLE;
  return true;
}

WatchStatus Solver::checkForPropagation(CRef cr, int& idx, Lit p) {
  Constr& C = ca[cr];
  if (C.isMarkedForDelete()) return WatchStatus::DROPWATCH;

  assert(isFalse(Level, p));
  ++stats.NWATCHLOOKUPS;
  int* data = C.data;

  if (C.isClause()) {
    assert(idx < 0);
    assert(p == data[0] || p == data[1]);
    assert(C.size() > 1);
    int widx = 0;
    Lit watch = data[0];
    Lit otherwatch = data[1];
    if (p == data[1]) {
      widx = 1;
      watch = data[1];
      otherwatch = data[0];
    }
    assert(p == watch);
    assert(p != otherwatch);
    if (isTrue(Level, otherwatch)) {
      idx = otherwatch - INF;         // set new blocked literal
      return WatchStatus::KEEPWATCH;  // constraint is satisfied
    }
    const unsigned int Csize = C.size();
    for (unsigned int i = 2; i < Csize; ++i) {
      Lit l = data[i];
      if (!isFalse(Level, l)) {
        int mid = i / 2 + 1;
        data[i] = data[mid];
        data[mid] = watch;
        data[widx] = l;
        adj[l].emplace_back(cr, otherwatch - INF);
        stats.NWATCHCHECKS += i - 1;
        return WatchStatus::DROPWATCH;
      }
    }
    stats.NWATCHCHECKS += Csize - 2;
    assert(isFalse(Level, watch));
    for (unsigned int i = 2; i < Csize; ++i) assert(isFalse(Level, data[i]));
    if (isFalse(Level, otherwatch))
      return WatchStatus::CONFLICTING;
    else {
      assert(!isTrue(Level, otherwatch));
      ++stats.NPROPCLAUSE;
      propagate(otherwatch, cr);
    }
    ++stats.NPROPCHECKS;
    return WatchStatus::KEEPWATCH;
  }

  assert(idx >= 0);
  unsigned int& watchIdx = C.watchIdx;
  const Val degree = C.degree;
  if (C.isCard()) {
    assert(idx % 2 == 1);
    unsigned int widx = idx;
    widx = widx >> 1;
    assert(data[widx] == p);
    const unsigned int Csize = C.size();
    if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS) {
      C.ntrailpops = stats.NTRAILPOPS;
      watchIdx = degree + 1;
    }
    assert(watchIdx > degree);
    stats.NWATCHCHECKS -= watchIdx;
    for (; watchIdx < Csize; ++watchIdx) {
      Lit l = data[watchIdx];
      if (!isFalse(Level, l)) {
        unsigned int mid = (watchIdx + degree + 1) / 2;
        assert(mid <= watchIdx);
        assert(mid > degree);
        data[watchIdx] = data[mid];
        data[mid] = data[widx];
        data[widx] = l;
        adj[l].emplace_back(cr, (widx << 1) + 1);
        stats.NWATCHCHECKS += watchIdx + 1;
        return WatchStatus::DROPWATCH;
      }
    }
    stats.NWATCHCHECKS += watchIdx;
    assert(isFalse(Level, data[widx]));
    for (unsigned int i = degree + 1; i < Csize; ++i) assert(isFalse(Level, data[i]));
    for (unsigned int i = 0; i <= degree; ++i)
      if (i != widx && isFalse(Level, data[i])) return WatchStatus::CONFLICTING;
    for (unsigned int i = 0; i <= degree; ++i) {
      Lit l = data[i];
      if (i != widx && !isTrue(Level, l)) {
        ++stats.NPROPCARD;
        propagate(l, cr);
      }
    }
    stats.NPROPCHECKS += degree + 1;
    return WatchStatus::KEEPWATCH;
  }

  assert(idx % 2 == 0);
  assert(data[idx + 1] == p);
  const unsigned int Csize2 = 2 * C.size();
  const Coef ClargestCoef = C.largestCoef();
  const Coef c = data[idx];

  Val& slack = C.slack;
  if (C.isCounting()) {  // use counting propagation
    slack -= c;
    if (slack < 0) return WatchStatus::CONFLICTING;
    if (slack < ClargestCoef) {
      if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS) {
        C.ntrailpops = stats.NTRAILPOPS;
        watchIdx = 0;
      }
      stats.NPROPCHECKS -= watchIdx >> 1;
      for (; watchIdx < Csize2 && data[watchIdx] > slack; watchIdx += 2) {
        const Lit l = data[watchIdx + 1];
        if (isUnknown(Pos, l)) {
          stats.NPROPCLAUSE += (degree == 1);
          stats.NPROPCARD += (degree != 1 && ClargestCoef == 1);
          ++stats.NPROPCOUNTING;
          propagate(l, cr);
        }
      }
      stats.NPROPCHECKS += watchIdx >> 1;
    }
    return WatchStatus::KEEPWATCH;
  }

  // use watched propagation
  if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS) {
    C.ntrailpops = stats.NTRAILPOPS;
    watchIdx = 0;
  }
  assert(c < 0);
  slack += c;
  if (!options.supProp ||
      slack - c >= ClargestCoef) {  // look for new watches if previously, slack was at least ClargestCoef
    stats.NWATCHCHECKS -= watchIdx >> 1;
    for (; watchIdx < Csize2 && slack < ClargestCoef; watchIdx += 2) {  // NOTE: first innermost loop of RoundingSat
      const Coef cf = data[watchIdx];
      const Lit l = data[watchIdx + 1];
      if (cf > 0 && !isFalse(Level, l)) {
        slack += cf;
        data[watchIdx] = -cf;
        adj[l].emplace_back(cr, watchIdx);
      }
    }
    stats.NWATCHCHECKS += watchIdx >> 1;
    if (slack < ClargestCoef) {
      assert(watchIdx == Csize2);
      watchIdx = 0;
    }
  }  // else we did not find enough watches last time, so we can skip looking for them now

  if (slack >= ClargestCoef) {
    data[idx] = -c;
    return WatchStatus::DROPWATCH;
  }
  if (slack < 0) return WatchStatus::CONFLICTING;
  // keep the watch, check for propagation
  stats.NPROPCHECKS -= watchIdx >> 1;
  for (; watchIdx < Csize2 && std::abs(data[watchIdx]) > slack;
       watchIdx += 2) {  // NOTE: second innermost loop of RoundingSat
    const Lit l = data[watchIdx + 1];
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (degree == 1);
      stats.NPROPCARD += (degree != 1 && ClargestCoef == 1);
      ++stats.NPROPWATCH;
      propagate(l, cr);
    }
  }
  stats.NPROPCHECKS += watchIdx >> 1;
  return WatchStatus::KEEPWATCH;
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

bool Solver::analyze() {
  if (logger) logger->logComment("analyzing", stats);
  assert(conflConstraint.getSlack(Level) < 0);
  stats.NADDEDLITERALS += conflConstraint.vars.size();
  conflConstraint.removeUnitsAndZeroes(Level, Pos);
  assert(actSet.size() == 0);  // will hold the literals that need their activity bumped
  for (Var v : conflConstraint.vars) actSet.add(conflConstraint.getLit(v));
  while (decisionLevel() > 0) {
    if (asynch_interrupt) return false;
    Lit l = trail.back();
    assert(std::abs(conflConstraint.getCoef(-l)) < INF);
    Coef confl_coef_l = conflConstraint.getCoef(-l);
    if (confl_coef_l > 0) {
      ++stats.NRESOLVESTEPS;
      assert(conflConstraint.getSlack(Level) < 0);
      AssertionStatus status = conflConstraint.isAssertingBefore(Level, decisionLevel());
      if (status == AssertionStatus::ASSERTING)
        break;
      else if (status == AssertionStatus::FALSIFIED) {
        backjumpTo(decisionLevel() - 1);
        assert(conflConstraint.getSlack(Level) < 0);
        continue;
      }
      assert(Reason[toVar(l)] != CRef_Undef);
      Constr& reasonC = ca[Reason[toVar(l)]];
      if (reasonC.getType() == ConstraintType::LEARNT) {
        cBumpActivity(reasonC);
        recomputeLBD(reasonC);
      }
      reasonC.toConstraint(tmpConstraint);
      stats.NADDEDLITERALS += tmpConstraint.vars.size();
      tmpConstraint.removeUnitsAndZeroes(Level, Pos);  // NOTE: also saturates
      if (options.weakenNonImplying)
        tmpConstraint.weakenNonImplying(Level, tmpConstraint.getCoef(l), tmpConstraint.getSlack(Level),
                                        stats);  // NOTE: also saturates
      assert(tmpConstraint.getCoef(l) > tmpConstraint.getSlack(Level));
      tmpConstraint.weakenDivideRound(getLevel(), l, options.maxdiv, options.weakenFull);
      assert(tmpConstraint.getSlack(Level) <= 0);
      for (Var v : tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
      Coef reason_coef_l = tmpConstraint.getCoef(l);
      Coef gcd_coef_l = aux::gcd(reason_coef_l, confl_coef_l);
      conflConstraint.addUp(tmpConstraint, confl_coef_l / gcd_coef_l, reason_coef_l / gcd_coef_l);
      conflConstraint.saturateAndFixOverflow(getLevel(), options.weakenFull);
      tmpConstraint.reset();
      assert(conflConstraint.getCoef(-l) == 0);
      assert(conflConstraint.getSlack(Level) < 0);
    }
    undoOne();
  }
  assert(conflConstraint.getSlack(Level) < 0);
  for (Lit l : actSet.keys)
    if (l != 0) vBumpActivity(toVar(l));
  actSet.reset();
  return true;
}

bool Solver::extractCore(const IntSet& assumptions, intConstr& outCore, Lit l_assump) {
  assert(!conflConstraint.isReset());
  outCore.reset();

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

  stats.NADDEDLITERALS += conflConstraint.vars.size();
  conflConstraint.removeUnitsAndZeroes(Level, Pos);
  assert(conflConstraint.getSlack(Level) < 0);

  // analyze conflict
  Val assumpslk = conflConstraint.getSlack(assumptions);
  while (assumpslk >= 0) {
    if (asynch_interrupt) return false;
    Lit l = trail.back();
    assert(std::abs(conflConstraint.getCoef(-l)) < INF);
    Coef confl_coef_l = conflConstraint.getCoef(-l);
    if (confl_coef_l > 0) {
      ca[Reason[toVar(l)]].toConstraint(tmpConstraint);
      stats.NADDEDLITERALS += tmpConstraint.vars.size();
      tmpConstraint.removeUnitsAndZeroes(Level, Pos);
      if (options.weakenNonImplying)
        tmpConstraint.weakenNonImplying(Level, tmpConstraint.getCoef(l), tmpConstraint.getSlack(Level),
                                        stats);  // NOTE: also saturates
      assert(tmpConstraint.getCoef(l) > tmpConstraint.getSlack(Level));
      tmpConstraint.weakenDivideRound(getLevel(), l, options.maxdiv, options.weakenFull);
      assert(tmpConstraint.getSlack(Level) <= 0);
      Coef reason_coef_l = tmpConstraint.getCoef(l);
      Coef gcd_coef_l = aux::gcd(reason_coef_l, confl_coef_l);
      conflConstraint.addUp(tmpConstraint, confl_coef_l / gcd_coef_l, reason_coef_l / gcd_coef_l);
      conflConstraint.saturateAndFixOverflow(getLevel(), options.weakenFull);
      tmpConstraint.reset();
      assert(conflConstraint.getCoef(-l) == 0);
      assert(conflConstraint.getSlack(Level) < 0);
      assumpslk = conflConstraint.getSlack(assumptions);
    }
    assert(decisionLevel() == (int)decisions.size());
    undoOne();
  }
  assert(conflConstraint.getDegree() > 0);
  assert(conflConstraint.getDegree() < INF);
  assert(conflConstraint.isSaturated());
  conflConstraint.copyTo(outCore);
  conflConstraint.reset();

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

CRef Solver::attachConstraint(intConstr& constraint, ConstraintType type) {
  assert(constraint.isSortedInDecreasingCoefOrder());
  assert(constraint.isSaturated());
  assert(constraint.hasNoZeroes());
  assert(constraint.hasNoUnits(Level));
  assert(constraint.getDegree() > 0);
  assert(constraint.getDegree() < INF);
  assert(constraint.vars.size() > 0);

  if (logger)
    constraint.logProofLineWithInfo("Attach", stats);
  else
    constraint.id = ++crefID;
  CRef cr = ca.alloc(constraint, type, constraint.id);
  constraints.push_back(cr);
  Constr& C = ca[cr];
  int* data = C.data;

  bool learned = type == ConstraintType::LEARNT;
  if (learned) {
    stats.LEARNEDLENGTHSUM += C.size();
    stats.LEARNEDDEGREESUM += C.degree;
  } else {
    stats.EXTERNLENGTHSUM += C.size();
    stats.EXTERNDEGREESUM += C.degree;
  }
  if (C.degree == 1) {
    stats.NCLAUSESLEARNED += learned;
    stats.NCLAUSESEXTERN += !learned;
  } else if (C.isCard() || C.largestCoef() == 1) {
    stats.NCARDINALITIESLEARNED += learned;
    stats.NCARDINALITIESEXTERN += !learned;
  } else {
    stats.NGENERALSLEARNED += learned;
    stats.NGENERALSEXTERN += !learned;
  }

  if (C.isSimple()) {
    if (C.degree >= C.size()) {
      assert(decisionLevel() == 0);
      for (unsigned int i = 0; i < C.size(); ++i) {
        assert(isUnknown(Pos, data[i]));
        propagate(data[i], cr);
      }
      return cr;
    }

    unsigned int watch = 0;
    for (unsigned int i = 0; i < C.size(); ++i) {
      Lit l = data[i];
      if (!isFalse(Level, l)) {
        data[i] = data[watch];
        data[watch++] = l;
        if (watch > C.degree + 1) break;
      }
    }
    assert(watch >= C.degree);  // we found enough watches to satisfy the constraint
    if (isFalse(Level, data[C.degree])) {
      for (unsigned int i = 0; i < C.degree; ++i) {
        assert(!isFalse(Level, data[i]));
        if (!isTrue(Level, data[i])) propagate(data[i], cr);
      }
      for (unsigned int i = C.degree + 1; i < C.size(); ++i) {  // ensure last watch is last falsified literal
        Lit l = data[i];
        assert(isFalse(Level, l));
        if (Level[-l] > Level[-data[C.degree]]) {
          data[i] = data[C.degree];
          data[C.degree] = l;
        }
      }
    }
    if (C.isClause())
      for (unsigned int i = 0; i < 2; ++i) adj[data[i]].emplace_back(cr, data[1 - i] - INF);  // add blocked literal
    else
      for (unsigned int i = 0; i <= C.degree; ++i) adj[data[i]].emplace_back(cr, (i << 1) + 1);  // add watch index
    return cr;
  }

  Val watchSum = -C.degree - C.largestCoef();
  unsigned int minWatches = 0;
  for (; minWatches < 2 * C.size() && watchSum < 0; minWatches += 2) watchSum += data[minWatches];
  minWatches >>= 1;
  assert(C.size() > 0);
  assert(minWatches > 0);
  C.setCounting(options.countingProp == 1 || options.countingProp > (1 - minWatches / (float)C.size()));

  if (C.isCounting()) {  // use counting propagation
    ++stats.NCOUNTING;
    for (unsigned int i = 0; i < 2 * C.size(); i += 2) {
      Lit l = data[i + 1];
      adj[l].emplace_back(cr, i);
      if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) C.slack += data[i];
    }
    assert(C.slack >= 0);
    if (C.slack < C.largestCoef()) {  // propagate
      for (unsigned int i = 0; i < 2 * C.size() && data[i] > C.slack; i += 2)
        if (isUnknown(Pos, data[i + 1])) {
          propagate(data[i + 1], cr);
        }
    }
    return cr;
  }

  // watched propagation
  ++stats.NWATCHED;
  for (unsigned int i = 0; i < 2 * C.size() && C.slack < C.largestCoef(); i += 2) {
    Lit l = data[i + 1];
    if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) {
      assert(!C.isWatched(i));
      C.slack += data[i];
      data[i] = -data[i];
      adj[l].emplace_back(cr, i);
    }
  }
  assert(C.slack >= 0);
  if (C.slack < C.largestCoef()) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(C.size());
    for (unsigned int i = 0; i < 2 * C.size(); i += 2)
      if (isFalse(Level, data[i + 1]) && Pos[std::abs(data[i + 1])] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(),
              [&](unsigned i1, unsigned i2) { return Pos[std::abs(data[i1 + 1])] > Pos[std::abs(data[i2 + 1])]; });
    Val diff = C.largestCoef() - C.slack;
    for (unsigned int i : falsifiedIdcs) {
      assert(!C.isWatched(i));
      diff -= data[i];
      data[i] = -data[i];
      adj[data[i + 1]].emplace_back(cr, i);
      if (diff <= 0) break;
    }
    // perform initial propagation
    for (unsigned int i = 0; i < 2 * C.size() && std::abs(data[i]) > C.slack; i += 2)
      if (isUnknown(Pos, data[i + 1])) {
        propagate(data[i + 1], cr);
      }
  }
  return cr;
}

// NOTE: backjumps to place where the constraint is not conflicting, as otherwise we might miss propagations
CRef Solver::processLearnedStack() {
  // loop back to front as the last constraint in the queue is a result of conflict analysis
  // and we want to first check this constraint to backjump.
  while (learnedStack.size() > 0) {
    tmpConstraint.construct(learnedStack.back());
    learnedStack.pop_back();
    tmpConstraint.removeUnitsAndZeroes(Level, Pos, true);
    tmpConstraint.sortInDecreasingCoefOrder();
    int assertionLevel = tmpConstraint.getAssertionLevel(Level, Pos);
    if (assertionLevel < 0) {
      backjumpTo(0);
      assert(tmpConstraint.getSlack(Level) < 0);
      if (logger) tmpConstraint.logInconsistency(Level, Pos, stats);
      tmpConstraint.reset();
      return CRef_Unsat;
    }
    backjumpTo(assertionLevel);
    Val slk = tmpConstraint.getSlack(Level);
    assert(slk >= 0);
    tmpConstraint.heuristicWeakening(Level, Pos, slk, stats);  // TODO: don't always weaken heuristically?
    tmpConstraint.postProcess(Level, Pos, false, stats);
    assert(tmpConstraint.isSaturated());
    if (tmpConstraint.getDegree() <= 0) {
      tmpConstraint.reset();
      continue;
    }
    CRef cr = attachConstraint(tmpConstraint, ConstraintType::LEARNT);
    assert(cr != CRef_Unsat);
    tmpConstraint.reset();
    Constr& C = ca[cr];
    if (assertionLevel < INF) recomputeLBD(C);  // some constraints are not asserting so their LBD's are unknown
  }
  return CRef_Undef;
}

ID Solver::addInputConstraint(ConstraintType type, bool addToLP) {
  assert(decisionLevel() == 0);
  if (logger) tmpConstraint.logAsInput();
  tmpConstraint.postProcess(Level, Pos, true, stats);
  assert(tmpConstraint.getDegree() < INF);
  if (tmpConstraint.getDegree() <= 0) {
    tmpConstraint.reset();
    return ID_Undef;  // already satisfied.
  }

  if (tmpConstraint.getSlack(Level) < 0) {
    if (options.verbosity > 0) puts("c Inconsistent input constraint");
    if (logger) tmpConstraint.logInconsistency(Level, Pos, stats);
    tmpConstraint.reset();
    assert(decisionLevel() == 0);
    return ID_Unsat;
  }

  CRef cr = attachConstraint(tmpConstraint, type);
  tmpConstraint.reset();
  if (!runPropagation(true)) {
    if (options.verbosity > 0) puts("c Input conflict");
    if (logger) {
      conflConstraint.logInconsistency(Level, Pos, stats);
      conflConstraint.reset();
    }
    assert(decisionLevel() == 0);
    return ID_Unsat;
  }
  ID id = ca[cr].id;
  if (type == ConstraintType::EXTERNAL) external[id] = cr;
  if (addToLP && lpSolver) lpSolver->addConstraint(cr, false);
  return id;
}

ID Solver::addConstraint(const intConstr& c, ConstraintType type, bool addToLP) {
  // NOTE: copy to tmpConstraint guarantees original constraint is not changed and does not need logger
  c.copyTo(tmpConstraint);
  ID result = addInputConstraint(type, addToLP);
  return result;
}

ID Solver::addConstraint(const SimpleConsInt& c, ConstraintType type, bool addToLP) {
  tmpConstraint.construct(c);
  ID result = addInputConstraint(type, addToLP);
  return result;
}

void Solver::removeConstraint(Constr& C) {
  assert(decisionLevel() == 0);
  assert(C.getType() != ConstraintType::EXTERNAL);
  assert(!C.isMarkedForDelete());
  C.markForDel();
  ca.wasted += C.getMemSize();
}

void Solver::dropExternal(ID id, bool forceDelete, bool removeFromLP) {
  if (id == ID_Undef) return;
  auto old_it = external.find(id);
  assert(old_it != external.end());
  Constr& constr = ca[old_it->second];
  constr.setType(ConstraintType::AUXILIARY);
  if (forceDelete) removeConstraint(constr);
  if (removeFromLP && lpSolver) lpSolver->removeConstraint(id);
  external.erase(old_it);
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
    int memSize = ca[cr].getMemSize();
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
    if (C.isMarkedForDelete() || C.getType() == ConstraintType::EXTERNAL) continue;
    Val eval = -C.degree;
    for (int j = 0; j < (int)C.size() && eval < 0; ++j)
      if (isUnit(Level, C.lit(j))) eval += C.coef(j);
    if (eval >= 0)
      removeConstraint(C);  // remove constraints satisfied at root
    else if (C.getType() == ConstraintType::LEARNT) {
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

Val Solver::lhs(Constr& C, const std::vector<bool>& sol) {
  Val result = 0;
  for (size_t j = 0; j < C.size(); ++j) {
    Lit l = C.lit(j);
    result += ((l > 0) == sol[toVar(l)]) * C.coef(j);
  }
  return result;
}
bool Solver::checksol(const std::vector<bool>& sol) {
  for (CRef cr : constraints) {
    Constr& C = ca[cr];
    if (C.getType() == ConstraintType::FORMULA && lhs(C, sol) < C.degree) return false;
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
SolveState Solver::solve(const IntSet& assumptions, intConstr& core, std::vector<bool>& solution) {
  backjumpTo(0);  // ensures assumptions are reset
  if (firstRun) presolve();
  std::vector<int> assumptions_lim = {0};
  assumptions_lim.reserve((int)assumptions.size() + 1);
  bool allClear = false;
  while (true) {
    if (asynch_interrupt) return SolveState::INTERRUPTED;
    assert(conflConstraint.isReset());
    if (processLearnedStack() == CRef_Unsat) return SolveState::UNSAT;
    allClear = runPropagation(allClear);
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
        if (!analyze()) return SolveState::INTERRUPTED;
        assert(conflConstraint.getDegree() > 0);
        assert(conflConstraint.getDegree() < INF);
        assert(conflConstraint.isSaturated());
        learnConstraint(conflConstraint);
        conflConstraint.reset();
      } else {
        if (!extractCore(assumptions, core)) return SolveState::INTERRUPTED;
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
              backjumpTo(0), core.reset();  // negated assumption is unit
            else {
              ca[Reason[toVar(l)]].toConstraint(conflConstraint);
              if (!extractCore(assumptions, core, -l)) return SolveState::INTERRUPTED;
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