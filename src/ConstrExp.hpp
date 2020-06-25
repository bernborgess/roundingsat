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

#include <algorithm>
#include <functional>
#include <memory>
#include <sstream>
#include "ConstrSimple.hpp"
#include "IntSet.hpp"
#include "Logger.hpp"
#include "Stats.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

enum AssertionStatus { NONASSERTING, ASSERTING, FALSIFIED };

template <typename SMALL, typename LARGE>  // LARGE should be able to fit sums of SMALL
struct ConstrExp {
  LARGE degree = 0;
  LARGE rhs = 0;
  std::vector<Var> vars;
  std::vector<SMALL> coefs;
  std::vector<bool> used;
  Origin orig = Origin::UNKNOWN;
  std::stringstream proofBuffer;
  std::shared_ptr<Logger> plogger;

 private:
  void remove(Var v) {
    assert(used[v]);
    coefs[v] = 0;
    used[v] = false;
  }

  bool increasesSlack(const IntVecIt& level, Var v) const {
    return isTrue(level, v) || (!isFalse(level, v) && coefs[v] > 0);
  }

  LARGE calcDegree() const {
    LARGE res = rhs;
    for (Var v : vars) res -= std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
    return res;
  }

  LARGE calcRhs() const {
    LARGE res = degree;
    for (Var v : vars) res += std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
    return res;
  }

  bool testConstraint() const {
    assert(degree == calcDegree());
    assert(rhs == calcRhs());
    assert(coefs.size() == used.size());
    std::unordered_set<Var> usedvars;
    usedvars.insert(vars.begin(), vars.end());
    for (Var v = 1; v < (int)coefs.size(); ++v) {
      assert(used[v] || coefs[v] == 0);
      assert(usedvars.count(v) == used[v]);
    }
    return true;
  }

 public:
  ConstrExp() { reset(); }

  template <typename CF, typename DG>
  void init(const ConstrSimple<CF, DG>& sc) {
    // TODO: assert whether CF/DG can fit SMALL/LARGE? Not always possible.
    assert(isReset());
    addRhs(sc.rhs);
    for (auto& t : sc.terms) {
      addLhs(t.c, t.l);
    }
    orig = sc.orig;
    if (plogger) {
      proofBuffer.str(std::string());
      proofBuffer << sc.proofLine;
    }
  }

  template <typename S, typename L>
  void copyTo(ConstrExp<S, L>& out) const {
    // TODO: assert whether S/L can fit SMALL/LARGE? Not always possible.
    assert(out.isReset());
    out.degree = static_cast<L>(degree);
    out.rhs = static_cast<L>(rhs);
    out.orig = orig;
    out.vars = vars;
    out.resize(coefs.size());
    for (Var v : vars) {
      out.coefs[v] = static_cast<S>(coefs[v]);
      assert(used[v] == true);
      assert(out.used[v] == false);
      out.used[v] = true;
    }
    if (plogger) {
      out.proofBuffer.str(std::string());
      out.proofBuffer << proofBuffer.str();
    }
  }

  template <typename CF, typename DG>
  ConstrSimple<CF, DG> toSimpleCons() {
    ConstrSimple<CF, DG> result;
    result.rhs = static_cast<DG>(getRhs());
    result.terms.reserve(vars.size());
    for (Var v : vars)
      if (coefs[v] != 0) result.terms.emplace_back((Coef)coefs[v], v);
    if (plogger) result.proofLine = proofBuffer.str();
    result.orig = orig;
    return result;
  }

  void resize(size_t s) {
    if (s > coefs.size()) {
      coefs.resize(s, 0);
      used.resize(s, false);
    }
  }

  void resetBuffer(ID proofID = ID_Trivial) {
    assert(plogger);
    assert(proofID != ID_Undef);
    assert(proofID != ID_Unsat);
    proofBuffer.clear();
    proofBuffer.str(std::string());
    proofBuffer << proofID << " ";
  }

  void initializeLogging(std::shared_ptr<Logger>& l) {
    assert(isReset());
    plogger = l;
    if (plogger) resetBuffer();
  }

  template <typename T>
  static std::string proofMult(const T& mult) {
    std::stringstream ss;
    if (mult != 1) ss << mult << " * ";
    return ss.str();
  }

  bool isReset() const { return vars.size() == 0 && rhs == 0 && degree == 0; }

  void reset() {
    for (Var v : vars) remove(v);
    vars.clear();
    rhs = 0;
    degree = 0;
    orig = Origin::UNKNOWN;
    if (plogger) resetBuffer();
  }

  void addRhs(const LARGE& r) {
    rhs += r;
    degree += r;
  }

  LARGE getRhs() const { return rhs; }
  LARGE getDegree() const { return degree; }
  SMALL getCoef(Lit l) const {
    assert((unsigned int)toVar(l) < coefs.size());
    return l < 0 ? -coefs[-l] : coefs[l];
  }
  Lit getLit(Lit l) const {  // NOTE: answer of 0 means coef 0 or not in vars
    Var v = toVar(l);
    return (v >= (Var)coefs.size() || coefs[v] == 0) ? 0 : (coefs[v] < 0 ? -v : v);
  }

  bool falsified(const IntVecIt& level, Var v) const {
    assert(v > 0);
    assert((getLit(v) != 0 && !isFalse(level, getLit(v))) == (coefs[v] > 0 && !isFalse(level, v)) ||
           (coefs[v] < 0 && !isTrue(level, v)));
    return (coefs[v] > 0 && isFalse(level, v)) || (coefs[v] < 0 && isTrue(level, v));
  }

  LARGE getSlack(const IntVecIt& level) const {
    LARGE slack = -rhs;
    for (Var v : vars)
      if (increasesSlack(level, v)) slack += coefs[v];
    return slack;
  }

  LARGE getSlack(const IntSet& assumptions) const {
    LARGE slack = -rhs;
    for (Var v : vars)
      if (assumptions.has(v) || (!assumptions.has(-v) && coefs[v] > 0)) slack += coefs[v];
    return slack;
  }

  void addLhs(const SMALL& cf, Lit l) {  // add c*(l>=0) if c>0 and -c*(-l>=0) if c<0
    if (cf == 0) return;
    assert(l != 0);
    SMALL c = cf;
    if (c < 0) degree -= c;
    Var v = l;
    if (l < 0) {
      rhs -= c;
      c = -c;
      v = -l;
    }
    assert(v < (Var)coefs.size());
    if (!used[v]) {
      assert(coefs[v] == 0);
      vars.push_back(v);
      coefs[v] = c;
      used[v] = true;
    } else {
      if ((coefs[v] < 0) != (c < 0)) degree -= std::min(rs::abs(c), rs::abs(coefs[v]));
      coefs[v] += c;
    }
  }

  void weaken(const SMALL& m, Var v) {  // add m*(v>=0) if m>0 and -m*(-v>=-1) if m<0
    assert(v > 0);
    assert(v < (Var)coefs.size());
    if (m == 0) return;
    if (plogger) {
      if (m > 0)
        proofBuffer << "x" << v << " " << proofMult(m) << "+ ";
      else
        proofBuffer << "~x" << v << " " << proofMult(-m) << "+ ";
    }

    if (m < 0) rhs += m;
    if (!used[v]) {
      assert(coefs[v] == 0);
      vars.push_back(v);
      coefs[v] = m;
      used[v] = true;
    } else {
      if ((coefs[v] < 0) != (m < 0)) degree -= std::min(rs::abs(m), rs::abs(coefs[v]));
      coefs[v] += m;
    }
  }

  // @post: preserves order of vars
  void removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos, bool doSaturation = true) {
    if (plogger) {
      for (Var v : vars) {
        Lit l = getLit(v);
        SMALL c = getCoef(l);
        if (l == 0) continue;
        if (isUnit(level, l))
          proofBuffer << (l < 0 ? "x" : "~x") << v << " " << proofMult(c) << "+ ";
        else if (isUnit(level, -l))
          proofBuffer << plogger->unitIDs[pos[v]] << " " << proofMult(c) << "+ ";
      }
    }
    int j = 0;
    for (int i = 0; i < (int)vars.size(); ++i) {
      Var v = vars[i];
      if (coefs[v] == 0)
        remove(v);
      else if (isUnit(level, v)) {
        rhs -= coefs[v];
        if (coefs[v] > 0) degree -= coefs[v];
        remove(v);
      } else if (isUnit(level, -v)) {
        if (coefs[v] < 0) degree += coefs[v];
        remove(v);
      } else
        vars[j++] = v;
    }
    vars.resize(j);
    if (doSaturation) saturate();
  }

  bool hasNoUnits(const IntVecIt& level) const {
    for (Var v : vars)
      if (isUnit(level, v) || isUnit(level, -v)) return false;
    return true;
  }

  // @post: mutates order of vars
  void removeZeroes() {
    for (int i = 0; i < (int)vars.size(); ++i) {
      Var v = vars[i];
      if (coefs[v] == 0) {
        remove(v);
        aux::swapErase(vars, i--);
      }
    }
  }

  bool hasNoZeroes() const {
    for (Var v : vars)
      if (coefs[v] == 0) return false;
    return true;
  }

  // @post: preserves order of vars
  void saturate(const std::vector<Var>& vs) {
    if (plogger && !isSaturated()) proofBuffer << "s ";  // log saturation only if it modifies the constraint
    if (degree <= 0) {  // NOTE: does not call reset(0), as we do not want to reset the buffer
      for (Var v : vars) remove(v);
      vars.clear();
      rhs = 0;
      degree = 0;
      return;
    }
    for (Var v : vs) {
      if (coefs[v] < -getDegree())
        rhs -= coefs[v] + degree, coefs[v] = -degree;
      else
        coefs[v] = std::min<LARGE>(coefs[v], degree);
    }
    assert(isSaturated());
  }

  void saturate() { saturate(vars); }

  bool isSaturated() const {
    for (Var v : vars)
      if (rs::abs(coefs[v]) > getDegree()) return false;
    return true;
  }

  void invert() {
    rhs = -rhs;
    for (Var v : vars) coefs[v] = -coefs[v];
    degree = calcDegree();
  }

  template <typename S, typename L>
  void addUp(ConstrExp<S, L>& c, const SMALL& cmult = 1, const SMALL& thismult = 1) {
    assert(cmult >= 1);
    assert(thismult >= 1);
    if (plogger) proofBuffer << proofMult(thismult) << c.proofBuffer.str() << proofMult(cmult) << "+ ";
    if (thismult > 1) {
      degree *= thismult;
      rhs *= thismult;
      for (Var v : vars) coefs[v] *= thismult;
    }
    rhs += (LARGE)cmult * (LARGE)c.getRhs();
    degree += (LARGE)cmult * (LARGE)c.getDegree();
    for (Var v : c.vars) {
      assert(v < (Var)coefs.size());
      assert(v > 0);
      SMALL val = cmult * c.coefs[v];
      if (!used[v]) {
        assert(coefs[v] == 0);
        vars.push_back(v);
        coefs[v] = val;
        used[v] = true;
      } else {
        if ((coefs[v] < 0) != (val < 0)) degree -= std::min(rs::abs(coefs[v]), rs::abs(val));
        coefs[v] += val;
      }
    }
  }

  void saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening) {
    removeZeroes();
    saturate();
    if (degree >= (LARGE)INF) {
      LARGE div = aux::ceildiv<LARGE>(degree, INF - 1);
      weakenNonDivisibleNonFalsifieds(level, div, fullWeakening, 0);
      divideRoundUp(div);
      saturate();
    }
    assert(degree < (LARGE)INF);
  }

  void multiply(const SMALL& m) {
    assert(m > 0);
    if (m == 1) return;
    if (plogger) proofBuffer << proofMult(m);
    for (Var v : vars) coefs[v] *= m;
    rhs *= m;
    degree *= m;
  }

  void divide(const LARGE& d) {
    if (plogger) proofBuffer << d << " d ";
    for (Var v : vars) {
      assert(coefs[v] % d == 0);
      coefs[v] /= d;
    }
    // NOTE: as all coefficients are divisible by d, we can aux::ceildiv the rhs and the degree
    rhs = aux::ceildiv_safe(rhs, d);
    degree = aux::ceildiv_safe(degree, d);
  }

  void divideRoundUp(const LARGE& d) {
    assert(d > 0);
    if (d == 1) return;
    for (Var v : vars) {
      if (coefs[v] % d == 0) continue;
      weaken((coefs[v] < 0 ? 0 : d) - aux::mod_safe<LARGE>(coefs[v], d), v);
    }
    divide(d);
  }

  void weakenDivideRound(const IntVecIt& level, Lit l, bool maxdiv, bool fullWeakening) {
    assert(getCoef(l) > 0);
    LARGE div = maxdiv ? getCoef(l) : getSlack(level) + 1;
    if (div <= 1) return;
    weakenNonDivisibleNonFalsifieds(level, div, fullWeakening, l);
    divideRoundUp(div);
    saturate();
  }

  void applyMIR(const LARGE& d, std::function<Lit(Var)> toLit) {
    assert(d > 0);
    LARGE tmpRhs = rhs;
    for (Var v : vars)
      if (toLit(v) < 0) tmpRhs -= coefs[v];
    LARGE bmodd = aux::mod_safe(tmpRhs, d);
    rhs = bmodd * aux::ceildiv_safe(tmpRhs, d);
    for (Var v : vars) {
      if (toLit(v) < 0) {
        coefs[v] = -(bmodd * aux::floordiv_safe(-coefs[v], d) + std::min(aux::mod_safe(-coefs[v], d), bmodd));
        rhs += coefs[v];
      } else
        coefs[v] = bmodd * aux::floordiv_safe(coefs[v], d) + std::min(aux::mod_safe(coefs[v], d), bmodd);
    }
    degree = calcDegree();
  }

  bool divideByGCD() {
    assert(isSaturated());
    assert(hasNoZeroes());
    if (vars.size() == 0 || rs::abs(coefs[vars.back()]) == 1) return false;
    SMALL _gcd = rs::abs(coefs[vars.back()]);  // smallest if sorted in decreasing order
    for (int i = vars.size() - 2; i >= 0; --i) {
      _gcd = rs::gcd(_gcd, rs::abs(coefs[vars[i]]));
      if (_gcd == 1) return false;
    }
    assert(_gcd > 1);
    divide(_gcd);
    return true;
  }

  // NOTE: only equivalence preserving operations!
  void postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst, Stats& sts) {
    removeUnitsAndZeroes(level, pos);  // NOTE: also saturates
    if (sortFirst) sortInDecreasingCoefOrder();
    if (divideByGCD()) ++sts.NGCD;
    if (simplifyToCardinality(true)) ++sts.NCARDDETECT;
  }

  // NOTE: also removes encountered zeroes and changes variable order
  AssertionStatus isAssertingBefore(const IntVecIt& level, int lvl) {
    assert(lvl >= 0);
    assert(isSaturated());
    LARGE slack = -degree;
    SMALL largestCoef = 0;
    for (int i = vars.size() - 1; i >= 0; --i) {
      Var v = vars[i];
      if (coefs[v] == 0) {
        remove(v);
        aux::swapErase(vars, i);
        continue;
      }
      Lit l = coefs[v] < 0 ? -v : v;
      if (level[-l] < lvl) continue;  // falsified lit
      SMALL c = rs::abs(coefs[v]);
      if (level[l] >= lvl) largestCoef = std::max(largestCoef, c);  // unknown lit
      slack += c;
      int mid = (vars.size() + i) / 2;  // move non-falsifieds to the back for efficiency in next call
      vars[i] = vars[mid];
      vars[mid] = v;
      if (slack >= getDegree()) return AssertionStatus::NONASSERTING;
    }
    if (slack >= largestCoef)
      return AssertionStatus::NONASSERTING;
    else if (slack >= 0)
      return AssertionStatus::ASSERTING;
    else
      return AssertionStatus::FALSIFIED;
  }

  // @return: earliest decision level that propagates a variable
  int getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const {
    assert(hasNoZeroes());
    assert(isSortedInDecreasingCoefOrder());
    assert(hasNoUnits(level));
    // calculate slack at level 0
    LARGE slack = -rhs;
    for (Var v : vars) slack += std::max(0, coefs[v]);
    if (slack < 0) return -1;

    // create useful datastructures
    std::vector<Lit> litsByPos;
    litsByPos.reserve(vars.size());
    for (Var v : vars) {
      Lit l = getLit(v);
      assert(l != 0);
      if (isFalse(level, l)) litsByPos.push_back(-l);
    }
    std::sort(litsByPos.begin(), litsByPos.end(), [&](Lit l1, Lit l2) { return pos[toVar(l1)] < pos[toVar(l2)]; });

    // calculate earliest propagating decision level by decreasing slack one decision level at a time
    auto posIt = litsByPos.cbegin();
    auto coefIt = vars.cbegin();
    int assertionLevel = 0;
    while (true) {
      while (posIt != litsByPos.cend() && level[*posIt] <= assertionLevel) {
        slack -= rs::abs(coefs[rs::abs(*posIt)]);
        ++posIt;
      }
      if (slack < 0) return assertionLevel - 1;
      while (coefIt != vars.cend() && assertionLevel >= level[getLit(*coefIt)]) ++coefIt;
      if (coefIt == vars.cend()) return INF;  // no assertion level
      if (slack < rs::abs(coefs[*coefIt])) return assertionLevel;
      if (posIt == litsByPos.cend()) return INF;  // slack will no longer decrease
      assertionLevel = level[*posIt];
    }
  }

  // @post: preserves order after removeZeroes()
  void weakenNonImplied(const IntVecIt& level, const LARGE& slack, Stats& sts) {
    for (Var v : vars)
      if (coefs[v] != 0 && rs::abs(coefs[v]) <= slack && !falsified(level, v)) {
        weaken(-coefs[v], v);
        ++sts.NWEAKENEDNONIMPLIED;
      }
    // TODO: always saturate?
  }

  // @post: preserves order after removeZeroes()
  bool weakenNonImplying(const IntVecIt& level, const SMALL& propCoef, const LARGE& slack, Stats& sts) {
    LARGE slk = slack;
    assert(hasNoZeroes());
    assert(isSortedInDecreasingCoefOrder());
    long long oldCount = sts.NWEAKENEDNONIMPLYING;
    for (int i = vars.size() - 1; i >= 0 && slk + rs::abs(coefs[vars[i]]) < propCoef; --i) {
      Var v = vars[i];
      if (falsified(level, v)) {
        slk += rs::abs(coefs[v]);
        weaken(-coefs[v], v);
        ++sts.NWEAKENEDNONIMPLYING;
      }
    }
    bool changed = oldCount != sts.NWEAKENEDNONIMPLYING;
    if (changed) saturate();  // TODO: always saturate?
    return changed;
  }

  // @post: preserves order after removeZeroes()
  void heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, const LARGE& slack, Stats& sts) {
    LARGE slk = slack;
    assert(slk == getSlack(level));
    if (slk < 0) return;  // no propagation, no idea what to weaken
    assert(isSortedInDecreasingCoefOrder());
    Var v_prop = -1;
    for (int i = vars.size() - 1; i >= 0; --i) {
      Var v = vars[i];
      if (rs::abs(coefs[v]) > slk && isUnknown(pos, v)) {
        v_prop = v;
        break;
      }
    }
    if (v_prop == -1) return;  // no propagation, no idea what to weaken
    if (weakenNonImplying(level, rs::abs(coefs[v_prop]), slk, sts)) slk = getSlack(level);  // slack changed
    assert(slk < rs::abs(coefs[v_prop]));
    weakenNonImplied(level, slk, sts);
  }

  // @post: preserves order
  template <typename T>
  void weakenSmalls(const T& limit) {
    for (Var v : vars)
      if (rs::abs(coefs[v]) < limit) weaken(-coefs[v], v);
    saturate();
  }

  void weakenNonDivisibleNonFalsifieds(const IntVecIt& level, const LARGE& div, bool fullWeakening, Lit asserting) {
    assert(div > 0);
    if (div == 1) return;
    if (fullWeakening) {
      for (Var v : vars)
        if (coefs[v] % div != 0 && !falsified(level, v) && v != toVar(asserting)) weaken(-coefs[v], v);
    } else {
      for (Var v : vars)
        if (coefs[v] % div != 0 && !falsified(level, v)) weaken(-(coefs[v] % div), v);
    }
  }

  LARGE absCoeffSum() const {
    LARGE result = 0;
    for (Var v : vars) result += rs::abs(coefs[v]);
    return result;
  }

  // @post: preserves order of vars
  bool simplifyToCardinality(bool equivalencePreserving) {
    assert(isSaturated());
    assert(isSortedInDecreasingCoefOrder());
    assert(hasNoZeroes());
    if (vars.size() == 0 || rs::abs(coefs[vars[0]]) == 1) return false;  // already cardinality
    if (degree <= 0) return false;

    int largeCoefsNeeded = 0;
    LARGE largeCoefSum = 0;
    while (largeCoefsNeeded < (int)vars.size() && largeCoefSum < getDegree()) {
      largeCoefSum += rs::abs(coefs[vars[largeCoefsNeeded]]);
      ++largeCoefsNeeded;
    }
    assert(largeCoefsNeeded > 0);
    if (largeCoefSum < getDegree()) {
      for (Var v : vars) weaken(-coefs[v], v);
      return true;  // trivial inconsistency
    }

    int skippable = vars.size();  // counting backwards
    if (equivalencePreserving) {
      LARGE smallCoefSum = 0;
      for (int i = 1; i <= largeCoefsNeeded; ++i) smallCoefSum += rs::abs(coefs[vars[vars.size() - i]]);
      if (smallCoefSum < getDegree()) return false;
      // else, we have an equivalent cardinality constraint
    } else {
      LARGE wiggleroom = degree - largeCoefSum + rs::abs(coefs[vars[largeCoefsNeeded - 1]]);
      assert(wiggleroom > 0);
      while (skippable > 0 && wiggleroom > rs::abs(coefs[vars[skippable - 1]])) {
        --skippable;
        wiggleroom -= rs::abs(coefs[vars[skippable]]);
      }
    }
    assert(skippable >= largeCoefsNeeded);

    if (plogger) {
      SMALL div_coef = rs::abs(coefs[vars[largeCoefsNeeded - 1]]);
      for (int i = 0; i < largeCoefsNeeded; ++i) {  // partially weaken large vars
        Lit l = getLit(vars[i]);
        SMALL d = getCoef(l) - div_coef;
        proofBuffer << (l > 0 ? "~x" : "x") << toVar(l) << " " << proofMult(d) << "+ ";
      }
      for (int i = skippable; i < (int)vars.size(); ++i) {  // weaken small vars
        Lit l = getLit(vars[i]);
        SMALL d = getCoef(l);
        proofBuffer << (l > 0 ? "~x" : "x") << toVar(l) << " " << proofMult(d) << "+ ";
      }
      if (div_coef > 1) proofBuffer << div_coef << " d ";
    }
    rhs = largeCoefsNeeded;
    degree = largeCoefsNeeded;
    for (int i = skippable; i < (int)vars.size(); ++i) remove(vars[i]);
    vars.resize(skippable);
    for (int i = 0; i < (int)vars.size(); ++i) {
      SMALL& c = coefs[vars[i]];
      if (c < 0) {
        c = -1;
        --rhs;
      } else
        c = 1;
    }
    return true;
  }

  bool isCardinality() const {
    for (Var v : vars)
      if (rs::abs(coefs[v]) > 1) return false;
    return true;
  }

  void sortInDecreasingCoefOrder() {
    std::sort(vars.begin(), vars.end(), [&](Var v1, Var v2) { return rs::abs(coefs[v1]) > rs::abs(coefs[v2]); });
  }

  bool isSortedInDecreasingCoefOrder() const {
    for (int i = 1; i < (int)vars.size(); ++i)
      if (rs::abs(coefs[vars[i - 1]]) < rs::abs(coefs[vars[i]])) return false;
    return true;
  }

  ID logAsInput() {
    assert(plogger);
    toStreamAsOPB(plogger->formula_out);
    plogger->proof_out << "l " << ++plogger->last_formID << "\n";
    ID id = ++plogger->last_proofID;
    resetBuffer(id);  // ensure consistent proofBuffer
    return id;
  }

  ID logProofLine() {
    assert(plogger);
    std::string buffer = proofBuffer.str();
    assert(buffer.back() == ' ');
    long long spacecount = 0;
    for (char const& c : buffer) {
      spacecount += (c == ' ');
      if (spacecount > 1) break;
    }
    ID id;
    if (spacecount > 1) {  // non-trivial line
      id = ++plogger->last_proofID;
      plogger->proof_out << "p " << buffer << "0\n";
      resetBuffer(id);
    } else {  // line is just one id, don't print it
      id = std::stol(buffer);
    }
#if !NDEBUG
    plogger->proof_out << "e " << id << " ";
    toStreamAsOPB(plogger->proof_out);
#endif
    return id;
  }

  ID logProofLineWithInfo(std::string&& info, const Stats& sts) {
    assert(plogger);
    _unused(info);
    _unused(sts);
#if !NDEBUG
    plogger->logComment(info, sts);
#endif
    return logProofLine();
  }

  // @pre: reducible to unit over v
  void logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit, const Stats& sts) {
    assert(plogger);
    // reduce to unit over v
    removeUnitsAndZeroes(level, pos);
    assert(getLit(v_unit) != 0);
    for (Var v : vars)
      if (v != v_unit) weaken(-coefs[v], v);
    assert(degree > 0);
    LARGE d = std::max<LARGE>(rs::abs(coefs[v_unit]), getDegree());
    if (d > 1) proofBuffer << d << " d ";
    if (coefs[v_unit] > 0) {
      coefs[v_unit] = 1;
      rhs = 1;
    } else {
      coefs[v_unit] = -1;
      rhs = 0;
    }
    degree = 1;
    plogger->unitIDs.push_back(logProofLineWithInfo("Unit", sts));
  }

  void logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts) {
    assert(plogger);
    removeUnitsAndZeroes(level, pos);
    assert(getSlack(level) < 0);
    ID id = logProofLineWithInfo("Inconsistency", sts);
    plogger->proof_out << "c " << id << " 0" << std::endl;
  }

  void toStreamAsOPB(std::ofstream& o) const {
    std::vector<Var> vs = vars;
    std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
    for (Var v : vs) {
      Lit l = getLit(v);
      if (l == 0) continue;
      o << "+" << getCoef(l) << (l < 0 ? " ~x" : " x") << v << " ";
    }
    o << ">= " << getDegree() << " ;\n";
  }

  void toStreamWithAssignment(std::ostream& o, const IntVecIt& level, const std::vector<int>& pos) const {
    std::vector<Var> vs = vars;
    std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
    for (Var v : vs) {
      Lit l = getLit(v);
      if (l == 0) continue;
      o << getCoef(l) << "x" << l
        << (isUnknown(pos, l) ? "u"
                              : (isFalse(level, l) ? "f" + std::to_string(level[-l]) : "t" + std::to_string(level[l])))
        << " ";
    }
    o << ">= " << getDegree() << "(" << getSlack(level) << ")";
  }
};

template <typename S, typename L>
std::ostream& operator<<(std::ostream& o, const ConstrExp<S, L>& C) {
  std::vector<Var> vars = C.vars;
  std::sort(vars.begin(), vars.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vars) {
    Lit l = C.coefs[v] < 0 ? -v : v;
    o << C.getCoef(l) << "x" << l << " ";
  }
  o << ">= " << C.getDegree();
  return o;
}

using ConstrExp32 = ConstrExp<int, long long>;
using ConstrExp64 = ConstrExp<long long, __int128>;
using ConstrExp96 = ConstrExp<__int128, __int128>;
// using ConstrExpArb = ConstrExp<bigint, bigint>;
