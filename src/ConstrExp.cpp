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

#include "ConstrExp.hpp"
#include <algorithm>
#include <functional>
#include "Constr.hpp"
#include "ConstrSimple.hpp"
#include "IntSet.hpp"
#include "SolverStructs.hpp"
#include "Stats.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

const int limit32 = 1e9;
const long long limit64 = 1e18;
const int128 limit96 = 1e27;

template <typename SMALL, typename LARGE>
ConstrExp<SMALL, LARGE>::ConstrExp(ConstrExpPool<ConstrExp<SMALL, LARGE>>& cep) : pool(cep) {
  reset();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::release() {
  pool.release(*this);
}

template <typename SMALL, typename LARGE>
ConstrExpSuper& ConstrExp<SMALL, LARGE>::reduce(ConstrExpPools& ce) const {
  Representation rep = minRepresentation();
  if (rep == Representation::B32) {
    ConstrExp32& result = ce.take32();
    copyTo(result);
    return result;
  } else if (rep == Representation::B64) {
    ConstrExp64& result = ce.take64();
    copyTo(result);
    return result;
  } else if (rep == Representation::B96) {
    ConstrExp96& result = ce.take96();
    copyTo(result);
    return result;
  } else {
    assert(rep == Representation::ARB);
    ConstrExpArb& result = ce.takeArb();
    copyTo(result);
    return result;
  }
}

template <typename SMALL, typename LARGE>
CRef ConstrExp<SMALL, LARGE>::toConstr(ConstraintAllocator& ca, bool locked, ID id) const {
  assert(isSortedInDecreasingCoefOrder());
  assert(isSaturated());
  assert(hasNoZeroes());
  assert(vars.size() > 0);
  assert(!isTautology());
  assert(!isInconsistency());

  CRef result = CRef{ca.at};
  if (options.clauseProp && isClause()) {
    ca.alloc<Clause>(vars.size())->initialize(*this, locked, id);
  } else if (options.cardProp && isCardinality()) {
    ca.alloc<Cardinality>(vars.size())->initialize(*this, locked, id);
  } else {
    LARGE maxCoef = rs::abs(coefs[vars[0]]);
    if (maxCoef > limit96) {
      ca.alloc<Arbitrary>(vars.size())->initialize(*this, locked, id);
    } else {
      LARGE watchSum = -degree;
      unsigned int minWatches = 1;  // sorted per decreasing coefs, so we can skip the first, largest coef
      for (; minWatches < vars.size() && watchSum < 0; ++minWatches) watchSum += rs::abs(coefs[vars[minWatches]]);
      bool useCounting = options.countingProp == 1 || options.countingProp > (1 - minWatches / (double)vars.size());
      if (maxCoef <= limit32) {
        if (useCounting) {
          ca.alloc<Counting32>(vars.size())->initialize(*this, locked, id);
        } else {
          ca.alloc<Watched32>(vars.size())->initialize(*this, locked, id);
        }
      } else if (maxCoef <= limit64) {
        if (useCounting) {
          ca.alloc<Counting64>(vars.size())->initialize(*this, locked, id);
        } else {
          ca.alloc<Watched64>(vars.size())->initialize(*this, locked, id);
        }
      } else {
        assert(maxCoef <= limit96);
        if (useCounting) {
          ca.alloc<Counting96>(vars.size())->initialize(*this, locked, id);
        } else {
          ca.alloc<Watched96>(vars.size())->initialize(*this, locked, id);
        }
      }
    }
  }
  return result;
}

template <typename SMALL, typename LARGE>
std::unique_ptr<ConstrSimpleSuper> ConstrExp<SMALL, LARGE>::toSimple() const {
  std::unique_ptr<ConstrSimple<SMALL, LARGE>> result = std::make_unique<ConstrSimple<SMALL, LARGE>>();
  result->rhs = rhs;
  result->terms.reserve(vars.size());
  for (Var v : vars)
    if (coefs[v] != 0) result->terms.emplace_back(coefs[v], v);
  if (plogger) result->proofLine = proofBuffer.str();
  result->orig = orig;
  return result;
};

template <typename SMALL, typename LARGE>
Representation ConstrExp<SMALL, LARGE>::minRepresentation() const {
  LARGE maxVal = std::max<LARGE>(getLargestCoef(), std::max(degree, rs::abs(rhs)) / INF);
  if (maxVal <= limit32) {
    return Representation::B32;
  } else if (maxVal <= limit64) {
    return Representation::B64;
  } else if (maxVal <= limit96) {
    return Representation::B96;
  } else {
    return Representation::ARB;
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::remove(Var v) {
  assert(used[v]);
  coefs[v] = 0;
  used[v] = false;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::increasesSlack(const IntVecIt& level, Var v) const {
  return isTrue(level, v) || (!isFalse(level, v) && coefs[v] > 0);
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::calcDegree() const {
  LARGE res = rhs;
  for (Var v : vars) res -= std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
  return res;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::calcRhs() const {
  LARGE res = degree;
  for (Var v : vars) res += std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
  return res;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::testConstraint() const {
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

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::resize(size_t s) {
  if (s > coefs.size()) {
    coefs.resize(s, 0);
    used.resize(s, false);
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::resetBuffer(ID proofID) {
  assert(plogger);
  assert(proofID != ID_Undef);
  assert(proofID != ID_Unsat);
  proofBuffer.clear();
  proofBuffer.str(std::string());
  proofBuffer << proofID << " ";
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::initializeLogging(std::shared_ptr<Logger>& l) {
  assert(isReset());
  plogger = l;
  if (plogger) resetBuffer();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::stopLogging() {
  proofBuffer.clear();
  plogger.reset();
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isReset() const {
  return vars.size() == 0 && rhs == 0 && degree == 0;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::reset() {
  for (Var v : vars) remove(v);
  vars.clear();
  rhs = 0;
  degree = 0;
  orig = Origin::UNKNOWN;
  if (plogger) resetBuffer();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::addRhs(const LARGE& r) {
  rhs += r;
  degree += r;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getRhs() const {
  return rhs;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getDegree() const {
  return degree;
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getCoef(Lit l) const {
  assert((unsigned int)toVar(l) < coefs.size());
  return l < 0 ? -coefs[-l] : coefs[l];
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getLargestCoef() const {
  SMALL result = 0;
  for (Var v : vars) result = std::max(result, rs::abs(coefs[v]));
  return result;
}

template <typename SMALL, typename LARGE>
Lit ConstrExp<SMALL, LARGE>::getLit(Lit l) const {  // NOTE: answer of 0 means coef 0
  Var v = toVar(l);
  assert(v < (Var)coefs.size());
  return (coefs[v] == 0) ? 0 : (coefs[v] < 0 ? -v : v);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::falsified(const IntVecIt& level, Var v) const {
  assert(v > 0);
  assert((getLit(v) != 0 && !isFalse(level, getLit(v))) == (coefs[v] > 0 && !isFalse(level, v)) ||
         (coefs[v] < 0 && !isTrue(level, v)));
  return (coefs[v] > 0 && isFalse(level, v)) || (coefs[v] < 0 && isTrue(level, v));
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getSlack(const IntVecIt& level) const {
  LARGE slack = -rhs;
  for (Var v : vars)
    if (increasesSlack(level, v)) slack += coefs[v];
  return slack;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getSlack(const IntSet& assumptions) const {
  LARGE slack = -rhs;
  for (Var v : vars)
    if (assumptions.has(v) || (!assumptions.has(-v) && coefs[v] > 0)) slack += coefs[v];
  return slack;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasNegativeSlack(const IntVecIt& level) const {
  return getSlack(level) < 0;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isTautology() const {
  return getDegree() <= 0;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isInconsistency() const {
  return getDegree() > absCoeffSum();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::addLhs(const SMALL& cf, Lit l) {  // add c*(l>=0) if c>0 and -c*(-l>=0) if c<0
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

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weaken(const SMALL& m, Var v) {  // add m*(v>=0) if m>0 and -m*(-v>=-1) if m<0
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
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos,
                                                   bool doSaturation) {
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

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasNoUnits(const IntVecIt& level) const {
  for (Var v : vars)
    if (isUnit(level, v) || isUnit(level, -v)) return false;
  return true;
}

// @post: mutates order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::removeZeroes() {
  for (int i = 0; i < (int)vars.size(); ++i) {
    Var v = vars[i];
    if (coefs[v] == 0) {
      remove(v);
      aux::swapErase(vars, i--);
    }
  }
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasNoZeroes() const {
  for (Var v : vars)
    if (coefs[v] == 0) return false;
  return true;
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturate(const std::vector<Var>& vs) {
  if (plogger && !isSaturated()) proofBuffer << "s ";  // log saturation only if it modifies the constraint
  if (degree <= 0) {  // NOTE: does not call reset(0), as we do not want to reset the buffer
    for (Var v : vars) remove(v);
    vars.clear();
    rhs = 0;
    degree = 0;
    return;
  }
  for (Var v : vs) {
    if (coefs[v] < -degree)
      rhs -= coefs[v] + degree, coefs[v] = -degree;
    else
      coefs[v] = std::min<LARGE>(coefs[v], degree);
  }
  assert(isSaturated());
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturate() {
  saturate(vars);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSaturated() const {
  for (Var v : vars)
    if (rs::abs(coefs[v]) > degree) return false;
  return true;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::invert() {
  rhs = -rhs;
  for (Var v : vars) coefs[v] = -coefs[v];
  degree = calcDegree();
}

// also removes zeroes
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening, int bitOverflow,
                                                     int bitReduce) {
  removeZeroes();
  if (bitOverflow == 0) {
    saturate();
    return;
  }
  assert(bitReduce > 0);
  SMALL largest = 0;
  for (Var v : vars) {
    largest = std::max(largest, rs::abs(coefs[v]));
  }
  largest = std::min<LARGE>(largest, degree);  // takes saturated coefficients into account
  if (largest == 0) return;
  if ((int)rs::msb(largest) >= bitOverflow) {
    LARGE cutoff = 2;
    cutoff = rs::pow(cutoff, bitReduce) - 1;
    LARGE div = aux::ceildiv<LARGE>(largest, cutoff);
    assert(aux::ceildiv<LARGE>(largest, div) <= cutoff);
    weakenNonDivisibleNonFalsifieds(level, div, fullWeakening, 0);
    divideRoundUp(div);
  }
  saturate();
}

// also removes zeroes
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturateAndFixOverflowRational(const std::vector<double>& lpSolution) {
  removeZeroes();
  LARGE maxRhs = std::max(getDegree(), rs::abs(getRhs()));
  if (maxRhs >= INFLPINT) {
    LARGE d = aux::ceildiv<BigVal>(maxRhs, INFLPINT - 1);
    assert(d > 1);
    for (Var v : vars) {
      LARGE rem = aux::mod_safe<LARGE>(coefs[v], d);
      if (rem == 0) continue;
      double d_double = static_cast<double>(d);
      if (lpSolution[v] == 0 || (std::isfinite(d_double) && d_double * lpSolution[v] < static_cast<double>(rem)))
        weaken(d - rem, v);
      else
        weaken(-rem, v);
    }
    divide(d);
  }
  saturate();
  assert(getDegree() < INFLPINT);
  assert(getRhs() < INFLPINT);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::fitsInDouble() const {
  return isSaturated() && getDegree() < INFLPINT && getRhs() < INFLPINT;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::multiply(const SMALL& m) {
  assert(m > 0);
  if (m == 1) return;
  if (plogger) proofBuffer << proofMult(m);
  for (Var v : vars) coefs[v] *= m;
  rhs *= m;
  degree *= m;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::divide(const LARGE& d) {
  if (plogger) proofBuffer << d << " d ";
  for (Var v : vars) {
    assert(coefs[v] % d == 0);
    coefs[v] /= d;
  }
  // NOTE: as all coefficients are divisible by d, we can aux::ceildiv the rhs and the degree
  rhs = aux::ceildiv_safe(rhs, d);
  degree = aux::ceildiv_safe(degree, d);
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::divideRoundUp(const LARGE& d) {
  assert(d > 0);
  if (d == 1) return;
  for (Var v : vars) {
    if (coefs[v] % d == 0) continue;
    weaken((coefs[v] < 0 ? 0 : d) - aux::mod_safe<LARGE>(coefs[v], d), v);
  }
  divide(d);
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenDivideRound(const IntVecIt& level, Lit l, bool slackdiv, bool fullWeakening) {
  assert(getCoef(l) > 0);
  LARGE div = slackdiv ? getSlack(level) + 1 : getCoef(l);
  if (div <= 1) return;
  weakenNonDivisibleNonFalsifieds(level, div, fullWeakening, l);
  divideRoundUp(div);
  saturate();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonDivisibleNonFalsifieds(const IntVecIt& level, const LARGE& div,
                                                              bool fullWeakening, Lit asserting) {
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

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::applyMIR(const LARGE& d, std::function<Lit(Var)> toLit) {
  assert(d > 0);
  LARGE tmpRhs = rhs;
  for (Var v : vars)
    if (toLit(v) < 0) tmpRhs -= coefs[v];
  LARGE bmodd = aux::mod_safe(tmpRhs, d);
  rhs = bmodd * aux::ceildiv_safe(tmpRhs, d);
  for (Var v : vars) {
    if (toLit(v) < 0) {
      coefs[v] =
          -(bmodd * aux::floordiv_safe<LARGE>(-coefs[v], d) + std::min(aux::mod_safe<LARGE>(-coefs[v], d), bmodd));
      rhs += coefs[v];
    } else
      coefs[v] = bmodd * aux::floordiv_safe<LARGE>(coefs[v], d) + std::min(aux::mod_safe<LARGE>(coefs[v], d), bmodd);
  }
  degree = calcDegree();
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::divideByGCD() {
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
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst,
                                          Stats& sts) {
  removeUnitsAndZeroes(level, pos);  // NOTE: also saturates
  if (sortFirst) sortInDecreasingCoefOrder();
  if (divideByGCD()) ++sts.NGCD;
  if (simplifyToCardinality(true)) ++sts.NCARDDETECT;
}

// NOTE: also removes encountered zeroes and changes variable order
template <typename SMALL, typename LARGE>
AssertionStatus ConstrExp<SMALL, LARGE>::isAssertingBefore(const IntVecIt& level, int lvl) {
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
    if (slack >= degree) return AssertionStatus::NONASSERTING;
  }
  if (slack >= largestCoef)
    return AssertionStatus::NONASSERTING;
  else if (slack >= 0)
    return AssertionStatus::ASSERTING;
  else
    return AssertionStatus::FALSIFIED;
}

// @return: earliest decision level that propagates a variable
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const {
  assert(hasNoZeroes());
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoUnits(level));
  // calculate slack at level 0
  LARGE slack = -rhs;
  for (Var v : vars) slack += std::max<SMALL>(0, coefs[v]);
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
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonImplied(const IntVecIt& level, const LARGE& slack, Stats& sts) {
  for (Var v : vars)
    if (coefs[v] != 0 && rs::abs(coefs[v]) <= slack && !falsified(level, v)) {
      weaken(-coefs[v], v);
      ++sts.NWEAKENEDNONIMPLIED;
    }
  // TODO: always saturate?
}

// @post: preserves order after removeZeroes()
template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::weakenNonImplying(const IntVecIt& level, const SMALL& propCoef, const LARGE& slack,
                                                Stats& sts) {
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
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, Stats& sts) {
  LARGE slk = getSlack(level);
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

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::absCoeffSum() const {
  LARGE result = 0;
  for (Var v : vars) result += rs::abs(coefs[v]);
  return result;
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::simplifyToCardinality(bool equivalencePreserving) {
  assert(isSaturated());
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  if (vars.size() == 0 || rs::abs(coefs[vars[0]]) == 1) return false;  // already cardinality
  if (degree <= 0) return false;

  int largeCoefsNeeded = 0;
  LARGE largeCoefSum = 0;
  while (largeCoefsNeeded < (int)vars.size() && largeCoefSum < degree) {
    largeCoefSum += rs::abs(coefs[vars[largeCoefsNeeded]]);
    ++largeCoefsNeeded;
  }
  assert(largeCoefsNeeded > 0);
  if (largeCoefSum < degree) {
    for (Var v : vars) weaken(-coefs[v], v);
    return true;  // trivial inconsistency
  }

  int skippable = vars.size();  // counting backwards
  if (equivalencePreserving) {
    LARGE smallCoefSum = 0;
    for (int i = 1; i <= largeCoefsNeeded; ++i) smallCoefSum += rs::abs(coefs[vars[vars.size() - i]]);
    if (smallCoefSum < degree) return false;
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

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isCardinality() const {
  for (Var v : vars)
    if (rs::abs(coefs[v]) > 1) return false;
  return true;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isClause() const {
  return degree == 1;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::sortInDecreasingCoefOrder() {
  std::sort(vars.begin(), vars.end(), [&](Var v1, Var v2) { return rs::abs(coefs[v1]) > rs::abs(coefs[v2]); });
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSortedInDecreasingCoefOrder() const {
  for (int i = 1; i < (int)vars.size(); ++i)
    if (rs::abs(coefs[vars[i - 1]]) < rs::abs(coefs[vars[i]])) return false;
  return true;
}

template <typename SMALL, typename LARGE>
ID ConstrExp<SMALL, LARGE>::logAsInput() {
  assert(plogger);
  toStreamAsOPB(plogger->formula_out);
  plogger->proof_out << "l " << ++plogger->last_formID << "\n";
  ID id = ++plogger->last_proofID;
  resetBuffer(id);  // ensure consistent proofBuffer
  return id;
}

template <typename SMALL, typename LARGE>
ID ConstrExp<SMALL, LARGE>::logProofLine() {
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

template <typename SMALL, typename LARGE>
ID ConstrExp<SMALL, LARGE>::logProofLineWithInfo([[maybe_unused]] std::string&& info,
                                                 [[maybe_unused]] const Stats& sts) {
  assert(plogger);
#if !NDEBUG
  plogger->logComment(info, sts);
#endif
  return logProofLine();
}

// @pre: reducible to unit over v
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit,
                                      const Stats& sts) {
  assert(plogger);
  // reduce to unit over v
  removeUnitsAndZeroes(level, pos);
  assert(getLit(v_unit) != 0);
  for (Var v : vars)
    if (v != v_unit) weaken(-coefs[v], v);
  assert(degree > 0);
  LARGE d = std::max<LARGE>(rs::abs(coefs[v_unit]), degree);
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

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts) {
  assert(plogger);
  removeUnitsAndZeroes(level, pos);
  assert(hasNegativeSlack(level));
  ID id = logProofLineWithInfo("Inconsistency", sts);
  plogger->proof_out << "c " << id << " 0" << std::endl;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamAsOPB(std::ofstream& o) const {
  std::vector<Var> vs = vars;
  std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vs) {
    Lit l = getLit(v);
    if (l == 0) continue;
    o << "+" << getCoef(l) << (l < 0 ? " ~x" : " x") << v << " ";
  }
  o << ">= " << degree << " ;\n";
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamWithAssignment(std::ostream& o, const IntVecIt& level,
                                                     const std::vector<int>& pos) const {
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
  o << ">= " << degree << "(" << getSlack(level) << ")";
}

template class ConstrExp<int, long long>;
template class ConstrExp<long long, int128>;
template class ConstrExp<int128, int128>;
template class ConstrExp<bigint, bigint>;

void ConstrExpPools::resize(size_t newn) {
  ce32s.resize(newn);
  ce64s.resize(newn);
  ce96s.resize(newn);
  ceArbs.resize(newn);
}

void ConstrExpPools::initializeLogging(std::shared_ptr<Logger> lgr) {
  ce32s.initializeLogging(lgr);
  ce64s.initializeLogging(lgr);
  ce96s.initializeLogging(lgr);
  ceArbs.initializeLogging(lgr);
}

template <>
ConstrExp32& ConstrExpPools::take<int, long long>() {
  return ce32s.take();
}
template <>
ConstrExp64& ConstrExpPools::take<long long, int128>() {
  return ce64s.take();
}
template <>
ConstrExp96& ConstrExpPools::take<int128, int128>() {
  return ce96s.take();
}
template <>
ConstrExpArb& ConstrExpPools::take<bigint, bigint>() {
  return ceArbs.take();
}

ConstrExp32& ConstrExpPools::take32() { return take<int, long long>(); }
ConstrExp64& ConstrExpPools::take64() { return take<long long, int128>(); }
ConstrExp96& ConstrExpPools::take96() { return take<int128, int128>(); }
ConstrExpArb& ConstrExpPools::takeArb() { return take<bigint, bigint>(); }
