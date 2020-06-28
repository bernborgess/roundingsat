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
#include <sstream>
#include "ConstrSimple.hpp"
#include "Logger.hpp"

struct IntSet;

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
  void remove(Var v);
  bool increasesSlack(const IntVecIt& level, Var v) const;
  LARGE calcDegree() const;
  LARGE calcRhs() const;
  bool testConstraint() const;
  bool falsified(const IntVecIt& level, Var v) const;

 public:
  ConstrExp() { reset(); }

  template <typename CF, typename DG>
  void init(const ConstrSimple<CF, DG>& sc) {
    // TODO: assert whether CF/DG can fit SMALL/LARGE? Not always possible.
    assert(isReset());
    addRhs(sc.rhs);
    for (const Term<CF>& t : sc.terms) {
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
    assert(out.coefs.size() == coefs.size());
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
  ConstrSimple<CF, DG> toSimpleCons() const {
    ConstrSimple<CF, DG> result;
    result.rhs = static_cast<DG>(rhs);
    result.terms.reserve(vars.size());
    for (Var v : vars)
      if (coefs[v] != 0) result.terms.emplace_back(static_cast<CF>(coefs[v]), v);
    if (plogger) result.proofLine = proofBuffer.str();
    result.orig = orig;
    return result;
  }

  void resize(size_t s);
  void resetBuffer(ID proofID = ID_Trivial);
  void initializeLogging(std::shared_ptr<Logger>& l);
  void stopLogging();

  template <typename T>
  std::string proofMult(const T& mult) {
    std::stringstream ss;
    if (mult != 1) ss << mult << " * ";
    return ss.str();
  }

  bool isReset() const;
  void reset();

  LARGE getRhs() const;
  LARGE getDegree() const;
  SMALL getCoef(Lit l) const;
  SMALL getLargestCoef() const;
  Lit getLit(Lit l) const;

  void addRhs(const LARGE& r);
  void addLhs(const SMALL& cf, Lit l);
  void weaken(const SMALL& m, Var v);

  LARGE getSlack(const IntVecIt& level) const;
  LARGE getSlack(const IntSet& assumptions) const;

  // @post: preserves order of vars
  void removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos, bool doSaturation = true);
  bool hasNoUnits(const IntVecIt& level) const;
  // @post: mutates order of vars
  void removeZeroes();
  bool hasNoZeroes() const;

  // @post: preserves order of vars
  void saturate(const std::vector<Var>& vs);
  void saturate();
  bool isSaturated() const;
  void saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening, int bitOverflow, int bitReduce);

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
    rhs += (LARGE)cmult * (LARGE)c.rhs;
    degree += (LARGE)cmult * (LARGE)c.degree;
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

  void invert();
  void multiply(const SMALL& m);
  void divide(const LARGE& d);
  void divideRoundUp(const LARGE& d);
  void weakenDivideRound(const IntVecIt& level, Lit l, bool slackdiv, bool fullWeakening);
  void weakenNonDivisibleNonFalsifieds(const IntVecIt& level, const LARGE& div, bool fullWeakening, Lit asserting);
  void weakenDivideRoundRational(const std::vector<double>& assignment, const LARGE& d);
  void applyMIR(const LARGE& d, std::function<Lit(Var)> toLit);

  bool divideByGCD();
  // NOTE: only equivalence preserving operations!
  void postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst, Stats& sts);
  // NOTE: also removes encountered zeroes and changes variable order
  AssertionStatus isAssertingBefore(const IntVecIt& level, int lvl);
  // @return: earliest decision level that propagates a variable
  int getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const;
  // @post: preserves order after removeZeroes()
  void weakenNonImplied(const IntVecIt& level, const LARGE& slack, Stats& sts);
  // @post: preserves order after removeZeroes()
  bool weakenNonImplying(const IntVecIt& level, const SMALL& propCoef, const LARGE& slack, Stats& sts);
  // @post: preserves order after removeZeroes()
  void heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, const LARGE& slack, Stats& sts);

  // @post: preserves order
  template <typename T>
  void weakenSmalls(const T& limit) {
    for (Var v : vars)
      if (rs::abs(coefs[v]) < limit) weaken(-coefs[v], v);
    saturate();
  }

  LARGE absCoeffSum() const;

  // @post: preserves order of vars
  bool simplifyToCardinality(bool equivalencePreserving);
  bool isCardinality() const;

  void sortInDecreasingCoefOrder();
  bool isSortedInDecreasingCoefOrder() const;

  ID logAsInput();
  ID logProofLine();
  ID logProofLineWithInfo([[maybe_unused]] std::string&& info, [[maybe_unused]] const Stats& sts);
  // @pre: reducible to unit over v
  void logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit, const Stats& sts);
  void logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts);

  void toStreamAsOPB(std::ofstream& o) const;
  void toStreamWithAssignment(std::ostream& o, const IntVecIt& level, const std::vector<int>& pos) const;
};

template <typename S, typename L>
std::ostream& operator<<(std::ostream& o, const ConstrExp<S, L>& C) {
  std::vector<Var> vars = C.vars;
  std::sort(vars.begin(), vars.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vars) {
    Lit l = C.coefs[v] < 0 ? -v : v;
    o << C.getCoef(l) << "x" << l << " ";
  }
  o << ">= " << C.degree;
  return o;
}

using ConstrExp32 = ConstrExp<int, long long>;
using ConstrExp64 = ConstrExp<long long, int128>;
using ConstrExp96 = ConstrExp<int128, int128>;
using ConstrExpArb = ConstrExp<bigint, bigint>;

template <typename CE>
class Storage {  // TODO: private constructor for ConstrExp, only accessible to Storage?
  size_t n = 0;
  std::vector<std::unique_ptr<CE>> ces;
  std::vector<CE*> availables;
  std::shared_ptr<Logger> plogger;

 public:
  void resize(size_t newn) {
    assert(n <= INF);
    n = newn;
    for (auto& ce : ces) ce->resize(n);
  }

  void initializeLogging(std::shared_ptr<Logger>& lgr) {
    plogger = lgr;
    for (auto& ce : ces) ce->initializeLogging(lgr);
  }

  CE& take() {
    assert(ces.size() < 20);  // Sanity check that no large amounts of ConstrExps are created
    if (availables.size() == 0) {
      ces.emplace_back(std::make_unique<CE>());
      ces.back()->resize(n);
      ces.back()->initializeLogging(plogger);
      availables.push_back(ces.back().get());
    }
    CE* result = availables.back();
    availables.pop_back();
    assert(result->isReset());
    assert(result->coefs.size() == n);
    return *result;
  }

  void leave(CE& ce) {
    assert(std::any_of(ces.begin(), ces.end(), [&](std::unique_ptr<CE>& i) { return i.get() == &ce; }));
    assert(std::none_of(availables.begin(), availables.end(), [&](CE* i) { return i == &ce; }));
    ce.reset();
    availables.push_back(&ce);
  }
};

class ConstrExpStore {
  Storage<ConstrExp32> ce32s;
  Storage<ConstrExp64> ce64s;
  Storage<ConstrExp96> ce96s;
  Storage<ConstrExpArb> ceArbs;

 public:
  void resize(size_t newn) {
    ce32s.resize(newn);
    ce64s.resize(newn);
    ce96s.resize(newn);
    ceArbs.resize(newn);
  }

  void initializeLogging(std::shared_ptr<Logger> lgr) {
    ce32s.initializeLogging(lgr);
    ce64s.initializeLogging(lgr);
    ce96s.initializeLogging(lgr);
    ceArbs.initializeLogging(lgr);
  }

  ConstrExp32& take32() { return ce32s.take(); }
  void leave(ConstrExp32& ce) { return ce32s.leave(ce); }
  ConstrExp64& take64() { return ce64s.take(); }
  void leave(ConstrExp64& ce) { return ce64s.leave(ce); }
  ConstrExp96& take96() { return ce96s.take(); }
  void leave(ConstrExp96& ce) { return ce96s.leave(ce); }
  ConstrExpArb& takeArb() { return ceArbs.take(); }
  void leave(ConstrExpArb& ce) { return ceArbs.leave(ce); }
};
