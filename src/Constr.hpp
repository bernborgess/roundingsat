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

#include "ConstrExp.hpp"
#include "ConstrSimple.hpp"
#include "typedefs.hpp"

enum ConstrType { CLAUSE, CARDINALITY, WATCHED, COUNTING, ARBITRARY };
enum WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };

struct CRef {
  uint32_t ofs;
  bool operator==(CRef const& o) const { return ofs == o.ofs; }
  bool operator!=(CRef const& o) const { return ofs != o.ofs; }
  bool operator<(CRef const& o) const { return ofs < o.ofs; }
  std::ostream& operator<<(std::ostream& os) { return os << ofs; }
};
const CRef CRef_Undef = {std::numeric_limits<uint32_t>::max()};
const CRef CRef_Unsat = {std::numeric_limits<uint32_t>::max() - 1};  // TODO: needed?
const bigint limit32 = bigint(1e9);
const bigint limit64 = bigint(1e18);
const bigint limit96 = bigint(1e27);

class Solver;
// TODO: check all static_cast downcasts of bigints
struct Constr {  // internal solver constraint optimized for fast propagation
  virtual int getMemSize(unsigned int length) const = 0;
  int getMemSize() const { return getMemSize(size()); }

  ID id;
  // NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
  struct {
    unsigned unused : 1;
    unsigned origin : 4;
    unsigned lbd : 27;
    unsigned markedfordel : 1;
    unsigned locked : 1;
    unsigned size : 30;
  } header;
  ActValC act;

  unsigned int size() const { return header.size; }
  void setLocked(bool lkd) { header.locked = lkd; }
  bool isLocked() { return header.locked; }
  Origin getOrigin() const { return (Origin)header.origin; }
  void setLBD(unsigned int lbd) { header.lbd = lbd; }
  unsigned int lbd() const { return header.lbd; }
  bool isMarkedForDelete() const { return header.markedfordel; }
  void markForDel() { header.markedfordel = 1; }

  virtual BigVal degree() const = 0;
  virtual BigCoef coef(unsigned int i) const = 0;
  BigCoef largestCoef() const { return coef(0); };
  virtual Lit lit(unsigned int i) const = 0;

  virtual void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id) = 0;
  virtual WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& slvr) = 0;
  virtual void undoFalsified(int i) = 0;

  template <typename S, typename L>
  inline void toConstraint(ConstrExp<S, L>& out) const {
    assert(out.isReset());  // don't use a ConstrExp used by other stuff
    out.addRhs(static_cast<L>(degree()));
    for (size_t i = 0; i < size(); ++i) {
      assert(coef(i) != 0);
      out.addLhs(static_cast<S>(coef(i)), lit(i));
    }
    out.degree = static_cast<L>(degree());
    out.orig = getOrigin();
    if (out.plogger) out.resetBuffer(id);
  }
  template <typename CF, typename DG>
  ConstrSimple<CF, DG> toSimpleCons() const {
    ConstrSimple<CF, DG> result;
    result.rhs = static_cast<DG>(degree());
    result.proofLine = std::to_string(id) + " ";
    result.orig = getOrigin();
    result.terms.reserve(size());
    for (unsigned int i = 0; i < size(); ++i) result.terms.emplace_back(static_cast<CF>(coef(i)), lit(i));
    return result;
  }
  std::ostream& operator<<(std::ostream& o) {
    for (size_t i = 0; i < size(); ++i) {
      o << coef(i) << "x" << lit(i) << " ";
    }
    o << ">= " << degree() << "\n";
    return o;
  }
  void print(const Solver& solver);

  bool isCorrectlyConflicting(const Solver& solver);
  bool isCorrectlyPropagating(const Solver& solver, int idx);
};

struct Clause final : public Constr {
  Lit data[];

  int getMemSize(unsigned int length) const { return (sizeof(Clause) + sizeof(Lit) * length) / sizeof(uint32_t); }

  BigVal degree() const { return 1; }
  BigCoef coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }

  void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
};

struct Cardinality final : public Constr {
  unsigned int watchIdx;
  unsigned int degr;
  long long ntrailpops;
  Lit data[];

  int getMemSize(unsigned int length) const { return (sizeof(Cardinality) + sizeof(Lit) * length) / sizeof(uint32_t); }

  BigVal degree() const { return degr; }
  BigCoef coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }

  void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
};

template <typename CF, typename DG>
struct Counting final : public Constr {
  unsigned int watchIdx;
  DG degr;
  long long ntrailpops;
  DG slack;  // sum of non-falsifieds minus w
  Term<CF> data[];

  int getMemSize(unsigned int length) const {
    return (sizeof(Counting<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return data[i].c; }
  Lit lit(unsigned int i) const { return data[i].l; }

  void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);

  bool hasCorrectSlack(const Solver& solver);
};

using Counting32 = Counting<int, long long>;
using Counting64 = Counting<long long, int128>;
using Counting96 = Counting<int128, int128>;

template <typename CF, typename DG>
struct Watched final : public Constr {
  unsigned int watchIdx;
  DG degr;
  long long ntrailpops;
  DG watchslack;  // sum of non-falsified watches minus w
  Term<CF> data[];

  int getMemSize(unsigned int length) const {
    return (sizeof(Watched<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return rs::abs(data[i].c); }
  Lit lit(unsigned int i) const { return data[i].l; }

  void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);

  bool hasCorrectSlack(const Solver& solver);
  bool hasCorrectWatches(const Solver& solver);
};

using Watched32 = Watched<int, long long>;
using Watched64 = Watched<long long, int128>;
using Watched96 = Watched<int128, int128>;

struct Arbitrary final : public Constr {
  unsigned int watchIdx;
  long long ntrailpops;
  bigint degr;
  bigint slack;               // sum of non-falsifieds minus w
  std::vector<bigint> coefs;  // NOTE: seemed not possible to put bigints in below dynamic array
  Lit lits[];

  int getMemSize(unsigned int length) const { return (sizeof(Arbitrary) + sizeof(Lit) * length) / sizeof(uint32_t); }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return coefs[i]; }
  Lit lit(unsigned int i) const { return lits[i]; }

  void initialize(const ConstrExpArb& constraint, bool locked, CRef cr, Solver& solver, ID id);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);

  bool hasCorrectSlack(const Solver& solver);
};
