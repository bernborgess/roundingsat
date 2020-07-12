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
#include "globals.hpp"
#include "typedefs.hpp"

enum WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };

class Solver;
// TODO: check all static_cast downcasts of bigints
struct Constr {  // internal solver constraint optimized for fast propagation
  virtual size_t getMemSize() const = 0;

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

  virtual ~Constr() {}

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

  virtual void initializeWatches(CRef cr, Solver& solver) = 0;
  virtual WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& slvr) = 0;
  virtual void undoFalsified(int i) = 0;
  virtual void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) = 0;

  virtual CeSuper toExpanded(ConstrExpPools& cePools) const = 0;

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

  static size_t getMemSize(unsigned int length) { return (sizeof(Clause) + sizeof(Lit) * length) / sizeof(uint32_t); }
  size_t getMemSize() const { return getMemSize(size()); }

  BigVal degree() const { return 1; }
  BigCoef coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }

  template <typename SMALL, typename LARGE>
  void initialize(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id) {
    assert(_id > ID_Trivial);
    assert(constraint->vars.size() < INF);
    assert(constraint->getDegree() == 1);
    unsigned int length = constraint->vars.size();

    id = _id;
    act = 0;
    header = {0, (unsigned int)constraint->orig, 0x07FFFFFF, 0, locked, length};

    for (unsigned int i = 0; i < length; ++i) {
      Var v = constraint->vars[i];
      assert(constraint->getLit(v) != 0);
      data[i] = constraint->getLit(v);
    }
  }
  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
  void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver);

  CeSuper toExpanded(ConstrExpPools& cePools) const;
};

struct Cardinality final : public Constr {
  unsigned int watchIdx;
  unsigned int degr;
  long long ntrailpops;
  Lit data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Cardinality) + sizeof(Lit) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size()); }

  BigVal degree() const { return degr; }
  BigCoef coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }

  template <typename SMALL, typename LARGE>
  void initialize(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id) {
    assert(_id > ID_Trivial);
    assert(constraint->vars.size() < INF);
    assert(rs::abs(constraint->coefs[constraint->vars[0]]) == 1);
    unsigned int length = constraint->vars.size();
    assert(constraint->getDegree() <= length);

    id = _id;
    act = 0;
    degr = static_cast<unsigned int>(constraint->getDegree());
    header = {0, (unsigned int)constraint->orig, 0x07FFFFFF, 0, locked, length};
    ntrailpops = -1;
    watchIdx = 0;

    for (unsigned int i = 0; i < length; ++i) {
      Var v = constraint->vars[i];
      assert(constraint->getLit(v) != 0);
      data[i] = constraint->getLit(v);
    }
  }
  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
  void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver);

  CeSuper toExpanded(ConstrExpPools& cePools) const;
};

template <typename CF, typename DG>
struct Counting final : public Constr {
  unsigned int watchIdx;
  DG degr;
  long long ntrailpops;
  DG slack;  // sum of non-falsifieds minus w
  Term<CF> data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Counting<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size()); }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return data[i].c; }
  Lit lit(unsigned int i) const { return data[i].l; }

  template <typename SMALL, typename LARGE>
  void initialize(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id) {
    assert(_id > ID_Trivial);
    // TODO: check whether constraint fits in <CF,DG>
    ++stats.NCOUNTING;
    unsigned int length = constraint->vars.size();

    id = _id;
    act = 0;
    degr = static_cast<DG>(constraint->getDegree());
    header = {0, (unsigned int)constraint->orig, 0x07FFFFFF, 0, locked, length};
    ntrailpops = -1;
    watchIdx = 0;

    for (unsigned int i = 0; i < length; ++i) {
      Var v = constraint->vars[i];
      assert(constraint->getLit(v) != 0);
      data[i] = {static_cast<CF>(rs::abs(constraint->coefs[v])), constraint->getLit(v)};
    }
  }
  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);
  void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver);

  CePtr<ConstrExp<CF, DG>> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;

  bool hasCorrectSlack(const Solver& solver);
};

template <typename CF, typename DG>
struct Watched final : public Constr {
  unsigned int watchIdx;
  DG degr;
  long long ntrailpops;
  DG watchslack;  // sum of non-falsified watches minus w
  Term<CF> data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Watched<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size()); }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return rs::abs(data[i].c); }
  Lit lit(unsigned int i) const { return data[i].l; }

  template <typename SMALL, typename LARGE>
  void initialize(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id) {
    assert(_id > ID_Trivial);
    // TODO: check whether constraint fits in <CF,DG>
    ++stats.NWATCHED;
    unsigned int length = constraint->vars.size();

    id = _id;
    act = 0;
    degr = static_cast<DG>(constraint->getDegree());
    header = {0, (unsigned int)constraint->orig, 0x07FFFFFF, 0, locked, length};
    ntrailpops = -1;
    watchIdx = 0;

    for (unsigned int i = 0; i < length; ++i) {
      Var v = constraint->vars[i];
      assert(constraint->getLit(v) != 0);
      data[i] = {static_cast<CF>(rs::abs(constraint->coefs[v])), constraint->getLit(v)};
    }
  }
  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);
  void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver);

  CePtr<ConstrExp<CF, DG>> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;

  bool hasCorrectSlack(const Solver& solver);
  bool hasCorrectWatches(const Solver& solver);
};

struct Arbitrary final : public Constr {
  unsigned int watchIdx;
  long long ntrailpops;
  BigVal degr;
  BigVal slack;                // sum of non-falsifieds minus w
  std::vector<BigCoef> coefs;  // NOTE: seemed not possible to put bigints in below dynamic array
  Lit lits[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Arbitrary) + sizeof(Lit) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size()); }

  BigVal degree() const { return degr; }
  BigCoef coef(unsigned int i) const { return coefs[i]; }
  Lit lit(unsigned int i) const { return lits[i]; }

  template <typename SMALL, typename LARGE>
  void initialize(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id) {
    assert(_id > ID_Trivial);
    ++stats.NCOUNTING;
    unsigned int length = constraint->vars.size();

    id = _id;
    act = 0;
    degr = constraint->getDegree();
    header = {0, (unsigned int)constraint->orig, 0x07FFFFFF, 0, locked, length};
    ntrailpops = -1;
    watchIdx = 0;

    coefs.resize(length);
    for (unsigned int i = 0; i < length; ++i) {
      Var v = constraint->vars[i];
      assert(constraint->getLit(v) != 0);
      coefs[i] = rs::abs(constraint->coefs[v]);
      lits[i] = constraint->getLit(v);
    }
  }
  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver);
  void undoFalsified(int i);
  void resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver);

  CeArb expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;

  bool hasCorrectSlack(const Solver& solver);
};
