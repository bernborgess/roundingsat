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

#include <ostream>
#include "ConstrExp.hpp"
#include "typedefs.hpp"

struct CRef {
  uint32_t ofs;
  bool operator==(CRef const& o) const { return ofs == o.ofs; }
  bool operator!=(CRef const& o) const { return ofs != o.ofs; }
  bool operator<(CRef const& o) const { return ofs < o.ofs; }
  std::ostream& operator<<(std::ostream& os) { return os << ofs; }
};
const CRef CRef_Undef = {std::numeric_limits<uint32_t>::max()};
const CRef CRef_Unsat = {std::numeric_limits<uint32_t>::max() - 1};  // TODO: needed?

struct Watch {
  CRef cref;
  int idx;  // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
  Watch(CRef cr, int i) : cref(cr), idx(i){};
  bool operator==(const Watch& other) const { return other.cref == cref && other.idx == idx; }
};

class Solver;
struct Constr {  // internal solver constraint optimized for fast propagation
  static int sz_constr(int length) { return (sizeof(Constr) + sizeof(int) * length) / sizeof(uint32_t); }
  ID id;
  Val degree;
  // NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
  struct {
    unsigned locked : 1;
    unsigned origin : 4;
    unsigned lbd : 27;
    unsigned markedfordel : 1;
    unsigned counting : 1;
    unsigned size : 30;
  } header;
  long long ntrailpops;
  ActValC act;
  unsigned int watchIdx;
  Val slack;  // sum of non-falsified watches minus w
  int data[];

  inline bool isClause() const { return slack == std::numeric_limits<Val>::min(); }
  inline bool isCard() const { return slack == std::numeric_limits<Val>::min() + 1; }
  inline bool isSimple() const { return slack < std::numeric_limits<Val>::min() + 2; }
  inline int getMemSize() const { return sz_constr(size() + (isSimple() ? 0 : size())); }
  inline unsigned int size() const { return header.size; }
  inline void setLocked(bool lkd) { header.locked = lkd; }
  inline bool isLocked() { return header.locked; }
  inline Origin getOrigin() const { return (Origin)header.origin; }
  inline void setLBD(unsigned int lbd) { header.lbd = lbd; }
  inline unsigned int lbd() const { return header.lbd; }
  inline bool isMarkedForDelete() const { return header.markedfordel; }
  inline void markForDel() { header.markedfordel = 1; }
  inline bool isCounting() const { return header.counting; }
  inline void setCounting(bool c) { header.counting = (unsigned int)c; }
  inline Coef largestCoef() const {
    assert(!isSimple());
    return rs::abs(data[0]);
  }
  inline Coef coef(unsigned int i) const { return isSimple() ? 1 : rs::abs(data[i << 1]); }
  inline Lit lit(unsigned int i) const { return isSimple() ? data[i] : data[(i << 1) + 1]; }
  inline bool isWatched(unsigned int i) const {
    assert(!isSimple());
    return data[i] < 0;
  }
  double strength() const;
  void undoFalsified(int i);
  template <typename S, typename L>
  inline void toConstraint(ConstrExp<S, L>& out) const {
    assert(out.isReset());  // don't use a ConstrExp used by other stuff
    out.addRhs(degree);
    for (size_t i = 0; i < size(); ++i) {
      assert(coef(i) != 0);
      out.addLhs(coef(i), lit(i));
    }
    out.degree = degree;
    out.orig = getOrigin();
    if (out.plogger) out.resetBuffer(id);
  }
  template <typename CF, typename DG>
  ConstrSimple<CF, DG> toSimpleCons() const {
    ConstrSimple<CF, DG> result;
    result.rhs = degree;
    result.proofLine = std::to_string(id) + " ";
    result.orig = getOrigin();
    result.terms.reserve(size());
    for (unsigned int i = 0; i < size(); ++i) result.terms.emplace_back(coef(i), lit(i));
    return result;
  }
  std::ostream& operator<<(std::ostream& o) {
    for (size_t i = 0; i < size(); ++i) {
      o << coef(i) << "x" << lit(i) << " ";
    }
    o << ">= " << degree << "\n";
    return o;
  }
};

// ---------------------------------------------------------------------
// Memory. Maximum supported size of learnt constraint database is 16GB

struct ConstraintAllocator {
  uint32_t* memory;  // TODO: why not uint64_t?
  uint32_t at = 0, cap = 0;
  uint32_t wasted = 0;  // for GC
  void capacity(uint32_t min_cap);
  CRef alloc(ConstrExp32& constraint, bool locked, ID id);
  Constr& operator[](CRef cr) { return (Constr&)*(memory + cr.ofs); }
  const Constr& operator[](CRef cr) const { return (Constr&)*(memory + cr.ofs); }
};

class OutOfMemoryException {};
static inline void* xrealloc(void* ptr, size_t size) {
  void* mem = realloc(ptr, size);
  if (mem == NULL && errno == ENOMEM)
    throw OutOfMemoryException();
  else
    return mem;
}

// ---------------------------------------------------------------------
// Order heap

struct OrderHeap {  // segment tree (fast implementation of priority queue).
  std::vector<ActValV>& activity;
  int cap = 0;
  std::vector<Var> tree = {-1, -1};

  OrderHeap(std::vector<ActValV>& a) : activity(a) {}

  void resize(int newsize);
  void recalculate();
  void percolateUp(Var x);
  bool empty() const;
  bool inHeap(Var x) const;
  void insert(Var x);
  Var removeMax();
};
