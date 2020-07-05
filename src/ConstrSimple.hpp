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

#include <iostream>
#include <sstream>
#include <vector>
#include "typedefs.hpp"

template <typename CF>
struct Term {
  Term() : c(0), l(0) {}
  Term(const CF& x, Lit y) : c(x), l(y) {}
  CF c;
  Lit l;
};

template <typename CF>
std::ostream& operator<<(std::ostream& o, const Term<CF>& t) {
  return o << t.c << "x" << t.l;
}

struct ConstrExpSuper;
struct ConstrExpPools;
template <typename CF, typename DG>
struct ConstrSimple;
using ConstrSimple32 = ConstrSimple<int, long long>;
using ConstrSimple64 = ConstrSimple<long long, int128>;
using ConstrSimple96 = ConstrSimple<int128, int128>;
using ConstrSimpleArb = ConstrSimple<bigint, bigint>;

struct ConstrSimpleSuper {
  Origin orig = Origin::UNKNOWN;
  virtual ConstrExpSuper& toExpanded(ConstrExpPools& cePools) const = 0;
  virtual void copyTo(ConstrSimple32& out) const = 0;
  virtual void copyTo(ConstrSimple64& out) const = 0;
  virtual void copyTo(ConstrSimple96& out) const = 0;
  virtual void copyTo(ConstrSimpleArb& out) const = 0;
};

template <typename CF, typename DG>
struct ConstrSimple final : public ConstrSimpleSuper {
  std::vector<Term<CF>> terms;
  DG rhs;
  std::string proofLine;

  ConstrSimple(const std::vector<Term<CF>>& t = {}, const DG& r = 0, const Origin& o = Origin::UNKNOWN,
               const std::string& p = (std::to_string(ID_Trivial) + " "))
      : terms(t), rhs(r), proofLine(p) {
    orig = o;
  }

  ConstrExpSuper& toExpanded(ConstrExpPools& cePools) const;

  void toNormalFormLit();
  void toNormalFormVar();

 private:
  template <typename C, typename D>
  void copy_(ConstrSimple<C, D>& out) const {
    out.orig = orig;
    out.rhs = static_cast<D>(rhs);
    out.terms.resize(terms.size());
    for (unsigned int i = 0; i < terms.size(); ++i) {
      out.terms[i].l = terms[i].l;
      out.terms[i].c = static_cast<C>(terms[i].c);
    }
    out.proofLine = proofLine;
  }

 public:
  void copyTo(ConstrSimple32& out) const { copy_(out); }
  void copyTo(ConstrSimple64& out) const { copy_(out); }
  void copyTo(ConstrSimple96& out) const { copy_(out); }
  void copyTo(ConstrSimpleArb& out) const { copy_(out); }
};

template <typename CF, typename DG>
inline std::ostream& operator<<(std::ostream& o, const ConstrSimple<CF, DG>& sc) {
  for (const Term<CF>& t : sc.terms) o << "+ " << t << " ";
  return o << ">= " << sc.rhs;
}
