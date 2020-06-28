/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt
Copyright (c) 2020, Stephan Gocht

Parts of the code were copied or adapted from MiniSat.

MiniSAT -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
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

#include <boost/multiprecision/cpp_int.hpp>  //  Integer types.
#include <cassert>
#include <iostream>
#include <limits>
#include <numeric>
#include <unordered_map>
#include <vector>

using int128 = __int128;  // NOTE: int128_t from Boost should work too, using a slightly less efficient extra sign bit.
using bigint = boost::multiprecision::cpp_int;
using BigCoef = bigint;
using BigVal = bigint;

namespace rs {  // RoundingSat namespace
template <typename T>
inline T abs(const T& x) {
  return std::abs(x);
}
template <>
inline bigint abs(const bigint& x) {
  return boost::multiprecision::abs(x);
}

template <typename T>
inline T gcd(const T& x, const T& y) {
  return std::gcd(x, y);
}
template <>
inline bigint gcd(const bigint& x, const bigint& y) {
  return boost::multiprecision::gcd(x, y);
}

template <typename T>
inline T lcm(const T& x, const T& y) {
  return std::lcm(x, y);
}
template <>
inline bigint lcm(const bigint& x, const bigint& y) {
  return boost::multiprecision::lcm(x, y);
}

template <typename T>
inline unsigned msb(const T& x) {
  assert(x > 0);
  // return std::bit_floor(x); // C++20
  return boost::multiprecision::msb(boost::multiprecision::uint128_t(x));
}
template <>
inline unsigned msb(const bigint& x) {
  assert(x > 0);
  return boost::multiprecision::msb(x);
}

template <typename T>
inline T pow(const T& x, unsigned y) {
  return std::pow(x, y);
}
template <>
inline bigint pow(const bigint& x, unsigned y) {
  return boost::multiprecision::pow(x, y);
}
}  // namespace rs

using ID = uint64_t;
const ID ID_Undef = std::numeric_limits<ID>::max();
const ID ID_Unsat = ID_Undef - 1;
const ID ID_Trivial = 1;  // represents constraint 0 >= 0

using Var = int;
using Lit = int;
inline Var toVar(Lit l) { return rs::abs(l); }

const int INF = 1e9 + 1;  // 1e9 is the maximum number of variables in the system, anything beyond is infinity

using IntVecIt = std::vector<int>::iterator;

using ActValV = long double;
const ActValV actLimitV = (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 *
                          (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300;  // ~1e2400 << 2^(2^13)
using ActValC = float;
const ActValC actLimitC = 1e30;  // ~1e30 << 2^(2^7)

/*
 * UNKNOWN: uninitialized value
 * FORMULA: original input formula constraints
 * LEARNED: learned from regular conflict analysis
 * BOUND: upper and lower bounds on the objective function
 * COREGUIDED: extension constraints from coreguided optimization
 * FARKAS: LP solver infeasibility witness
 * LEARNEDFARKAS: constraint learned from conflict analysis on FARKAS
 * GOMORY: Gomory cut
 *
 * max number of types is 16, as the type is stored with 4 bits in Constr
 */
enum Origin { UNKNOWN, FORMULA, LEARNED, BOUND, COREGUIDED, FARKAS, LEARNEDFARKAS, GOMORY, UPPERBOUND, LOWERBOUND };

// TODO: make below methods part of a Solver object that's passed around
inline bool isTrue(const IntVecIt& level, Lit l) { return level[l] != INF; }
inline bool isFalse(const IntVecIt& level, Lit l) { return level[-l] != INF; }
inline bool isUnit(const IntVecIt& level, Lit l) { return level[l] == 0; }
inline bool isUnknown(const std::vector<int>& pos, Lit l) { return pos[toVar(l)] == INF; }
