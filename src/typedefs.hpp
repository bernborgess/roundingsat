/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

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

using ID = uint64_t;
const ID ID_Undef = UINT64_MAX;
const ID ID_Unsat = UINT64_MAX-1;

using Var = int;
using Lit = int;
using Coef = int;
using Val = long long;

const Coef INF = 1e9+1;

using IntVecIt = std::vector<int>::iterator;

// TODO: below is part of Solver.hpp
enum SolveState { SAT, UNSAT, INCONSISTENT, INTERRUPTED, INPROCESSING }; // TODO: add RESTARTING?
/*
 * FORMULA constraints are original input formula constraints that are only deleted when satisfied at root.
 * AUXILIARY constraints are non-formula constraints that are only deleted when satisfied at root.
 * EXTERNAL constraints are non-formula constraints that are never deleted.
 * LEARNT constraints are implied by any combination of the above, and may be deleted heuristically.
 */
enum ConstraintType { FORMULA, AUXILIARY, EXTERNAL, LEARNT };