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

#include <vector>
#include <iostream>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <csignal>
#include <unordered_map>
#include <memory>

#include "aux.hpp"
#include "typedefs.hpp"
#include "IntSet.hpp"
#include "Constraint.hpp"
#include "Options.hpp"
#include "Solver.hpp"
#include "globals.hpp"

Stats stats;
Options options;
std::shared_ptr<Logger> logger;
Var n;
Var orig_n;
bool asynch_interrupt;

Solver solver;

// ---------------------------------------------------------------------
// IO

namespace io {
	void print_stats(const Stats& stats) {
		printf("c CPU time			  : %g s\n", aux::cpuTime() - stats.STARTTIME);
		printf("c deterministic time %lld %.2e\n", stats.getDetTime(), (double) stats.getDetTime());
		printf("c propagations %lld\n", stats.NPROP);
		printf("c decisions %lld\n", stats.NDECIDE);
		printf("c conflicts %lld\n", stats.NCONFL);
		printf("c restarts %lld\n", stats.NRESTARTS);
		printf("c inprocessing phases %lld\n", stats.NCLEANUP);
		printf("c clauses %lld\n", stats.NCLAUSESLEARNED);
		printf("c cardinalities %lld\n", stats.NCARDINALITIESLEARNED);
		printf("c general constraints %lld\n", stats.NGENERALSLEARNED);
		printf("c watched constraints %lld\n", stats.NWATCHED);
		printf("c counting constraints %lld\n", stats.NCOUNTING);
		printf("c average constraint length %.2f\n",
		       stats.NCONFL == 0 ? 0 : (double) stats.LEARNEDLENGTHSUM / stats.NCONFL);
		printf("c average constraint degree %.2f\n",
		       stats.NCONFL == 0 ? 0 : (double) stats.LEARNEDDEGREESUM / stats.NCONFL);
		printf("c gcd simplifications %lld\n", stats.NGCD);
		printf("c detected cardinalities %lld\n", stats.NCARDDETECT);
		printf("c weakened non-implied lits %lld\n", stats.NWEAKENEDNONIMPLIED);
		printf("c weakened non-implying lits %lld\n", stats.NWEAKENEDNONIMPLYING);
		printf("c auxiliary variables introduced %d\n", n - orig_n);
		printf("c solutions found %lld\n", stats.NSOLS);
		printf("c cores constructed %lld\n", stats.NCORES);
		printf("c core cardinality constraints returned %lld\n", stats.NCORECARDINALITIES);
		printf("c clausal propagations %lld\n", stats.NPROPCLAUSE);
		printf("c cardinality propagations %lld\n", stats.NPROPCARD);
		printf("c watched propagations %lld\n", stats.NPROPWATCH);
		printf("c counting propagations %lld\n", stats.NPROPCOUNTING);
		printf("c watch lookups %lld\n", stats.NWATCHLOOKUPS);
		printf("c watch backjump lookups %lld\n", stats.NWATCHLOOKUPSBJ);
		printf("c watch checks %lld\n", stats.NWATCHCHECKS);
		printf("c propagation checks %lld\n", stats.NPROPCHECKS);
		printf("c constraint additions %lld\n", stats.NADDEDLITERALS);
		printf("c trail pops %lld\n", stats.NTRAILPOPS);
	}

	void printSol(const std::vector<bool>& sol) {
		if (!options.printSol) return;
		printf("v");
		for (Var v = 1; v <= orig_n; ++v) printf(sol[v] ? " x%d" : " -x%d", v);
		printf("\n");
	}

	void exit_SAT(const std::vector<bool>& sol) {
		if (logger) logger->flush();
		print_stats(stats);
		puts("s SATISFIABLE");
		printSol(sol);
		exit(10);
	}

	void exit_UNSAT(const std::vector<bool>& sol, Val bestObjVal) {
		if (logger) logger->flush();
		print_stats(stats);
		if (sol.size() > 0) {
			std::cout << "o " << bestObjVal << std::endl;
			std::cout << "s OPTIMUM FOUND" << std::endl;
			printSol(sol);
			exit(30);
		} else {
			puts("s UNSATISFIABLE");
			exit(20);
		}
	}

	void exit_INDETERMINATE(const std::vector<bool>& sol) {
		if (sol.size() > 0) exit_SAT(sol);
		if (logger) logger->flush();
		print_stats(stats);
		puts("s UNKNOWN");
		exit(0);
	}

	void exit_ERROR(const std::initializer_list<std::string>& messages) {
		if (logger) logger->flush();
		print_stats(stats);
		std::cout << "Error: ";
		for (const std::string& m: messages) std::cout << m;
		std::cout << std::endl;
		exit(1);
	}

	void usage(char* name) {
		printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", name);
		printf("\n");
		printf("Options:\n");
		printf("  --help           Prints this help message.\n");
		printf("  --print-sol=arg  Prints the solution if found (default %d).\n", options.printSol);
		printf("  --options.verbosity=arg  Set the options.verbosity of the output (default %d).\n", options.verbosity);
		printf("\n");
		printf("  --var-decay=arg  Set the VSIDS decay factor (0.5<=arg<1; default %lf).\n", options.v_vsids_decay);
		printf("  --options.rinc=arg       Set the base of the Luby restart sequence (float >=1; default %lf).\n", options.rinc);
		printf("  --options.rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %lld).\n", options.rfirst);
		printf(
				"  --original-rto=arg Set whether to use RoundingSat's original round-to-one conflict analysis (0 or 1; default %d).\n",
				options.originalRoundToOne);
		printf(
				"  --opt-mode=arg   Set optimization mode: 0 linear, 1(2) (lazy) core-guided, 3(4) (lazy) hybrid (default %d).\n",
				options.optMode);
		printf(
				"  --prop-counting=arg Counting propagation instead of watched propagation (float between 0 (no counting) and 1 (always counting)); default %lf).\n",
				options.countingProp);
		printf("  --prop-clause=arg Optimized two-watched propagation for clauses (0 or 1; default %d).\n", options.clauseProp);
		printf("  --prop-card=arg  Optimized watched propagation for cardinalities (0 or 1; default %d).\n", options.cardProp);
		printf("  --prop-idx=arg   Optimize index of watches during propagation (0 or 1; default %d).\n", options.idxProp);
		printf("  --prop-sup=arg   Avoid superfluous watch checks (0 or 1; default %d).\n", options.supProp);
		printf("  --proof-log=arg  Set a filename for the proof logs (string).\n");
	}

	typedef bool (* func)(double);

	template<class T>
	void getOptionNum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, func test,
	                  T& val) {
		if (opt_val.count(option)) {
			double v = atof(opt_val.at(option).c_str());
			if (test(v)) val = v;
			else io::exit_ERROR({"Invalid value for ", option, ": ", opt_val.at(option), ".\nCheck usage with --help option."});
		}
	}

	void getOptionStr(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option,
	                  std::string& val) {
		if (opt_val.count(option)) val = opt_val.at(option);
	}

	Options read_options(int argc, char** argv) {
		Options options;
		for (int i = 1; i < argc; i++) {
			if (!strcmp(argv[i], "--help")) {
				usage(argv[0]);
				exit(1);
			}
		}
		std::vector<std::string> opts = {"print-sol", "verbosity", "var-decay", "rinc", "rfirst", "original-rto",
		                                 "opt-mode", "prop-counting", "prop-clause", "prop-card", "prop-idx", "prop-sup",
		                                 "proof-log"};
		std::unordered_map<std::string, std::string> opt_val;
		for (int i = 1; i < argc; i++) {
			if (std::string(argv[i]).substr(0, 2) != "--") options.formulaName = argv[i];
			else {
				bool found = false;
				for (std::string& key : opts) {
					if (std::string(argv[i]).substr(0, key.size() + 3) == "--" + key + "=") {
						found = true;
						opt_val[key] = std::string(argv[i]).substr(key.size() + 3);
					}
				}
				if (!found) io::exit_ERROR({"Unknown option: ", argv[i], ".\nCheck usage with --help option."});
			}
		}
		getOptionNum(opt_val, "print-sol", [](double x) -> bool { return x == 0 || x == 1; }, options.printSol);
		getOptionNum(opt_val, "verbosity", [](double) -> bool { return true; }, options.verbosity);
		getOptionNum(opt_val, "var-decay", [](double x) -> bool { return x >= 0.5 && x < 1; }, options.v_vsids_decay);
		getOptionNum(opt_val, "rinc", [](double x) -> bool { return x >= 1; }, options.rinc);
		getOptionNum(opt_val, "rfirst", [](double x) -> bool { return x >= 1; }, options.rfirst);
		getOptionNum(opt_val, "original-rto", [](double x) -> bool { return x == 0 || x == 1; }, options.originalRoundToOne);
		getOptionNum(opt_val, "opt-mode", [](double x) -> bool { return x == std::round(x) && 0 <= x && x <= 4; }, options.optMode);
		getOptionNum(opt_val, "prop-counting", [](double x) -> bool { return x >= 0 || x <= 1; }, options.countingProp);
		getOptionNum(opt_val, "prop-clause", [](double x) -> bool { return x == 0 || x == 1; }, options.clauseProp);
		getOptionNum(opt_val, "prop-card", [](double x) -> bool { return x == 0 || x == 1; }, options.cardProp);
		getOptionNum(opt_val, "prop-idx", [](double x) -> bool { return x == 0 || x == 1; }, options.idxProp);
		getOptionNum(opt_val, "prop-sup", [](double x) -> bool { return x == 0 || x == 1; }, options.supProp);
		getOptionStr(opt_val, "proof-log", options.proofLogName);
		return options;
	}
}

// ---------------------------------------------------------------------
// Parsers

namespace parser {
	int
	read_number(const std::string& s) { // TODO: should also read larger numbers than int (e.g., capture large degree)
		long long answer = 0;
		for (char c : s)
			if ('0' <= c && c <= '9') {
				answer *= 10, answer += c - '0';
				if (answer >= INF) io::exit_ERROR({"Input formula contains absolute value larger than 10^9: ", s});
			}
		for (char c : s) if (c == '-') answer = -answer;
		return answer;
	}

	void opb_read(std::istream& in, intConstr& objective) {
		assert(objective.isReset());
		intConstr input; // TODO: make input use multiple precision to avoid overflow errors
		input.resize(n + 1);
		bool first_constraint = true;
		_unused(first_constraint);
		for (std::string line; getline(in, line);) {
			if (line.empty()) continue;
			else if (line[0] == '*') continue;
			else {
				for (char& c : line) if (c == ';') c = ' ';
				bool opt_line = line.substr(0, 4) == "min:";
				std::string line0;
				if (opt_line) line = line.substr(4), assert(first_constraint);
				else {
					std::string symbol;
					if (line.find(">=") != std::string::npos) symbol = ">=";
					else symbol = "=";
					assert(line.find(symbol) != std::string::npos);
					line0 = line;
					line = line.substr(0, line.find(symbol));
				}
				first_constraint = false;
				std::istringstream is(line);
				input.reset();
				std::vector<std::string> tokens;
				std::string tmp;
				while (is >> tmp) tokens.push_back(tmp);
				if (tokens.size() % 2 != 0) io::exit_ERROR({"No support for non-linear constraints."});
				for (int i = 0; i < (long long) tokens.size(); i += 2)
					if (find(tokens[i].begin(), tokens[i].end(), 'x') != tokens[i].end())
						io::exit_ERROR({"No support for non-linear constraints."});
				for (int i = 0; i < (long long) tokens.size(); i += 2) {
					std::string scoef = tokens[i];
					std::string var = tokens[i + 1];
					Coef coef = read_number(scoef);
					bool negated = false;
					std::string origvar = var;
					if (!var.empty() && var[0] == '~') {
						negated = true;
						var = var.substr(1);
					}
					if (var.empty() || var[0] != 'x') io::exit_ERROR({"Invalid literal token: ", origvar});
					var = var.substr(1);
					Lit l = atoi(var.c_str());
					if (!(1 <= l && l <= n)) io::exit_ERROR({"Literal token out of variable range: ", origvar});
					if (negated) l = -l;
					input.addLhs(coef, l);
				}
				if (opt_line) input.copyTo(objective);
				else {
					input.addRhs(read_number(line0.substr(line0.find("=") + 1)));
					if (input.getDegree() >= (Val) INF)
						io::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
					if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) io::exit_UNSAT({}, 0);
					if (line0.find(" = ") != std::string::npos) { // Handle equality case with second constraint
						input.invert();
						if (input.getDegree() >= (Val) INF)
							io::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
						if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) io::exit_UNSAT({}, 0);
					}
				}
			}
		}
		orig_n = n;
	}

	void wcnf_read(std::istream& in, long long top, intConstr& objective) {
		assert(objective.isReset());
		intConstr input;
		input.resize(n + 1);
		for (std::string line; getline(in, line);) {
			if (line.empty() || line[0] == 'c') continue;
			else {
				std::istringstream is(line);
				long long weight;
				is >> weight;
				if (weight == 0) continue;
				input.reset();
				input.addRhs(1);
				Lit l;
				while (is >> l, l) input.addLhs(1, l);
				if (weight < top) { // soft clause
					if (weight >= INF) io::exit_ERROR({"Clause weight exceeds 10^9: ", std::to_string(weight)});
					if (weight < 0) io::exit_ERROR({"Negative clause weight: ", std::to_string(weight)});
					solver.setNbVariables(n + 1); // increases n to n+1
					input.resize(n + 1);
					objective.resize(n + 1);
					objective.addLhs(weight, n);
					input.addLhs(1, n);
				} // else hard clause
				if (input.getDegree() >= (Val) INF)
					io::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
				if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) io::exit_UNSAT({}, 0);
			}
		}
		orig_n = n - objective.vars.size();
	}

	void cnf_read(std::istream& in) {
		intConstr input;
		input.resize(n + 1);
		for (std::string line; getline(in, line);) {
			if (line.empty() || line[0] == 'c') continue;
			else {
				std::istringstream is(line);
				input.reset();
				input.addRhs(1);
				Lit l;
				while (is >> l, l) input.addLhs(1, l);
				if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) io::exit_UNSAT({}, 0);
			}
		}
		orig_n = n;
	}

	void file_read(std::istream& in, intConstr& objective) {
		for (std::string line; getline(in, line);) {
			if (line.empty() || line[0] == 'c') continue;
			if (line[0] == 'p') {
				std::istringstream is(line);
				is >> line; // skip 'p'
				std::string type;
				is >> type;
				long long n;
				is >> n;
				solver.setNbVariables(n);
				if (type == "cnf") {
					cnf_read(in);
					return;
				} else if (type == "wcnf") {
					is >> line; // skip nbConstraints
					long long top;
					is >> top;
					wcnf_read(in, top, objective);
					return;
				}
			} else if (line[0] == '*' && line.substr(0, 13) == "* #variable= ") {
				std::istringstream is(line.substr(13));
				long long n;
				is >> n;
				solver.setNbVariables(n);
				opb_read(in, objective);
				return;
			}
		}
		io::exit_ERROR({"No supported format [opb, cnf, wcnf] detected."});
	}
}

// ---------------------------------------------------------------------
// Meta-search

namespace meta {
	std::vector<bool> solution;
	intConstr aux;
	intConstr core;
	Val upper_bound;
	Val lower_bound;

	inline void printObjBounds(Val lower, Val upper) {
		if (upper < std::numeric_limits<Val>::max()) printf("c bounds %10lld >= %10lld\n", upper, lower);
		else printf("c bounds          - >= %10lld\n", lower);
	}

	void handleNewSolution(const intConstr& origObj, ID& lastUpperBound) {
		Val prev_val = upper_bound;
		_unused(prev_val);
		upper_bound = -origObj.getRhs();
		for (Var v: origObj.vars) upper_bound += origObj.coefs[v] * solution[v];
		assert(upper_bound < prev_val);

		origObj.copyTo(aux);
		aux.invert();
		aux.addRhs(-upper_bound + 1);
		solver.dropExternal(lastUpperBound, true);
		lastUpperBound = solver.addConstraint(aux, ConstraintType::EXTERNAL);
		aux.reset();
		if (lastUpperBound == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
	}

	struct LazyVar {
		int mult; // TODO: add long long to int check?
		Val rhs;
		std::vector<Lit> lhs; //TODO: refactor lhs and introducedVars to one Lit vector
		std::vector<Var> introducedVars;
		ID atLeastID = ID_Undef;
		ID atMostID = ID_Undef;

		LazyVar(intConstr& core, Var startvar, int m) :
				mult(m), rhs(core.getDegree()), introducedVars{startvar} {
			assert(core.isCardinality());
			lhs.reserve(core.vars.size());
			for (Var v: core.vars) lhs.push_back(core.getLit(v));
		}

		~LazyVar() {
			solver.dropExternal(atLeastID, false);
			solver.dropExternal(atMostID, false);
		}

		Var getCurrentVar() const { return introducedVars.back(); }

		void addVar(Var v) { introducedVars.push_back(v); }

		void addAtLeastConstraint() {
			// X >= k + y1 + ... + yi
			std::vector<Coef> coefs;
			coefs.reserve(lhs.size() + introducedVars.size());
			std::vector<Lit> lits;
			lits.reserve(lhs.size() + introducedVars.size());
			for (Lit l: lhs) {
				coefs.push_back(1);
				lits.push_back(l);
			}
			for (Var v: introducedVars) {
				coefs.push_back(-1);
				lits.push_back(v);
			}
			solver.dropExternal(atLeastID,
			             false); // TODO: dropExternal(atLeastID,true)? Or treat them as learned/implied constraints?
			atLeastID = solver.addConstraint(coefs, lits, rhs, ConstraintType::EXTERNAL);
			if (atLeastID == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
		}

		void addAtMostConstraint() {
			// X =< k + y1 + ... + yi-1 + (1+n-k-i)yi
			std::vector<Coef> coefs;
			coefs.reserve(lhs.size() + introducedVars.size());
			std::vector<Lit> lits;
			lits.reserve(lhs.size() + introducedVars.size());
			for (Lit l: lhs) {
				coefs.push_back(-1);
				lits.push_back(l);
			}
			for (Var v: introducedVars) {
				coefs.push_back(1);
				lits.push_back(v);
			}
			assert(getCurrentVar() == introducedVars.back());
			coefs.push_back(lhs.size() - rhs - introducedVars.size());
			lits.push_back(getCurrentVar());
			solver.dropExternal(atMostID, false); // TODO: dropExternal(atMostID,true)? Or treat them as learned/implied constraints?
			atMostID = solver.addConstraint(coefs, lits, -rhs, ConstraintType::EXTERNAL);
			if (atMostID == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
		}

		void addSymBreakingConstraint(Var prevvar) const {
			assert(introducedVars.size() > 1);
			// y-- + ~y >= 1 (equivalent to y-- >= y)
			if (solver.addConstraint({1, 1}, {prevvar, -getCurrentVar()}, 1, ConstraintType::AUXILIARY) == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
		}
	};

	std::ostream& operator<<(std::ostream& o, const LazyVar* lv) {
		for (Var v: lv->introducedVars) o << v << " ";
		o << "| ";
		for (Lit l: lv->lhs) o << "+x" << l << " ";
		o << ">= " << lv->rhs;
		return o;
	}

	void checkLazyVariables(longConstr& reformObj, std::vector<LazyVar*>& lazyVars) {
		for (int i = 0; i < (int) lazyVars.size(); ++i) {
			LazyVar* lv = lazyVars[i];
			if (reformObj.getLit(lv->getCurrentVar()) == 0) {
				// add auxiliary variable
				long long newN = n + 1;
				solver.setNbVariables(newN);
				reformObj.resize(newN + 1);
				Var oldvar = lv->getCurrentVar();
				lv->addVar(newN);
				// reformulate the objective
				reformObj.addLhs(lv->mult, newN);
				// add necessary lazy constraints
				lv->addAtLeastConstraint();
				lv->addAtMostConstraint();
				lv->addSymBreakingConstraint(oldvar);
				if (lv->introducedVars.size() + lv->rhs == lv->lhs.size()) {
					aux::swapErase(lazyVars, i--);
					delete lv;
					continue;
				}
			}
		}
	}

	void addLowerBound(const intConstr& origObj, Val lower_bound, ID& lastLowerBound) {
		origObj.copyTo(aux);
		aux.addRhs(lower_bound);
		solver.dropExternal(lastLowerBound, true);
		lastLowerBound = solver.addConstraint(aux, ConstraintType::EXTERNAL);
		aux.reset();
		if (lastLowerBound == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
	}

	void handleInconsistency(longConstr& reformObj, const intConstr& origObj, std::vector<LazyVar*>& lazyVars,
			ID& lastLowerBound) {
		// take care of derived unit lits and remove zeroes
		reformObj.removeUnitsAndZeroes(solver.Level, solver.Pos, false);
		Val prev_lower = lower_bound;
		_unused(prev_lower);
		lower_bound = -reformObj.getDegree();
		if (core.getDegree() == 0) { // apparently only unit assumptions were derived
			assert(lower_bound > prev_lower);
			checkLazyVariables(reformObj, lazyVars);
			addLowerBound(origObj, lower_bound, lastLowerBound);
			return;
		}
		// figure out an appropriate core
		core.simplifyToCardinality(false);

		// adjust the lower bound
		if (core.getDegree() > 1) ++stats.NCORECARDINALITIES;
		long long mult = INF;
		for (Var v: core.vars) {
			assert(reformObj.getLit(v) != 0);
			mult = std::min<long long>(mult, std::abs(reformObj.coefs[v]));
		}
		assert(mult < INF);
		assert(mult > 0);
		lower_bound += core.getDegree() * mult;

		if ((options.optMode == 2 || options.optMode == 4) && core.vars.size() - core.getDegree() > 1) {
			// add auxiliary variable
			long long newN = n + 1;
			solver.setNbVariables(newN);
			core.resize(newN + 1);
			reformObj.resize(newN + 1);
			// reformulate the objective
			core.invert();
			reformObj.addUp(solver.Level, core, mult, 1, false);
			core.invert();
			reformObj.addLhs(mult, newN); // add only one variable for now
			assert(lower_bound == -reformObj.getDegree());
			// add first lazy constraint
			LazyVar* lv = new LazyVar(core, newN, mult); // TODO: shared_ptr
			lazyVars.push_back(lv);
			lv->addAtLeastConstraint();
			lv->addAtMostConstraint();
		} else {
			// add auxiliary variables
			long long oldN = n;
			long long newN = oldN - core.getDegree() + core.vars.size();
			solver.setNbVariables(newN);
			core.resize(newN + 1);
			reformObj.resize(newN + 1);
			// reformulate the objective
			for (Var v = oldN + 1; v <= newN; ++v) core.addLhs(-1, v);
			core.invert();
			reformObj.addUp(solver.Level, core, mult, 1, false);
			assert(lower_bound == -reformObj.getDegree());
			// add channeling constraints
			if (solver.addConstraint(core, ConstraintType::AUXILIARY) == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
			core.invert();
			if (solver.addConstraint(core, ConstraintType::AUXILIARY) == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
			for (Var v = oldN + 1; v < newN; ++v) { // add symmetry breaking constraints
				if (solver.addConstraint({1, 1}, {v, -v - 1}, 1, ConstraintType::AUXILIARY) == ID_Unsat) io::exit_UNSAT(solution,upper_bound);
			}
		}
		checkLazyVariables(reformObj, lazyVars);
		addLowerBound(origObj, lower_bound, lastLowerBound);
	}

	void optimize(intConstr& origObj) {
		assert(origObj.vars.size() > 0);
		// NOTE: -origObj.getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
		origObj.removeUnitsAndZeroes(solver.Level, solver.Pos, false);
		lower_bound = -origObj.getDegree();
		upper_bound = std::numeric_limits<Val>::max();
		core.initializeLogging(logger);

		Val opt_coef_sum = 0;
		for (Var v: origObj.vars) opt_coef_sum += std::abs(origObj.coefs[v]);
		if (opt_coef_sum >= (Val) INF)
			io::exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."}); // TODO: remove restriction

		longConstr reformObj;
		origObj.copyTo(reformObj);
		ID lastUpperBound = ID_Undef;
		ID lastLowerBound = ID_Undef;

		IntSet assumps;
		std::vector<LazyVar*> lazyVars;
		size_t upper_time = 0, lower_time = 0;
		SolveState reply = SolveState::SAT;
		while (true) {
			size_t current_time = stats.getDetTime();
			if (reply != SolveState::INPROCESSING) printObjBounds(lower_bound, upper_bound);
			assumps.reset();
			if (options.optMode == 1 || options.optMode == 2 || (options.optMode > 2 && lower_time < upper_time)) { // use core-guided step
				reformObj.removeZeroes();
				for (Var v: reformObj.vars) {
					assert(reformObj.getLit(v) != 0);
					assumps.add(-reformObj.getLit(v));
				}
				std::sort(assumps.keys.begin(), assumps.keys.end(), [&](Lit l1, Lit l2) {
					return reformObj.getCoef(-l1) > reformObj.getCoef(-l2) ||
					       (reformObj.getCoef(-l1) == reformObj.getCoef(-l2) && std::abs(l1) < std::abs(l2));
				});
			}
			assert(upper_bound > lower_bound);
			reply = solver.solve(assumps, core, solution);
			if (reply == SolveState::INTERRUPTED) io::exit_INDETERMINATE(solution);
			else if (reply == SolveState::UNSAT) io::exit_UNSAT(solution,upper_bound);
			assert(solver.decisionLevel() == 0);
			if (assumps.size() == 0) upper_time += stats.getDetTime() - current_time;
			else lower_time += stats.getDetTime() - current_time;
			if (reply == SolveState::SAT) {
				assert(solution.size() > 0);
				++stats.NSOLS;
				handleNewSolution(origObj, lastUpperBound);
				assert((options.optMode != 1 && options.optMode != 2) || lower_bound == upper_bound);
			} else if (reply == SolveState::INCONSISTENT) {
				++stats.NCORES;
				if (core.getSlack(solver.Level) < 0) {
					if (logger) core.logInconsistency(solver.Level, solver.Pos, stats);
					assert(solver.decisionLevel() == 0);
					io::exit_UNSAT(solution,upper_bound);
				}
				handleInconsistency(reformObj, origObj, lazyVars, lastLowerBound);
				core.resize(n+1);
			} // else reply==SolveState::INPROCESSING, keep looping
			if (lower_bound >= upper_bound) {
				printObjBounds(lower_bound, upper_bound);
				if (logger) {
					assert(lastUpperBound != ID_Undef);
					assert(lastUpperBound != ID_Unsat);
					assert(lastLowerBound != ID_Undef);
					assert(lastLowerBound != ID_Unsat);
					aux.initializeLogging(logger);
					longConstr coreAggregate;
					coreAggregate.initializeLogging(logger);
					coreAggregate.resize(n + 1);
					origObj.copyTo(aux);
					aux.invert();
					aux.addRhs(1 - upper_bound);
					aux.resetBuffer(lastUpperBound - 1); // -1 to get the unprocessed formula line
					coreAggregate.addUp(solver.Level, aux, 1, 1, false);
					aux.reset();
					origObj.copyTo(aux);
					aux.addRhs(lower_bound);
					aux.resetBuffer(lastLowerBound - 1); // -1 to get the unprocessed formula line
					coreAggregate.addUp(solver.Level, aux, 1, 1, false);
					aux.reset();
					assert(coreAggregate.getSlack(solver.Level) < 0);
					assert(solver.decisionLevel() == 0);
					coreAggregate.logInconsistency(solver.Level, solver.Pos, stats);
				}
				io::exit_UNSAT(solution,upper_bound);
			}
		}
	}

	void decide() {
		while (true) {
			SolveState reply = solver.solve({}, core, solution);
			assert(reply != SolveState::INCONSISTENT);
			if (reply == SolveState::INTERRUPTED) io::exit_INDETERMINATE({});
			if (reply == SolveState::SAT) io::exit_SAT(solution);
			else if (reply == SolveState::UNSAT) io::exit_UNSAT({},0);
		}
	}

}

// ---------------------------------------------------------------------
// Exit and interrupt

static void SIGINT_interrupt(int signum){
	_unused(signum);
	asynch_interrupt = true;
}

static void SIGINT_exit(int signum){
	_unused(signum);
	printf("\n*** INTERRUPTED ***\n");
	exit(1);
}

// ---------------------------------------------------------------------
// Main

int main(int argc, char**argv){
	stats.STARTTIME=aux::cpuTime();
	asynch_interrupt=false;

	signal(SIGINT, SIGINT_exit);
	signal(SIGTERM,SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);

	intConstr objective;

	options = io::read_options(argc, argv);
	if(!options.proofLogName.empty()) logger = std::make_shared<Logger>(options.proofLogName);
	solver.tmpConstraint.initializeLogging(logger);
	solver.conflConstraint.initializeLogging(logger);
	solver.logConstraint.initializeLogging(logger);

	if (!options.formulaName.empty()) {
		std::ifstream fin(options.formulaName);
		if (!fin) io::exit_ERROR({"Could not open ",options.formulaName});
		parser::file_read(fin,objective);
	} else {
		if (options.verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
		parser::file_read(std::cin,objective);
	}
	if(logger) logger->formula_out << "* INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW\n";
	std::cout << "c #variables=" << orig_n << " #constraints=" << solver.constraints.size() << std::endl;

	signal(SIGINT, SIGINT_interrupt);
	signal(SIGTERM,SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);

	if(objective.vars.size() > 0) meta::optimize(objective);
	else meta::decide();
}
