/***********************************************************************
Copyright (c) 2014-2019, Jan Elffers
Copyright (c)      2019, Jo Devriendt

Parts of the code were copied or adapted from Minisat.

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

using namespace std;
#include <vector>
#include <iostream>
#include <sstream>
#include <fstream>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <csignal>
#include <map>

#define _unused(x) ((void)(x)) // marks variables unused in release mode

std::ostream& operator<<(std::ostream& os, __int128 t) { return os << (double) t; }

template <class T> inline void swapErase(T& indexable, size_t index){
	indexable[index]=indexable.back();
	indexable.pop_back();
}

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE(),exit_ERROR(const std::initializer_list<std::string>&);

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

enum DeletionStatus { LOCKED, UNLOCKED, FORCEDELETE, MARKEDFORDELETE };

struct Clause {
	struct {
		unsigned status       : 2;
		unsigned lbd          : 30;
		unsigned unused       : 1;
		unsigned learnt       : 1;
		unsigned size         : 30;
	} header;
	float act;
	int w; // TODO: not needed in memory actually...
	// watch data
	unsigned int nbackjump;
	int slack; // sum of non-falsified watches minus w.
	// NOTE: will never be larger than 2 * non-falsified watch, so fits in 32 bit for the n-watched literal scheme
	int watchIdx;
	int propIdx;
	// ordinary data
	int data[0]; // TODO: data as pairs of coef-lit instead of list of all lits, then all coefs?

	inline size_t size() const { return header.size; }
	inline int * lits() { return data; }
	inline int * coefs() { return (int*)(data+header.size); }

	inline void setStatus(DeletionStatus ds){ header.status=(unsigned) ds; }
	inline DeletionStatus getStatus(){ return (DeletionStatus) header.status; }
	inline void setLBD(unsigned int lbd){ header.lbd=min(header.lbd,lbd); }
	inline unsigned int lbd() const { return header.lbd; }
	inline bool learnt() const { return header.learnt; }
	inline int largestCoef() { return abs(coefs()[0]); }
	inline int coef(int i) { return abs(coefs()[i]); }
	inline bool isWatched(int idx) { return coefs()[idx]<0; }
	inline bool isClause() const { return w==-1; }
};

struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
int verbosity = 1;
// currently, the maximum number of variables is hardcoded (variable N), and most arrays are of fixed size.
int n = 0;
int orig_n = 0;
vector<CRef> clauses, learnts, external;
struct Watch {
	CRef cref;
	int idx;
};
const int resize_factor=2;
const int INF=1e9+1;

double initial_time;
size_t NBACKJUMP=0, DETERMINISTICTIME=0;
long long NCONFL=0, NDECIDE=0, NPROP=0;
__int128 LEARNEDLENGTHSUM=0, LEARNEDDEGREESUM=0;
long long NCLAUSESLEARNED=0, NCARDINALITIESLEARNED=0, NGENERALSLEARNED=0;
long long NGCD=0, NCARDDETECT=0, NCORECARDINALITIES=0, NCORES=0;
long long NWEAKENEDNONIMPLYING=0, NWEAKENEDNONIMPLIED=0;
double rinc = 2;
int rfirst = 100;
int nbclausesbeforereduce=2000;
int incReduceDB=300;
int cnt_reduceDB=0;
bool originalRoundToOne=false;
int opt_mode=0;
int curr_restarts=0;
long long nconfl_to_restart=0;

template <class T>
inline T ceildiv(const T& p,const T& q){ assert(q>0); assert(p>=0); return (p+q-1)/q; }
template <class T>
inline T floordiv(const T& p,const T& q){ assert(q>0); assert(p>=0); return p/q; }
template <class T>
inline T ceildiv_safe(const T& p,const T& q){ assert(q>0); return (p<0?-floordiv(-p,q):ceildiv(p,q)); }
template <class T>
inline T floordiv_safe(const T& p,const T& q){ assert(q>0); return (p<0?-ceildiv(-p,q):floordiv(p,q)); }

template<class T> void resizeLitMap(std::vector<T>& _map, typename std::vector<T>::iterator& map, int size, T init){
	assert(size<(1<<28));
	int oldsize = (_map.size()-1)/2;
	if(oldsize>=size) return;
	int newsize = oldsize;
	while(newsize<size) newsize=newsize*resize_factor+1;
	_map.resize(2*newsize+1);
	map=_map.begin()+newsize;
	int i=_map.size()-1;
	for(; i>newsize+oldsize; --i) _map[i]=init;
	for(; i>=newsize-oldsize; --i) _map[i]=_map[i-newsize+oldsize];
	for(; i>=0; --i) _map[i]=init;
}

unsigned int gcd(unsigned int u, unsigned int v){
	assert(u!=0);
	assert(v!=0);
	if (u%v==0) return v;
	if (v%u==0) return u;
	unsigned int t;
	int shift = __builtin_ctz(u | v);
	u >>= __builtin_ctz(u);
	do {
		v >>= __builtin_ctz(v);
		if (u > v) { t = v; v = u; u = t; }
		v = v - u;
	} while (v != 0);
	return u << shift;
}

vector<vector<Watch>> _adj={{}}; vector<vector<Watch>>::iterator adj;
vector<int> _Level={-1}; vector<int>::iterator Level;
vector<int> trail, trail_lim, Pos;
vector<CRef> Reason;
int qhead; // for unit propagation
int last_sol_obj_val = INF;
inline bool foundSolution(){return last_sol_obj_val<INF;}
vector<bool> last_sol;
vector<int> phase;
inline void newDecisionLevel() { trail_lim.push_back(trail.size()); }
inline int decisionLevel() { return trail_lim.size(); }

template<class SMALL, class LARGE> // LARGE should be able to fit sums of SMALL
struct Constraint{
	std::vector<int> vars;
	vector<SMALL> coefs;
	LARGE rhs = 0;
	static constexpr SMALL _unused_(){ return std::numeric_limits<SMALL>::max(); }

	inline void resize(size_t s){
		if(s>coefs.size()) coefs.resize(s,_unused_());
	}

	void reset(LARGE r=0){
		for(int v: vars) coefs[v]=_unused_();
		vars.clear();
		rhs=r;
	}

	void init(Clause& C){
		reset();
		for(size_t i=0;i<C.size();++i) addLhs(C.coef(i), C.lits()[i]);
		addRhs(C.w);
		saturate();
	}

	long long removeUnits(bool doSaturation=true){
		for(int i=0; i<(int)vars.size(); ++i){
			int v=vars[i];
			if(Level[v]==0) addRhs(-coefs[v]);
			if(Level[v]==0 || Level[-v]==0){
				coefs[v]=_unused_();
				swapErase(vars,i--);
			}
		}
		if(doSaturation) return saturate();
		else return getDegree();
	}

	void removeZeroes(){
		for(int i=0; i<(int)vars.size(); ++i){
			int v=vars[i];
			if(coefs[v]==0){
				coefs[v]=_unused_();
				swapErase(vars,i--);
			}
		}
	}

	void addLhs(SMALL c, int l){ // treat negative literals as 1-v
		assert(l!=0);
		if(c==0 || Level[-l]==0) return;
		if(Level[l]==0){ rhs-=c; return; }
		int v = l;
		if(l<0){
			rhs -= c;
			c = -c;
			v = -l;
		}
		assert(v<(int)coefs.size());
		if(coefs[v]==_unused_()) vars.push_back(v), coefs[v]=0;
		coefs[v]+=c;
	}

	inline void addRhs(SMALL r){ rhs+=r; }
	inline LARGE getRhs() const { return rhs; }
	inline LARGE getDegree() const {
		LARGE result = rhs;
		for (int v: vars) result -= min<SMALL>(0,coefs[v]); // considering negative coefficients
		return result;
	}
	inline SMALL getCoef(int l) const { return coefs[abs(l)]==_unused_()?0:(l<0?-coefs[-l]:coefs[l]); }
	inline int getLit(int l) const { // NOTE: always check for answer "0"!
		int v = abs(l);
		SMALL c = coefs[v];
		if(c==0 || c==_unused_()) return 0;
		else if(c<0) return -v;
		else return v;
	}
	inline bool increasesSlack(int v) const { // NOTE: equivalent to "non-falsified" for a normal-form constraint
		assert((getLit(v)!=0 && Level[-getLit(v)]==-1)==(coefs[v]>0 && Level[-v]==-1) || (coefs[v]<0 && Level[v]==-1));
		return (coefs[v]>0 && Level[-v]==-1) || (coefs[v]<0 && Level[v]==-1);
	}

	inline void weaken(SMALL m, int l){ // add either abs(m)*(l>=0) or abs(m)*(-l>=-1)
		addLhs(m,l);
		if(m<0) addRhs(m);
	}

	LARGE saturate(){ // returns degree
		LARGE w = getDegree();
		if(w<=0) reset(), rhs=w;
		for (int v: vars){
			if(coefs[v]>w) coefs[v]=w;
			if(coefs[v]<-w) rhs-=coefs[v]+w, coefs[v]=-w;
		}
		assert(w==getDegree()); // degree is invariant under saturation
		return w;
	}

	template<class COEFS, class RHS>
	void getNormalForm(std::vector<int>& lits, std::vector<COEFS>& cs, RHS& w) const {
		lits.clear(); cs.clear();
		w=getDegree();
		if(w<=0) return;
		lits.reserve(vars.size()); cs.reserve(vars.size());
		for(int v: vars){
			int l = getLit(v);
			if(l==0) continue;
			lits.push_back(l);
			cs.push_back(min<LARGE>(getCoef(l),w));
		}
	}

	template<class S, class L>
	void copyTo(Constraint<S,L>& out, S mult=1) const {
		out.reset();
		out.resize(coefs.size());
		out.vars=vars;
		for(int v: vars) out.coefs[v]=mult*coefs[v];
		out.rhs=mult*rhs;
	}

	LARGE getSlack() const {
		LARGE slack = -rhs;
		for(int v: vars) if(Level[v]!=-1 || (Level[-v]==-1 && coefs[v]>0)) slack+=coefs[v];
		return slack;
	}

	template<class S, class L>
	void add(const Constraint<S,L>& c, SMALL mult=1, bool saturateAndReduce=true){
		assert(mult>0);
		for(int v: c.vars) addLhs(mult*c.coefs[v],v);
		addRhs(mult*c.rhs);
		if(!saturateAndReduce) return;
		LARGE deg = saturate();
		if (deg > (int) 1e9) roundToOne(ceildiv<LARGE>(deg,1e9),!originalRoundToOne);
		assert(getDegree() <= (int)1e9);
	}

	void roundToOne(SMALL d, bool partial){
		assert(d>0);
		for(int v:vars){
			assert(Level[-v]!=0);
			assert(Level[ v]!=0);
			if(coefs[v]%d==0){ coefs[v]/=d; continue; }
			else if(increasesSlack(v)){
				if(partial) weaken(-coefs[v]%d,v); // partial weakening
				else weaken(-coefs[v],v);
			}else{
				assert((Level[v]==-1)==(coefs[v]>0));
				if(coefs[v]<0) weaken(-d-(coefs[v]%d),v);
				else weaken(d-(coefs[v]%d),v);
			}
			assert(coefs[v]%d==0);
			coefs[v]/=d;
		}
		// NOTE: as all coefficients are divisible by d, we can ceildiv the rhs instead of the degree
		rhs=ceildiv_safe<LARGE>(rhs,d);
		saturate();
	}

	bool isCardinality() const {
		for(int v: vars) if(abs(coefs[v])>1) return false;
		return true;
	}

	bool simplifyToCardinality(bool equivalencePreserving){
		if(isCardinality()) return false;
		sort(vars.begin(),vars.end(),[&](int v1, int v2){return abs(coefs[v1])<abs(coefs[v2]);});
		LARGE degree = getDegree();
		assert(degree>0);
		assert(coefs[vars[0]]!=0);

		int largeCoefsNeeded=1;
		LARGE largeCoefSum=0;
		for(; largeCoefsNeeded<=(int)vars.size(); ++largeCoefsNeeded){
			largeCoefSum+=abs(coefs[vars[vars.size()-largeCoefsNeeded]]);
			if(largeCoefSum>=degree) break;
		}
		if(largeCoefSum<degree){ // trivially unsatisfiable constraint
			reset(1); return true;
		}

		int skippable=0;
		if(equivalencePreserving){
			LARGE smallCoefSum=0;
			for(int i=0; i<largeCoefsNeeded; ++i) smallCoefSum+=abs(coefs[vars[i]]);
			if(smallCoefSum<degree) return false;
			// else, we have an equivalent cardinality constraint
		}else{
			LARGE wiggleroom=degree-largeCoefSum+abs(coefs[vars[vars.size()-largeCoefsNeeded]]);
			assert(wiggleroom>0);
			for(; skippable<(int)vars.size(); ++skippable){
				wiggleroom-=abs(coefs[vars[skippable]]);
				if(wiggleroom<=0) break;
			}
			assert(skippable<(int)vars.size());
		}

		rhs=largeCoefsNeeded;
		// TODO: sort vars from large to small to be able to simply pop skippable literals
		for(int i=0; i<skippable; ++i) coefs[vars[i]]=0;
		for(int i=skippable; i<(int)vars.size(); ++i){
			int v = vars[i];
			if(coefs[v]<0){
				coefs[v]=-1;
				--rhs;
			}else coefs[v]=1;
		}
		removeZeroes();
		return true;
	}

	bool divideByGCD(){
		if(isCardinality()) return false;
		int mn=INF;
		for(int v: vars){
			SMALL c = abs(coefs[v]);
			mn=min(mn,c);
			if(c==1 || c>1e9) return false; // TODO: large coefs currently unsupported
		}
		assert(mn<INF); assert(mn>0);
		unsigned int _gcd = mn;
		for(int v: vars){
			_gcd = gcd(_gcd,(unsigned int) abs(coefs[v]));
			if(_gcd==1) return false;
		}
		assert(_gcd>1);
		for (int v: vars) coefs[v] /= (int)_gcd;
		// NOTE: as all coefficients are divisible, we can ceildiv the rhs instead of the degree
		rhs=ceildiv_safe<LARGE>(rhs,_gcd);
		return true;
	}

	// NOTE: only equivalence preserving operations here!
	void postProcess(){
		removeZeroes();
		LARGE degree = removeUnits();
		if(degree>1 && divideByGCD()) ++NGCD;
		if(degree>1 && simplifyToCardinality(true)) ++NCARDDETECT;
	}

	bool falsifiedCurrentLvlIsOne(){
		bool foundOne=0;
		for(int i=0; i<(int)vars.size(); ++i){
			int v = vars[i];
			if((coefs[v]>0 && Level[-v]==decisionLevel()) || (coefs[v]<0 && Level[v]==decisionLevel())){
				vars[i]=vars[foundOne];
				vars[foundOne]=v;
				if(foundOne) return false;
				else foundOne=1;
			}
		}
		return foundOne;
	}

	// @return: earliest decision level that propagates a variable
	int getAssertionLevel(){
		assert(getSlack()<0);
		if(decisionLevel()==0) return 0;
		removeZeroes(); // ensures getLit is never 0

		// calculate slack at level -1
		LARGE slack = -rhs;
		for(int v: vars) if(coefs[v]>0) slack+=coefs[v];
		if(slack<0) return 0;

		// create useful datastructures
		std::sort(vars.begin(),vars.end(),[&](int v1,int v2){ return abs(coefs[v1])>abs(coefs[v2]); });
		std::vector<int> litsByPos;
		litsByPos.reserve(vars.size());
		for(int v: vars){
			int l = getLit(v);
			if(~Level[-l]) litsByPos.push_back(-l);
		}
		std::sort(litsByPos.begin(),litsByPos.end(),[&](int l1,int l2){ return Pos[abs(l1)]<Pos[abs(l2)]; });

		// calculate earliest propagating decision level by decreasing slack one decision level at a time
		auto posIt = litsByPos.cbegin();
		auto coefIt = vars.cbegin();
		int assertionLevel = 0;
		while(true){
			while(posIt!=litsByPos.cend() && Level[*posIt]<=assertionLevel){
				slack-=abs(coefs[abs(*posIt)]);
				++posIt;
			}
			if(slack<0){ assertionLevel=max(assertionLevel-1,0); break; }
			while((unsigned int)assertionLevel>=(unsigned int)Level[getLit(*coefIt)]) ++coefIt;
			// NOTE: unsigned int cast ensures assertionLevel < -1
			assert(coefIt!=vars.cend());
			if(slack<abs(coefs[*coefIt])) break;
			++assertionLevel;
		}
		assert(assertionLevel<decisionLevel());
		return assertionLevel;
	}

	void weakenNonImplied(LARGE slack){
		for (int v: vars){
			if (abs(coefs[v])<=slack && increasesSlack(v)){
				assert(coefs[v]!=0);
				weaken(-coefs[v],v);
				++NWEAKENEDNONIMPLIED;
			}
		}
	}

	LARGE weakenNonImplying(SMALL propCoef, LARGE slack){
		LARGE wiggle_room = propCoef-slack-1;
		if(wiggle_room<=0) return slack;
		removeZeroes(); // ensures getLit(v)!=0
		int j=0;
		for(int i=0; i<(int)vars.size(); ++i){
			int v = vars[i];
			if(abs(coefs[v])<=wiggle_room && !increasesSlack(v)) vars[i]=vars[j], vars[j]=v, ++j;
		}
		std::sort(vars.begin(),vars.begin()+j,[&](int v1,int v2){
			int c1=abs(coefs[v1]); assert(c1<=wiggle_room);
			int c2=abs(coefs[v2]); assert(c2<=wiggle_room);
			return c1<c2 || (c1==c2 && Pos[v1]>Pos[v2]);
		});
		for(int i=0; i<j; ++i){
			int v = vars[i];
			assert(!increasesSlack(v));
			int c = abs(coefs[v]);
			wiggle_room-=c;
			if(wiggle_room<0) break;
			weaken(-coefs[v],v);
			slack+=c;
			++NWEAKENEDNONIMPLYING;
		}
		assert(slack==getSlack());
		return slack;
	}

	LARGE heuristicWeakening(){
		LARGE slk = getSlack();

		SMALL smallestPropagated=_unused_(); // smallest coefficient of propagated literals
		if (slk >= 0) {
			for (int v: vars){
				SMALL c = abs(coefs[v]);
				if (Pos[v]==-1 && c>slk) {
					smallestPropagated = min(smallestPropagated, c);
				}
			}
		}
		if(smallestPropagated==_unused_()) return slk; // no propagation, no idea what to weaken
		weakenNonImplied(slk);
		return weakenNonImplying(smallestPropagated,slk);
	}
};

Constraint<int, long long> objective_func;
Constraint<int, long long> tmpConstraint;
Constraint<long long, __int128> confl_data;

template<class S, class L>
ostream & operator<<(ostream & o, const Constraint<S,L>& C) {
	std::vector<int> vars = C.vars;
	sort(vars.begin(),vars.end(), [](S v1, S v2) { return v1<v2; });
	for(int v: vars){
		int l = C.getLit(v);
		if(l==0) continue;
		o << C.getCoef(l) << "x" << l << ":" << (~Level[l]?"t":(~Level[-l]?"f":"u")) << "@" << max(Level[l],Level[-l]) << "," << Pos[abs(l)] << " ";
	}
	o << ">= " << C.getDegree();
	return o;
}
ostream & operator<<(ostream & o, Clause & C) {
	// TODO: improve performance
	Constraint<int,long long> aux;
	aux.resize(n+1);
	aux.init(C);
	o << aux;
	return o;
}

struct IntSet{
private:
	vector<bool> _values={false};
	vector<bool>::iterator values=_values.begin();
	vector<int> keys;
	static constexpr bool _unused_(){ return false; }

public:
	void reset(){
		for(int k: keys) values[k]=_unused_();
		keys.clear();
	}

	inline void resize(int size){ resizeLitMap(_values,values,size,_unused_()); }
	inline int size() const { return keys.size(); }

	inline bool has(int key) const { return values[key]!=_unused_(); }
	void add(int key){
		if(has(key)) return;
		values[key]=true;
		keys.push_back(key);
	}
	inline std::vector<int>& getKeys(){ return keys; }
};

IntSet tmpSet;
IntSet actSet;

// ---------------------------------------------------------------------
// memory. maximum supported size of learnt clause database is 16GB

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size)
{
	void* mem = realloc(ptr, size);
	if (mem == NULL && errno == ENOMEM){
		throw OutOfMemoryException();
	}else
		return mem;
}
struct {
	uint32_t* memory;
	uint32_t at=0, cap=0;
	uint32_t wasted=0; // for GC
	void capacity(uint32_t min_cap){
		if (cap >= min_cap) return;

		uint32_t prev_cap = cap;
		while (cap < min_cap){
			// NOTE: Multiply by a factor (13/8) without causing overflow, then add 2 and make the
			// result even by clearing the least significant bit. The resulting sequence of capacities
			// is carefully chosen to hit a maximum capacity that is close to the '2^32-1' limit when
			// using 'uint32_t' as indices so that as much as possible of this space can be used.
			uint32_t delta = ((cap >> 1) + (cap >> 3) + 2) & ~1;
			cap += delta;

			if (cap <= prev_cap)
				throw OutOfMemoryException();
		}
		// printf(" .. (%p) cap = %u\n", this, cap);

		assert(cap > 0);
		memory = (uint32_t*) xrealloc(memory, sizeof(uint32_t) * cap);
	}
	int sz_clause(int length) { return (sizeof(Clause)+sizeof(int)*length+sizeof(int)*length)/sizeof(uint32_t); }

	CRef alloc(const Constraint<int,long long>& constraint, bool learnt, bool locked){
		long long degree = constraint.getDegree();
		assert(degree>0);
		assert(degree<=1e9);
		// as the constraint should be saturated, the coefficients are between 1 and 1e9 as well.
		int w = (int)degree;

		assert(!constraint.vars.empty());
		unsigned int length = constraint.vars.size();
		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		capacity(at + sz_clause(length));
		Clause * clause = (Clause*)(memory+at);
		new (clause) Clause;
		at += sz_clause(length);
		clause->header = {(unsigned) (locked?LOCKED:UNLOCKED),length,0,learnt,length};
		clause->act = 0;
		clause->nbackjump = 0;
		clause->slack = -w;
		clause->watchIdx = 0;
		clause->propIdx = 0;
		clause->w = w;
		for(unsigned int i=0;i<length;i++){
			int v = constraint.vars[i];
			assert(constraint.getLit(v)!=0);
			clause->lits()[i]=constraint.getLit(v);
			clause->coefs()[i]=abs(constraint.coefs[v]);
		}
		return {(uint32_t)(at-sz_clause(length))};
	}
	Clause& operator[](CRef cr) { return (Clause&)*(memory+cr.ofs); }
	const Clause& operator[](CRef cr) const { return (Clause&)*(memory+cr.ofs); }
} ca;

// VSIDS ---------------------------------------------------------------
double var_decay=0.95;
double var_inc=1.0;
vector<double> activity;
struct{
	int cap=0;
	// segment tree (fast implementation of priority queue).
	vector<int> tree = {-1,-1};
	void resize(int newsize) {
		if (cap >= newsize) return;
		// insert elements in such order that tie breaking remains intact
		vector<int> variables;
		while (!empty()) variables.push_back(removeMax());
		tree.clear();
		while(cap<newsize) cap=cap*resize_factor+1;
		tree.resize(2*(cap+1), -1);
		for (int x : variables) insert(x);
	}
	void percolateUp(int x) {
		for(int at=x+cap+1; at>1; at>>=1){
			if(tree[at^1]==-1 || activity[x]>activity[tree[at^1]])tree[at>>1]=x;
			else break;
		}
	}
	bool empty() { return tree[1] == -1; }
	bool inHeap(int v) { return tree[v+cap+1] != -1; }
	void insert(int x) {
		assert(x<=cap);
		if (inHeap(x)) return;
		tree[x+cap+1] = x;
		percolateUp(x);
	}
	int removeMax() {
		int x = tree[1];
		assert(x != -1);
		tree[x+cap+1] = -1;
		for(int at=x+cap+1; at>1; at>>=1){
			if(tree[at^1] != -1 && (tree[at]==-1 || activity[tree[at^1]]>activity[tree[at]]))tree[at>>1]=tree[at^1];
			else tree[at>>1]=tree[at];
		}
		return x;
	}
} order_heap;

void varDecayActivity() { var_inc *= (1 / var_decay); }
void varBumpActivity(int v){
	assert(v>0);
	if ( (activity[v] += var_inc) > 1e100 ) {
		// Rescale:
		for (int i = 1; i <= n; i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100; }

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.percolateUp(v); }
// CLAUSE VSIDS --------------------------------------------------------
double cla_inc=1.0;
double clause_decay=0.999;
void claDecayActivity() { cla_inc *= (1 / clause_decay); }
void claBumpActivity (Clause& c) {
		if ( (c.act += cla_inc) > 1e20 ) {
			// Rescale:
			for (size_t i = 0; i < learnts.size(); i++)
				ca[learnts[i]].act *= 1e-20;
			cla_inc *= 1e-20; } }
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void uncheckedEnqueue(int p, CRef from=CRef_Undef){
	assert(Pos[abs(p)]==-1);
	int v = abs(p);
	Level[p] = decisionLevel();
	Pos[v] = (int) trail.size();
	trail.push_back(p);
	Reason[v]=CRef_Undef;
	if(decisionLevel()==0) ++NPROP; // avoid locked clauses for unit literals
	else if(from!=CRef_Undef){ ++NPROP;	Reason[v]=from; }
}

// @pre: removeUnits and removeZeroes executed on constraint
CRef attachConstraint(Constraint<int,long long>& constraint, bool learnt, bool locked=false){
	// sort from smallest to largest coefficient
	std::sort(constraint.vars.begin(),constraint.vars.end(),[&](int v1,int v2){
		return abs(constraint.coefs[v1])>abs(constraint.coefs[v2]); });

	CRef cr = ca.alloc(constraint, learnt, locked);
	if (learnt) learnts.push_back(cr);
	else clauses.push_back(cr);
	Clause& C = ca[cr]; int* lits = C.lits(); int* coefs = C.coefs();

	for(int i=0; i<(int)C.size() && C.slack<C.largestCoef(); ++i){
		int l = lits[i];
		if(Level[-l]==-1 || Pos[abs(l)]>=qhead){
			assert(!C.isWatched(i));
			C.slack+=coefs[i];
			coefs[i]=-coefs[i];
			adj[l].push_back({cr,i});
		}
	}
	assert(C.slack>=0);
	if(C.slack<C.largestCoef()){
		// set sufficient falsified watches
		std::vector<int> falsifieds;
		falsifieds.reserve(C.size());
		for(int i=0; i<(int)C.size(); ++i) if(~Level[-lits[i]]) falsifieds.push_back(i);
		std::sort(falsifieds.begin(),falsifieds.end(),[&](int i1,int i2){ return Pos[abs(lits[i1])]>Pos[abs(lits[i2])]; });
		int diff = C.largestCoef()-C.slack;
		for(int i: falsifieds){
			assert(!C.isWatched(i));
			diff-=coefs[i];
			coefs[i]=-coefs[i];
			adj[lits[i]].push_back({cr,i});
			if(diff<=0) break;
		}
	}
	// perform initial propagation
	for(int i=0; i<(int)C.size() && abs(coefs[i])>C.slack; ++i) if(Pos[abs(lits[i])]==-1) uncheckedEnqueue(lits[i],cr);
	return cr;
}

void undoOne(){
	assert(!trail.empty());
	int l = trail.back();
	if(qhead==(int)trail.size()){
		for(const Watch& w: adj[-l]){
			Clause& C = ca[w.cref];
			assert(C.isWatched(w.idx));
			C.slack += C.coef(w.idx);
		}
		--qhead;
	}
	int v = abs(l);
	trail.pop_back();
	Level[l] = -1;
	Pos[v] = -1;
	phase[v] = l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	order_heap.insert(v);
}

void backjumpTo(int level){
	assert(level>=0);
	++NBACKJUMP; assert(NBACKJUMP<std::numeric_limits<unsigned int>::max());
	while(decisionLevel()>level) undoOne();
}

void decide(int l){
	newDecisionLevel();
	uncheckedEnqueue(l);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void recomputeLBD(Clause& C) {
	if(C.lbd()<=2) return;
	tmpSet.reset();
	int * lits = C.lits();
	for (int i=0; i<(int)C.size(); i++) if (~Level[-lits[i]]) tmpSet.add(Level[-lits[i]]);
	C.setLBD(tmpSet.size());
}

void analyze(CRef confl){
	Clause & C = ca[confl];
	if (C.learnt()) {
		claBumpActivity(C);
		recomputeLBD(C);
	}

	confl_data.init(C);
	actSet.reset();
	for(int v: confl_data.vars) actSet.add(confl_data.getLit(v));
	while(1){
		if (decisionLevel() == 0) {
			assert(0>confl_data.getSlack());
			exit_UNSAT();
		}
		int l = trail.back();
		int confl_coef_l = confl_data.getCoef(-l);
		if(confl_coef_l>0) {
			if (confl_data.falsifiedCurrentLvlIsOne()) {
				break;
			} else {
				assert(Reason[abs(l)] != CRef_Undef);
				if(originalRoundToOne){
					confl_data.roundToOne(confl_coef_l,false);
					confl_coef_l=1;
				}
				Clause& reasonC = ca[Reason[abs(l)]];
				if (reasonC.learnt()) {
					claBumpActivity(reasonC);
					recomputeLBD(reasonC);
				}
				tmpConstraint.init(reasonC);
				tmpConstraint.weakenNonImplying(tmpConstraint.getCoef(l),tmpConstraint.getSlack());
				tmpConstraint.roundToOne(tmpConstraint.getCoef(l),!originalRoundToOne);
				for(int v: tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
				confl_data.add(tmpConstraint,confl_coef_l);
				assert(confl_data.getCoef(-l)==0);
				assert(0>confl_data.getSlack());
			}
		}
		undoOne();
	}
	assert(0>confl_data.getSlack());
	for(int l: actSet.getKeys()) if(l!=0) varBumpActivity(abs(l));
}

/**
 * Unit propagation with watched literals.
 *
 * post condition: the propagation queue is empty (even if there was a conflict).
 */
CRef propagate() {
	CRef confl = CRef_Undef;
	while(qhead<(int)trail.size() && confl==CRef_Undef){
		int p=trail[qhead++];
		vector<Watch> & ws = adj[-p];
		for(int it_ws=0; it_ws<(int)ws.size(); ++it_ws){
			++DETERMINISTICTIME;
			CRef cr = ws[it_ws].cref;
			int idx = ws[it_ws].idx;
			Clause & C = ca[cr];
			if(C.getStatus()>=FORCEDELETE){ swapErase(ws,it_ws--); continue; }
			if(C.nbackjump<NBACKJUMP) C.nbackjump=NBACKJUMP, C.propIdx=0, C.watchIdx=0;
			const int * const lits = C.lits(); int * const coefs = C.coefs();
			const int Csize = C.size(); const int ClargestCoef = C.largestCoef();
			int Cslack = C.slack;
			const int c = coefs[idx];
			assert(c<0);
			Cslack+=c;
			if(Cslack-c>=ClargestCoef){ // look for new watches
				int i=C.watchIdx;
				DETERMINISTICTIME-=i;
				for(; i<Csize && Cslack<ClargestCoef; ++i){ // NOTE: innermost loop of RoundingSat
					const int l = lits[i];
					const int cf = coefs[i];
					if(Level[-l]==-1 && cf>0){
						Cslack+=cf;
						coefs[i]=-cf;
						adj[l].push_back({cr,i});
					}
				}
				DETERMINISTICTIME+=i;
				C.watchIdx=i;
			} // else we did not find enough watches last time, so we can skip looking for them now
			C.slack=Cslack;

			if(Cslack>=ClargestCoef){ // new watches are sufficient, remove previous watch
				coefs[idx]=-c;
				swapErase(ws,it_ws--);
			}else if(Cslack>=0){ // keep the watch, check for propagation
				int i=C.propIdx;
				DETERMINISTICTIME-=i;
				for(; i<Csize && abs(coefs[i])>Cslack; ++i){
					const int l = lits[i];
					if(Pos[abs(l)]==-1) uncheckedEnqueue(l,cr);
				}
				DETERMINISTICTIME+=i;
				C.propIdx=i;
			}else{ // conflict, clean up current level and stop propagation
				confl=cr;
				for(int i=0; i<=it_ws; ++i){
					Clause& constraint = ca[ws[i].cref];
					if(constraint.isClause()) continue;
					constraint.slack += constraint.coef(ws[i].idx);
				}
				--qhead;
				break;
			}
		}
	}
	return confl;
}

int pickBranchLit(){
	int next = 0;
	// Activity based decision:
	while (next == 0 || Pos[next]!=-1){
		if (order_heap.empty()) return 0;
		else next = order_heap.removeMax();
	}
	assert(phase[0]==0);
	return phase[next];
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Initialization
void init(){
	qhead = 0;
	ca.memory = NULL;
	ca.at = 0;
	ca.cap = 0;
	ca.wasted = 0;
	ca.capacity(1024*1024);//4MB
}

void setNbVariables(long long nvars){
	if (nvars < 0) exit_ERROR({"Number of variables must be positive."});
	if (nvars > 1e9) exit_ERROR({"Number of variables cannot exceed 1e9."});
	if (nvars <= n) return;
	resizeLitMap(_adj,adj,nvars,{});
	resizeLitMap(_Level,Level,nvars,-1);
	Pos.resize(nvars+1,-1);
	Reason.resize(nvars+1,CRef_Undef);
	activity.resize(nvars+1,0);
	phase.resize(nvars+1,false);
	last_sol.resize(nvars+1,false);
	tmpConstraint.resize(nvars+1);
	confl_data.resize(nvars+1);
	tmpSet.resize(nvars);
	actSet.resize(nvars);
	order_heap.resize(nvars);
	for(int i=n+1;i<=nvars;++i) phase[i] = -i, order_heap.insert(i);
	n = nvars;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Constraint addition

void learnConstraint(Constraint<long long,__int128>& confl){
	assert(confl.getDegree()>0);
	assert(confl.getDegree()<=1e9);

	confl.copyTo(tmpConstraint);
	backjumpTo(tmpConstraint.getAssertionLevel());
	assert(qhead==(int)trail.size()); // jumped back sufficiently far to catch up with qhead

	long long slack = tmpConstraint.heuristicWeakening();
	if(slack < 0) {
		assert(decisionLevel()==0);
		exit_UNSAT();
	}
	tmpConstraint.postProcess();

	CRef cr = attachConstraint(tmpConstraint,true);
	Clause & C = ca[cr];
	recomputeLBD(C);

	LEARNEDLENGTHSUM+=C.size();
	LEARNEDDEGREESUM+=C.w;
	if(C.isClause()) ++NCLAUSESLEARNED;
	else if(tmpConstraint.isCardinality()) ++NCARDINALITIESLEARNED;
	else ++NGENERALSLEARNED;
}

CRef addInputConstraint(Constraint<int, long long>& c, bool initial=false){
	assert(decisionLevel()==0);
	assert(learnts.size()==0 || !initial);
	c.postProcess();
	long long degree = c.getDegree();
	if(degree > (long long) 1e9) exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
	if(degree<=0) return CRef_Undef; // already satisfied.

	long long slack = c.getSlack();
	if(slack < 0)puts("c Inconsistent input constraint"),exit_UNSAT();

	CRef result = attachConstraint(c,!initial,true);
	if (propagate() != CRef_Undef)puts("c Input conflict"),exit_UNSAT();

	return result;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Parsers

/*
 * The OPB parser does not support nonlinear constraints like "+1 x1 x2 +1 x3 x4 >= 1;"
 */
int read_number(const string & s) {
	long long answer = 0;
	for (char c : s) if ('0' <= c && c <= '9') {
		answer *= 10, answer += c - '0';
		if (answer > (int) 1e9) exit_ERROR({"Input formula contains absolute value larger than 10^9: ",s});
	}
	for (char c : s) if (c == '-') answer = -answer;
	return answer;
}

void opb_read(istream & in) {
	Constraint<int,long long> inverted;
	bool first_constraint = true; _unused(first_constraint);
	for (string line; getline(in, line);) {
		if (line.empty()) continue;
		else if (line[0] == '*') continue;
		else {
			for (char & c : line) if (c == ';') c = ' ';
			bool opt_line = line.substr(0, 4) == "min:";
			string line0;
			if (opt_line) line = line.substr(4), assert(first_constraint);
			else {
				string symbol;
				if (line.find(">=") != string::npos) symbol = ">=";
				else symbol = "=";
				assert(line.find(symbol) != string::npos);
				line0 = line;
				line = line.substr(0, line.find(symbol));
			}
			first_constraint = false;
			istringstream is (line);
			tmpConstraint.reset();
			vector<string> tokens;
			{ string tmp; while (is >> tmp) tokens.push_back(tmp); }
			if (tokens.size() % 2 != 0) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(int)tokens.size(); i+=2) if (find(tokens[i].begin(),tokens[i].end(),'x')!=tokens[i].end()) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(int)tokens.size(); i+=2) {
				string scoef = tokens[i];
				string var = tokens[i+1];
				int coef = read_number(scoef);
				bool negated = false;
				string origvar = var;
				if (!var.empty() && var[0] == '~') {
					negated = true;
					var = var.substr(1);
				}
				if (var.empty() || var[0] != 'x') exit_ERROR({"Invalid literal token: ",origvar});
				var = var.substr(1);
				int l = atoi(var.c_str());
				if (!(1 <= l && l <= n)) exit_ERROR({"Literal token out of variable range: ",origvar});
				if (negated) l = -l;
				tmpConstraint.addLhs(coef,l);
			}
			if (opt_line) objective_func=tmpConstraint;
			else {
				tmpConstraint.addRhs(read_number(line0.substr(line0.find("=") + 1)));
				// Handle equality case with two constraints
				if (line0.find(" = ") != string::npos) {
					tmpConstraint.copyTo(inverted,-1);
					addInputConstraint(inverted,true);
				}
				addInputConstraint(tmpConstraint,true); // NOTE: addInputConstraint modifies tmpConstraint, so invert should be called first
			}
		}
	}
	orig_n=n;
}

void wcnf_read(istream & in, long long top) {
	objective_func.reset();
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			long long weight; is >> weight;
			if(weight==0) continue;
			tmpConstraint.reset(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			if(weight<top){ // soft clause
				if(weight>1e9) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
				if(weight<0) exit_ERROR({"Negative clause weight: ",std::to_string(weight)});
				setNbVariables(n+1); // increases n to n+1
				objective_func.resize(n+1);
				objective_func.addLhs(weight,n);
				tmpConstraint.addLhs(1,n);
			} // else hard clause
			addInputConstraint(tmpConstraint,true);
		}
	}
	orig_n = n-objective_func.vars.size();
}

void cnf_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			tmpConstraint.reset(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			addInputConstraint(tmpConstraint,true);
		}
	}
	orig_n=n;
}

void file_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		if (line[0] == 'p') {
			istringstream is (line);
			is >> line; // skip 'p'
			string type; is >> type;
			int n; is >> n;
			setNbVariables(n);
			if(type=="cnf"){
				cnf_read(in);
				return;
			}else if(type == "wcnf"){
				is >> line; // skip nbConstraints
				long long top; is >> top;
				wcnf_read(in, top);
				return;
			}
		} else if (line[0] == '*' && line.substr(0, 13) == "* #variable= ") {
			istringstream is (line.substr(13));
			int n;
			is >> n;
			setNbVariables(n);
			opb_read(in);
			return;
		}
	}
	exit_ERROR({"No supported format [opb, cnf, wcnf] detected."});
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// We assume in the garbage collection method that reduceDB() is the
// only place where clauses are deleted.
void garbage_collect(){
	assert(decisionLevel()==0); // so we don't need to update the pointer of Reason<CRef>
	if (verbosity > 0) puts("c GARBAGE COLLECT");
	for(int l=-n; l<=n; l++) {
		size_t i, j;
		for(i=0,j=0;i<adj[l].size();i++){
			CRef cr = adj[l][i].cref;
			if(ca[cr].getStatus()!=MARKEDFORDELETE) adj[l][j++]=adj[l][i];
		}
		adj[l].erase(adj[l].begin()+j,adj[l].end());
	}
	// clauses, learnts, adj[-n..n], reason[-n..n].
	uint32_t ofs_learnts=0;for(CRef cr:clauses)ofs_learnts+=ca.sz_clause(ca[cr].size());
	sort(learnts.begin(), learnts.end(), [](CRef x,CRef y){return x.ofs<y.ofs;}); // we have to sort here, because reduceDB shuffles them.
	ca.wasted=0;
	ca.at=ofs_learnts;
	vector<CRef> learnts_old = learnts;
	for(CRef & cr : learnts){
		size_t length = ca[cr].size();
		memmove(ca.memory+ca.at, ca.memory+cr.ofs, sizeof(uint32_t)*ca.sz_clause(length));
		cr.ofs = ca.at;
		ca.at += ca.sz_clause(length);
	}
	#define update_ptr(cr) if(cr.ofs>=ofs_learnts)cr=learnts[lower_bound(learnts_old.begin(), learnts_old.end(), cr)-learnts_old.begin()]
	for(int l=-n;l<=n;l++) for(size_t i=0;i<adj[l].size();i++) update_ptr(adj[l][i].cref);
	for(CRef& ext: external) update_ptr(ext);
	#undef update_ptr
}

struct reduceDB_lt {
	bool operator () (CRef x, CRef y) {
		// Main criteria... Like in MiniSat we keep all binary clauses
		if(ca[x].size()> 2 && ca[y].size()==2) return 1;

		if(ca[y].size()>2 && ca[x].size()==2) return 0;
		if(ca[x].size()==2 && ca[y].size()==2) return 0;

		// Second one  based on literal block distance
		if(ca[x].lbd() > ca[y].lbd()) return 1;
		if(ca[x].lbd() < ca[y].lbd()) return 0;

		// Finally we can use old activity or size, we choose the last one
		return ca[x].act < ca[y].act;
	}
};

void removeConstraint(CRef cr){
	assert(decisionLevel()==0);
	Clause& c = ca[cr];
	assert(c.getStatus()!=MARKEDFORDELETE);
	assert(c.getStatus()!=LOCKED);
	c.setStatus(MARKEDFORDELETE);
	ca.wasted += ca.sz_clause(c.size());
}

void reduceDB(){
	cnt_reduceDB++;
	if (verbosity > 0) puts("c INPROCESSING");

	assert(decisionLevel()==0);
	size_t i, j;

	sort(learnts.begin(), learnts.end(), reduceDB_lt());
	if(ca[learnts[learnts.size() / 2]].lbd()<=3) nbclausesbeforereduce += 1000;
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Clause& c = ca[learnts[i]];
		if (c.getStatus()==FORCEDELETE){
			removeConstraint(learnts[i]);
		}else if (c.lbd()>2 && c.size() > 2 && c.getStatus()==UNLOCKED && i < learnts.size() / 2)
			removeConstraint(learnts[i]);
		else
			learnts[j++] = learnts[i];
	}
	learnts.erase(learnts.begin()+j,learnts.end());
	if ((double) ca.wasted / (double) ca.at > 0.2) garbage_collect();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
static double luby(double y, int x){

	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

	while (size-1 != x){
		size = (size-1)>>1;
		seq--;
		x = x % size;
	}

	return pow(y, seq);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

bool asynch_interrupt = false;
static void SIGINT_interrupt(int signum){
	asynch_interrupt = true;
}

static void SIGINT_exit(int signum){
	printf("\n"); printf("*** INTERRUPTED ***\n");
	exit(1);
}

void print_stats() {
	double timespent = cpuTime()-initial_time;
	printf("c CPU time			  : %g s\n", timespent);
	printf("c deterministic time %zu %.2e\n", DETERMINISTICTIME,(double)DETERMINISTICTIME);
	printf("d propagations %lld\n", NPROP);
	printf("d decisions %lld\n", NDECIDE);
	printf("d conflicts %lld\n", NCONFL);
	printf("d restarts %d\n", curr_restarts);
	printf("d inprocessing phases %d\n", cnt_reduceDB);
	printf("d clauses learned %lld\n", NCLAUSESLEARNED);
	printf("d cardinalities learned %lld\n", NCARDINALITIESLEARNED);
	printf("d general constraints learned %lld\n", NGENERALSLEARNED);
	printf("d average learned constraint length %.2f\n", NCONFL==0?0:(double)LEARNEDLENGTHSUM/NCONFL);
	printf("d average learned constraint degree %.2f\n", NCONFL==0?0:(double)LEARNEDDEGREESUM/NCONFL);
	printf("d gcd simplifications %lld\n", NGCD);
	printf("d detected cardinalities %lld\n", NCARDDETECT);
	printf("d weakened non-implied lits %lld\n", NWEAKENEDNONIMPLIED);
	printf("d weakened non-implying lits %lld\n", NWEAKENEDNONIMPLYING);
	printf("d auxiliary variables introduced %d\n", n-orig_n);
	if(opt_mode>0){
		printf("d cores constructed %lld\n", NCORES);
		printf("d core cardinality constraints returned %lld\n", NCORECARDINALITIES);
	}
}

long long lhs(Clause& C, const std::vector<bool>& sol){
	long long result = 0;
	for(size_t j=0; j<C.size(); ++j){
		int l = C.lits()[j];
		result+=((l>0)==sol[abs(l)])*C.coef(j);
	}
	return result;
}

bool checksol() {
	for(CRef cr: clauses){
		Clause& C = ca[cr];
		if(lhs(C,last_sol)<C.w) return false;
	}
	puts("c SATISFIABLE (checked)");
	return true;
}

void exit_SAT() {
	assert(checksol());
	print_stats();
	puts("s SATISFIABLE");
	//printf("v");for(int i=1;i<=orig_n;i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(10);
}

void exit_UNSAT() {
	print_stats();
	if(foundSolution()){
		cout << "o " << last_sol_obj_val << endl;
		cout << "s OPTIMUM FOUND" << endl;
		assert(checksol());
		//printf("v");for(int i=1;i<=orig_n;i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
		exit(30);
	}else{
		puts("s UNSATISFIABLE");
		exit(20);
	}
}

void exit_INDETERMINATE() {
	if(foundSolution()) exit_SAT();
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void exit_ERROR(const std::initializer_list<std::string>& messages){
	cout << "Error: ";
	for(const string& m: messages) cout << m;
	std::cout << std::endl;
	exit(1);
}

void usage(int argc, char**argv) {
	printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", argv[0]);
	printf("\n");
	printf("Options:\n");
	printf("  --help           Prints this help message\n");
	printf("  --verbosity=arg  Set the verbosity of the output (default %d).\n",verbosity);
	printf("\n");
	printf("  --var-decay=arg  Set the VSIDS decay factor (0.5<=arg<1; default %lf).\n",var_decay);
	printf("  --rinc=arg       Set the base of the Luby restart sequence (floating point number >=1; default %lf).\n",rinc);
	printf("  --rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %d).\n",rfirst);
	printf("  --original-rto=arg Set whether to use RoundingSat's original round-to-one conflict analysis (0 or 1; default %d).\n",originalRoundToOne);
	printf("  --opt-mode=arg   Set optimization mode: 0 linear, 1(2) (lazy) core-guided, 3(4) (lazy) hybrid (default %d).\n",opt_mode);
}

char * filename = 0;

typedef bool (*func)(double);
template <class T>
void getOption(const map<string, string>& opt_val, const string& option, func test, T& val){
	if (opt_val.count(option)) {
		double v = atof(opt_val.at(option).c_str());
		if (test(v)) val=v;
		else exit_ERROR({"Invalid value for ",option,": ",opt_val.at(option),".\nCheck usage with --help option."});
	}
}

void read_options(int argc, char**argv) {
	for(int i=1;i<argc;i++){
		if (!strcmp(argv[i], "--help")) {
			usage(argc, argv);
			exit(1);
		}
	}
	vector<string> opts = {"verbosity", "var-decay", "rinc", "rfirst", "original-rto", "opt-mode"};
	map<string, string> opt_val;
	for(int i=1;i<argc;i++){
		if (string(argv[i]).substr(0,2) != "--") filename = argv[i];
		else {
			bool found = false;
			for(string& key : opts) {
				if (string(argv[i]).substr(0,key.size()+3)=="--"+key+"=") {
					found = true;
					opt_val[key] = string(argv[i]).substr(key.size()+3);
				}
			}
			if (!found) exit_ERROR({"Unknown option: ",argv[i],".\nCheck usage with --help option."});
		}
	}
	getOption(opt_val,"verbosity",[](double x)->bool{return true;},verbosity);
	getOption(opt_val,"var-decay",[](double x)->bool{return x>=0.5 && x<1;},var_decay);
	getOption(opt_val,"rinc",[](double x)->bool{return x>=1;},rinc);
	getOption(opt_val,"rfirst",[](double x)->bool{return x>=1;},rfirst);
	getOption(opt_val,"original-rto",[](double x)->bool{return x==0 || x==1;},originalRoundToOne);
	getOption(opt_val,"opt-mode",[](double x)->bool{return x==0 || x==1 || x==2 || x==3 || x==4;},opt_mode);
}

template<class SMALL, class LARGE>
LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core){
	LARGE slack = -core.rhs;
	for(int v: core.vars) if(assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v]>0)) slack+=core.coefs[v];
	return slack;
}

void extractCore(CRef confl, Constraint<int,long long>* out, int l_assump=0){
	assert(out!=nullptr);
	Constraint<int,long long>& outCore = *out; outCore.reset();
	assert(confl!=CRef_Undef);

	if(l_assump!=0){ // l_assump is an assumption propagated to the opposite value
		assert(~Level[-l_assump]);
		while(~Level[-l_assump]) undoOne();
		assert(Pos[abs(l_assump)]==-1);
		decide(l_assump);
	}

	confl_data.init(ca[confl]);
	assert(confl_data.getSlack()<0);

	// Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
	// For this, we first copy the trail, then backjump to 0, then rebuild the trail.
	// Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
	tmpSet.reset(); // holds the assumptions
	std::vector<int> props; // holds the propagations
	assert(trail_lim.size()>0);
	for(int i=trail_lim[0]; i<(int)trail.size(); ++i){
		int l = trail[i];
		if(Reason[abs(l)]==CRef_Undef) tmpSet.add(l); // decision, hence assumption
		else props.push_back(l);
	}
	backjumpTo(0);

	for(int l: tmpSet.getKeys()) decide(l);
	for(int l: props) { assert(Reason[abs(l)]!=CRef_Undef); uncheckedEnqueue(l,Reason[abs(l)]); }

	// analyze conflict
	long long assumpslk = assumpSlack(tmpSet,confl_data);
	while(assumpslk>=0){
		int l = trail.back();
		int confl_coef_l = confl_data.getCoef(-l);
		if(confl_coef_l>0) {
			Clause& reasonC = ca[Reason[abs(l)]];
			tmpConstraint.init(reasonC);
			tmpConstraint.weakenNonImplying(tmpConstraint.getCoef(l),tmpConstraint.getSlack());
			tmpConstraint.roundToOne(tmpConstraint.getCoef(l),false);
			confl_data.add(tmpConstraint,confl_coef_l);
			assert(confl_data.getCoef(-l)==0);
			assumpslk = assumpSlack(tmpSet,confl_data);
		}
		undoOne();
		assert(decisionLevel()>=1);
	}
	confl_data.copyTo(outCore);

	// weaken non-falsifieds
	for(int v: outCore.vars){
		if(tmpSet.has(-outCore.getLit(v))) continue;
		outCore.weaken(-outCore.coefs[v],v);
	}
	outCore.postProcess();

	assert(assumpSlack(tmpSet,outCore)<0);
	backjumpTo(0);
}

bool solve(const vector<int>& assumptions, Constraint<int,long long>* out=nullptr) {
	backjumpTo(0); // ensures assumptions are reset
	std::vector<unsigned int> assumptions_lim={0};
	assumptions_lim.reserve(assumptions.size());
	while (true) {
		CRef confl = propagate();
		if (confl != CRef_Undef) {
			varDecayActivity();
			claDecayActivity();
			if (decisionLevel() == 0) exit_UNSAT();
			NCONFL++; nconfl_to_restart--;
			if(NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10lld | #Learnt: %10lld\n",NCONFL,(long long)learnts.size());
//					print_stats();
					if(verbosity>2){
						// memory usage
						cout<<"c total clause space: "<<ca.cap*4/1024./1024.<<"MB"<<endl;
						cout<<"c total #watches: ";{int cnt=0;for(int l=-n;l<=n;l++)cnt+=(int)adj[l].size();cout<<cnt<<endl;}
					}
				}
			}
			if(assumptions_lim.back()>=assumptions.size()){
				analyze(confl);
				learnConstraint(confl_data);
			}else{
				extractCore(confl,out);
				return false;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				backjumpTo(0);
				double rest_base = luby(rinc, curr_restarts++);
				nconfl_to_restart = (long long) rest_base * rfirst;
				if(NCONFL >= (cnt_reduceDB+1) * nbclausesbeforereduce) {
					reduceDB();
					nbclausesbeforereduce += incReduceDB;
				}
			}
			int next = 0;
			if(assumptions_lim.size()>(unsigned int) decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			while(assumptions_lim.back()<assumptions.size()){
				int l_assump = assumptions[assumptions_lim.back()];
				if (~Level[-l_assump]){ // found conflicting assumption
					if(Level[-l_assump]==0){ backjumpTo(0); out->reset(); return false; }
					extractCore(Reason[abs(l_assump)],out,l_assump);
					return false;
				}
				if (~Level[l_assump]){ // assumption already propagated
					++assumptions_lim.back();
				}else{ // unassigned assumption
					next = l_assump;
					assumptions_lim.push_back(assumptions_lim.back());
					break;
				}
			}
			if(next==0) next = pickBranchLit();
			if(next==0) {
				assert(order_heap.empty());
				for (int i = 1; i <= n; ++i)last_sol[i] = ~Level[i];
				backjumpTo(0);
				return true;
			}
			decide(next);
			++NDECIDE;
		}
	}
}

inline void printObjBounds(long long lower, long long upper){
	if(upper<INF) printf("o %10lld >= %10lld\n",upper,lower);
	else printf("o          - >= %10lld\n",lower);
}

void handleNewSolution(const Constraint<int,long long>& origObjective, long long lower_bound){
	int prev_val = last_sol_obj_val; _unused(prev_val);
	last_sol_obj_val = -origObjective.getRhs();
	for(int v: origObjective.vars) last_sol_obj_val+=origObjective.coefs[v]*last_sol[v];
	assert(last_sol_obj_val<prev_val);
	if(last_sol_obj_val==lower_bound) exit_UNSAT();

	origObjective.copyTo(tmpConstraint,-1);
	tmpConstraint.addRhs(-last_sol_obj_val+1);
	CRef cr = addInputConstraint(tmpConstraint);
	assert(cr!=CRef_Undef);
	if(external.size()>0){
		assert(external.size()==1);
		ca[external[0]].setStatus(FORCEDELETE);
		external.pop_back();
	}
	external.push_back(cr);
	assert(ca[cr].getStatus()==LOCKED);
}

struct LazyVar{
	int mult;
	int currentvar;
	int idx;
	int nvars;
	// core
	std::vector<int> lhs;
	int rhs;

	void init(const Constraint<int, long long>& core, int startvar, int m){
		assert(core.isCardinality());
		mult=m;
		rhs=core.getDegree();
		lhs.reserve(core.vars.size());
		for(int v: core.vars) lhs.push_back(core.getLit(v));
		currentvar=startvar;
		idx=0;
		nvars=lhs.size()-rhs;
	}

	void getAtLeastConstraint(Constraint<int, long long>& out){
		// X >= (k+i+1)yi
		out.reset();
		for(int l: lhs) out.addLhs(1,l);
		out.addLhs(-(rhs+idx+1),currentvar);
	}

	void getAtMostConstraint(Constraint<int, long long>& out){
		// ~X >= (n-k-i)~yi
		out.reset();
		for(int l: lhs) out.addLhs(1,-l);
		out.addLhs(-(lhs.size()-rhs-idx),-currentvar);
	}

	void getSymBreakingConstraint(Constraint<int, long long>& out, int prevvar){
		// yi>=yi++
		assert(idx>0);
		out.reset(1);
		out.addLhs(1,prevvar);
		out.addLhs(1,-currentvar);
	}
};

ostream & operator<<(ostream & o, LazyVar & lv) {
	o << lv.currentvar << " " << lv.idx << " " << lv.nvars << " | ";
	for(int l: lv.lhs) o << "+x" << l << " ";
	o << ">= " << lv.rhs;
	return o;
}

void handleInconsistency(Constraint<int,long long>& objective, Constraint<int,long long>& core, long long& lower_bound,
                         std::vector<LazyVar>& lazyVars){
	// take care of derived unit lits
	long long prev_lower = lower_bound; _unused(prev_lower);
	lower_bound = -objective.removeUnits(false);
	if(core.getDegree()==0){
		assert(lower_bound>prev_lower);
		return; // apparently only unit assumptions were derived
	}

	// figure out an appropriate core
	core.simplifyToCardinality(false);

	// adjust the lower bound
	long long degree = core.getDegree();
	if(degree>1) ++NCORECARDINALITIES;
	assert(degree<=1e9); assert(degree>0);
	int mult = INF;
	for(int v: core.vars){
		assert(objective.getLit(v)!=0);
		mult=min(mult,abs(objective.coefs[v]));
	}
	assert(mult<INF);
	lower_bound+=degree*mult;

	if((opt_mode==2 || opt_mode==4) && core.vars.size()-degree>1){
		// add auxiliary variable
		int newN = n+1;
		setNbVariables(newN);
		core.resize(newN+1);
		objective.resize(newN+1);
		// reformulate the objective
		core.copyTo(tmpConstraint,-1);
		tmpConstraint.addLhs(1,newN);
		objective.add(tmpConstraint,mult,false);
		objective.removeZeroes();
		assert(lower_bound==-objective.getDegree());
		// add first lazy constraint
		lazyVars.push_back(LazyVar());
		LazyVar& lv = lazyVars.back();
		lv.init(core,newN,mult);
		lv.getAtLeastConstraint(tmpConstraint);
		addInputConstraint(tmpConstraint);
		lv.getAtMostConstraint(tmpConstraint);
		addInputConstraint(tmpConstraint);
		// check for new lazy variables
		for(int i=0; i<(int)lazyVars.size(); ++i){
			LazyVar& lv=lazyVars[i];
			int currentvar = lv.currentvar;
			if(objective.getCoef(currentvar)==0){
				lv.idx++;
				if(lv.idx==lv.nvars){ swapErase(lazyVars,--i); break; }
				// add auxiliary variable
				int newN = n+1;
				setNbVariables(newN);
				core.resize(newN+1);
				objective.resize(newN+1);
				int oldvar = lv.currentvar;
				lv.currentvar = newN;
				// reformulate the objective
				objective.addLhs(lv.mult,newN);
				// add necessary lazy constraints
				lv.getAtLeastConstraint(tmpConstraint);
				addInputConstraint(tmpConstraint);
				lv.getAtMostConstraint(tmpConstraint);
				addInputConstraint(tmpConstraint);
				lv.getSymBreakingConstraint(tmpConstraint,oldvar);
				addInputConstraint(tmpConstraint);
			}
		}
	}else{
		// add auxiliary variables
		int oldN = n;
		int newN = oldN-degree+core.vars.size();
		setNbVariables(newN);
		core.resize(newN+1);
		objective.resize(newN+1);
		// reformulate the objective
		for(int v=oldN+1; v<=newN; ++v) core.addLhs(-1,v);
		core.copyTo(tmpConstraint,-1);
		objective.add(tmpConstraint,mult,false);
		objective.removeZeroes();
		assert(lower_bound==-objective.getDegree());
		// add channeling constraints
		addInputConstraint(tmpConstraint);
		core.copyTo(tmpConstraint);
		addInputConstraint(tmpConstraint);
		for(int v=oldN+1; v<newN; ++v){
			tmpConstraint.reset(1);
			tmpConstraint.addLhs(1,v);
			tmpConstraint.addLhs(1,-v-1);
			addInputConstraint(tmpConstraint);
		}
	}
}

void optimize(Constraint<int,long long>& objective){
	assert(objective.vars.size() > 0);
	// NOTE: -objective.getRhs() keeps track of the offset of the reformulated objective (or after removing unit lits)
	objective.removeZeroes();
	long long lower_bound = -objective.removeUnits(false);

	long long opt_coef_sum = 0;
	for (int v: objective.vars) opt_coef_sum+=abs(objective.coefs[v]);
	if (opt_coef_sum > (int) 1e9) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});

	Constraint<int,long long> origObjective;
	objective.copyTo(origObjective);

	std::vector<int> assumps;
	std::vector<LazyVar> lazyVars;
	assumps.reserve(objective.vars.size());
	Constraint<int,long long> core;
	size_t upper_time=0, lower_time=0;
	while(true){
		size_t current_time=DETERMINISTICTIME;
		printObjBounds(lower_bound,last_sol_obj_val);
		assumps.clear();
		if(opt_mode==1 || opt_mode==2 || (opt_mode>2 && lower_time<upper_time)){ // use core-guided step
			for(int v: objective.vars) assumps.push_back(-objective.getLit(v));
			std::sort(assumps.begin(),assumps.end(),[&](int l1,int l2){
				return objective.getCoef(-l1)>objective.getCoef(-l2) ||
				       (objective.getCoef(-l1)==objective.getCoef(-l2) && abs(l1)<abs(l2));
			});
		}
		if(solve(assumps,&core)){
			upper_time+=DETERMINISTICTIME-current_time;
			handleNewSolution(origObjective,lower_bound);
		}	else {
			assert(decisionLevel()==0);
			lower_time+=DETERMINISTICTIME-current_time;
			++NCORES;
			if(assumps.size()==0) exit_UNSAT();
			handleInconsistency(objective,core,lower_bound,lazyVars);
		}
	}
}

int main(int argc, char**argv){
	read_options(argc, argv);
	initial_time = cpuTime();
	init();
	signal(SIGINT, SIGINT_exit);
	signal(SIGTERM,SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);
	if (filename != 0) {
		ifstream fin (filename);
		if (!fin)  exit_ERROR({"Could not open ",filename});
		file_read(fin);
	} else {
		if (verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
		file_read(cin);
	}
	signal(SIGINT, SIGINT_interrupt);
	signal(SIGTERM,SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);

	std::cout << "c #variables=" << orig_n << " #constraints=" << clauses.size() << std::endl;

	if(objective_func.vars.size() > 0){
		optimize(objective_func);
	}else{
		// TODO: fix empty objective function
		if(solve({})) exit_SAT();
		else exit_UNSAT();
	}
}
