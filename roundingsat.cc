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
#include <set>

#define _unused(x) ((void)(x)) // marks variables unused in release mode

std::ostream& operator<<(std::ostream& os, __int128 t) { return os << (double) t; }

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE(),exit_OPT(),exit_ERROR(const std::initializer_list<std::string>&);

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

struct Clause {
	struct {
		unsigned markedfordel : 1;
		unsigned learnt       : 1;
		unsigned size         : 30; } header;
	// watch data
	int nwatch;
	long long sumwatchcoefs;
	long long minsumwatch;
	// ordinary data
	int w;
	float act;
	int lbd;
	int data[0];

	size_t size() const { return header.size; }
	
	int * lits() { return data; }
	int * coefs() { return (int*)(data+header.size); }
	
	bool learnt() const { return header.learnt; }
	bool markedfordel() const { return header.markedfordel; }
	void markfordel() { header.markedfordel=1; }
};
struct lit{int l;lit(int l):l(l){}};
ostream&operator<<(ostream&o,lit const&l){if(l.l<0)o<<"~";o<<"x"<<abs(l.l);return o;}
ostream & operator<<(ostream & o, Clause & C) {
	vector<int> order;
	for (int i = 0; i < (int) C.size(); i++) order.push_back(i);
	sort(order.begin(), order.end(), [&C](int i, int j) { return abs(C.lits()[i]) < abs(C.lits()[j]); });
	for (int i = 0; i < (int) C.size(); i++) {
		int l = C.lits()[order[i]];
		int coef = C.coefs()[order[i]];
		o << coef << " " << lit(l) << " ";
	}
	o << ">= " << C.w << ";";
	return o;
}

// ---------------------------------------------------------------------
// memory. maximum supported size of learnt clause database is 16GB
struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };

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
	uint32_t at, cap;
	uint32_t wasted; // for GC
	void capacity(uint32_t min_cap)
	{
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
	CRef alloc(vector<int> lits, vector<int> coefs, int w, bool learnt){
		assert(!lits.empty());
		int length = (int) lits.size();
		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		capacity(at + sz_clause(length));
		Clause * clause = (Clause*)(memory+at);
		new (clause) Clause;
		at += sz_clause(length);
		clause->header = {0, learnt, (unsigned)length};
		clause->w = w;
		clause->act = 0;
		for(int i=0;i<length;i++)clause->lits()[i]=lits[i];
		for(int i=0;i<length;i++)clause->coefs()[i]=coefs[i];
		return {(uint32_t)(at-sz_clause(length))};
	}
	Clause& operator[](CRef cr) { return (Clause&)*(memory+cr.ofs); }
	const Clause& operator[](CRef cr) const { return (Clause&)*(memory+cr.ofs); }
} ca;
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
int verbosity = 1;
// currently, the maximum number of variables is hardcoded (variable N), and most arrays are of fixed size.
int n = 0;
int orig_n = 0;
int opt_K = 0;
int opt_normalize_add = 0, opt_coef_sum = 0;
vector<CRef> clauses, learnts;
CRef objective=CRef_Undef;
bool optimizing(){ return objective!=CRef_Undef; }
struct Watch {
	CRef cref;
};
const double resize_factor=1.5;

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
	int oldmiddle = (_map.size()-1)/2;
	int newmiddle = resize_factor*size;
	assert(newmiddle>oldmiddle);
	_map.resize(2*newmiddle+1);
	map=_map.begin()+newmiddle;
	for(int i=_map.size()-1; i>newmiddle+oldmiddle; --i) _map[i]=init;
	for(int i=newmiddle+oldmiddle; i>=newmiddle-oldmiddle; --i) _map[i]=_map[i-newmiddle+oldmiddle];
	for(int i=newmiddle-oldmiddle-1; i>=0; --i) _map[i]=init;
}

vector<vector<Watch>> _adj; vector<vector<Watch>>::iterator adj;
vector<CRef> _Reason; vector<CRef>::iterator Reason;
vector<int> trail;
vector<int> _Level; vector<int>::iterator Level;
vector<int> trail_lim;
int qhead; // for unit propagation
vector<int> phase;
void newDecisionLevel() { trail_lim.push_back(trail.size()); }
int decisionLevel() { return trail_lim.size(); }

template<class SMALL, class LARGE> // LARGE should be able to fit sums of SMALL
struct Constraint{
	std::vector<int> vars;
	vector<SMALL> coefs;
	LARGE rhs = 0;
	SMALL _unused_ = std::numeric_limits<SMALL>::min();

	inline void resize(int s){
		coefs.resize(s,_unused_);
	}

	void reset(){
		for(int v: vars) coefs[v]=_unused_;
		vars.clear();
		rhs=0;
	}

	// TODO: simplify C: remove level 0's, saturate, gcd, weaken non-implying...
	void init(Clause& C){
		reset();
		//for(int i=0; i<C.size(); ++i) {
		//	int l = C.lits()[i];
		//	int c = C.coefs()[i];
		//	if (Level[l] == 0) { w -= c; }
		//	if(w<=0) return;
		//}
		for(size_t i=0;i<C.size();++i){
			addLhs(C.coefs()[i], C.lits()[i]);
		}
		addRhs(C.w);
		saturate();
	}

	void addLhs(SMALL c, int l){ // treat negative literals as 1-v
		assert(l!=0);
		if(c==0) return;
		int v = l;
		if(l<0){
			rhs -= c;
			c = -c;
			v = -l;
		}
		assert(v<(int)coefs.size());
		if(coefs[v]==_unused_) vars.push_back(v), coefs[v]=0;
		coefs[v]+=c;
	}

	inline void addRhs(SMALL r){ rhs+=r; }
	inline LARGE getRhs(){ return rhs; }
	inline LARGE getDegree() {
		LARGE result = rhs;
		for (int v: vars) result -= min<SMALL>(0,coefs[v]); // considering negative coefficients
		return result;
	}
	inline SMALL getCoef(int l) { return l<0?-coefs[-l]:coefs[l]; }
	inline int getLit(int l){
		int v = abs(l);
		if(coefs[v]==0 || coefs[v]==_unused_) return 0;
		if(coefs[v]<0) return -v;
		else return v;
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

	void getNormalForm(std::vector<int>& lits, std::vector<SMALL>& cs, LARGE& w){
		lits.clear(); cs.clear();
		w=getDegree();
		if(w<=0) return;
		lits.reserve(vars.size()); cs.reserve(vars.size());
		for(int v: vars){
			int l = getLit(v);
			lits.push_back(l);
			cs.push_back(min<LARGE>(getCoef(l),w));
		}
	}

	void invert(){
		for(int v: vars) coefs[v]=-coefs[v];
		rhs=-rhs;
	}

	void divide(SMALL d){
		for (int v: vars) coefs[v] = ceildiv_safe<SMALL>(coefs[v],d);
		rhs=ceildiv_safe<LARGE>(rhs,d);
	}

	LARGE getSlack(){
		LARGE slack = -rhs;
		for(int v: vars) if(Level[v]!=-1 || (Level[-v]==-1 && coefs[v]>0)) slack+=coefs[v];
		return slack;
	}

	template<class S, class L>
	void add(const Constraint<S,L>& c, SMALL mult=1){
		assert(mult>0);
		for(int v: c.vars){
			addLhs(mult*c.coefs[v],v);
		}
		addRhs(mult*c.rhs);

		LARGE deg = saturate();
		if (deg > (int) 1e9) {
			// round to cardinality.
			long long d = 0;
			for(int x:vars)d=max(d, abs(coefs[x]));
			roundToOne(d);
		}
	}

	void roundToOne(SMALL d){
		assert(d>0);
		for(int v:vars){
			//assert(Level[-v]!=0);
			//assert(Level[ v]!=0);
			if((coefs[v]%d)==0){ coefs[v]/=d; continue; }
			if((Level[v]==-1 && Level[-v]==-1) || (Level[v]!=-1)==(coefs[v]>0)){
				weaken(-coefs[v],v);
				// weaken(-coefs[v]%d,v); // partial weakening
			}else{
				assert((Level[v]==-1)==(coefs[v]>0));
				if(coefs[v]<0) weaken(-d-(coefs[v]%d),v);
				else weaken(d-(coefs[v]%d),v);
			}
			assert(coefs[v]%d==0);
			coefs[v]/=d;
		}
		rhs=ceildiv_safe<LARGE>(rhs,d);
		saturate();
	}

	bool simplify(){
		return false; // TODO
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
};
template<class S, class L>
ostream & operator<<(ostream & o, Constraint<S,L>& C) {
	sort(C.vars.begin(),C.vars.end(), [](S v1, S v2) { return v1<v2; });
	for(int v: C.vars){
		int l = C.getLit(v);
		if(l==0) continue;
		o << C.getCoef(l) << "x" << l << ":" << (Level[l]>0?"t":(Level[-l]>0?"f":"u")) << "@" << max(Level[l],Level[-l]) << " ";
	}
	o << ">= " << C.getDegree();
	return o;
}

Constraint<int, long long> tmpConstraint;

double initial_time;
int NCONFL=0, NDECIDE=0;
long long NPROP=0, NIMPL=0;
__int128 LEARNEDLENGTHSUM=0, LEARNEDDEGREESUM=0;
long long NCLAUSESLEARNED=0, NCARDINALITIESLEARNED=0, NGENERALSLEARNED=0;
double rinc = 2;
int rfirst = 100;
int nbclausesbeforereduce=2000;
int incReduceDB=300;
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
		cap = resize_factor*newsize;
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

template<class A,class B> long long slack(int length,A const& lits,B const& coefs,long long w){
	long long s=-w;
	for(int i=0;i<length;i++){
		int l = lits[i];
		int coef = coefs[i];
		if(Level[-l]==-1)s+=coef;
	}
	return s;
}

long long slack(Clause & C){ return slack(C.size(),C.lits(),C.coefs(),C.w); }

void attachClause(CRef cr){
	Clause & C = ca[cr];
	// sort literals by the decision level at which they were falsified, descending order (never falsified = level infinity)
	vector<pair<int,int>> order;
	for(int i=0;i<(int)C.size();i++){
		int lvl=Level[-C.lits()[i]]; if(lvl==-1)lvl=1e9;
		order.emplace_back(-lvl,i);
	}
	sort(order.begin(),order.end());
	vector<int>lits_old (C.lits(), C.lits()+C.size());
	vector<int>coefs_old (C.coefs(), C.coefs()+C.size());
	for(int i=0;i<(int)C.size();i++){
		C.lits()[i] = lits_old[order[i].second];
		C.coefs()[i] = coefs_old[order[i].second];
	}
	C.sumwatchcoefs = 0;
	C.nwatch = 0;
	int mxcoef = 0; for(int i=0;i<(int)C.size();i++) if (abs(C.lits()[i]) <= n - opt_K) mxcoef = max(mxcoef, C.coefs()[i]);
	C.minsumwatch = (long long) C.w + mxcoef;
	for(int i=0;i<(int)C.size();i++) {
		C.sumwatchcoefs += C.coefs()[i];
		C.nwatch++;
		adj[C.lits()[i]].push_back({cr});
		if (C.sumwatchcoefs >= C.minsumwatch) break;
	}
}

bool locked(CRef cr){
	if(objective==cr) return true;
	Clause & c = ca[cr];
	for(size_t idx=0;idx<c.size();idx++){
		if(Reason[c.lits()[idx]] == cr) return true;
	}
	return false;
}

void removeClause(CRef cr){
	Clause& c = ca[cr];
	assert(!c.markedfordel());
	assert(!locked(cr));
	c.markfordel();
	ca.wasted += ca.sz_clause(c.size());
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
void uncheckedEnqueue(int p, CRef from){
	assert(Level[p]==-1 && Level[-p]==-1);
	Level[p] = -2;
	Reason[p] = from;
	trail.push_back(p);
}

void undoOne(){
	assert(!trail.empty());
	int l = trail.back();
	trail.pop_back();
	Level[l] = -1;
	phase[abs(l)]=l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	Reason[l] = CRef_Undef;
	order_heap.insert(abs(l));
}

void backjumpTo(int level){
	while(decisionLevel()>level) undoOne();
	qhead = trail.size();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
/**
 * In the conflict analysis we represent the learnt clause
 * by an array of length 2*N, with one position per literal.
 * 
 * After each analyze() we want to reset this array.
 * Because this is expensive we keep track of which literals participate
 * in the analysis and reset only their coefficients.
 */
struct ConflictData {
	long long slack;
	int cnt_falsified_currentlvl;
	// here we use int64 because we could get overflow in the following case:
	// the reason's coefs multiplied by the coef. of the intermediate conflict clause
	vector<long long> _M; vector<long long>::iterator M;
	long long w;
	vector<int> used; // 1: used, 2: clashing in some step
	vector<int> usedlist;
	void resize(int size){
		resizeLitMap(_M,M,size,(long long)0);
		used.resize(size+1,0);
	}
	void reset(){
		slack=0;
		cnt_falsified_currentlvl=0;
		w=0;
		for(int x:usedlist)M[x]=M[-x]=0,used[x]=0;
		usedlist.clear();
	}
	void use(int x){
		if(!used[x])used[x]=max(used[x],1),usedlist.push_back(x);
	}
} confl_data;

void round_reason(int l0, vector<int>&out_lits,vector<int>&out_coefs,int&out_w) {
	Clause & C = ca[Reason[l0]];
	int old_coef_l0 = C.coefs()[find(C.lits(),C.lits()+C.size(),l0)-C.lits()];
	int w = C.w;
	for(size_t i=0;i<C.size();i++){
		int l = C.lits()[i];
		int coef = C.coefs()[i];
		if (Level[-l] == -1) {
			if (coef % old_coef_l0 != 0) w -= coef;
			else out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);
			
			// partial weakening would instead do:
			/*w -= coef % old_coef_l0;
			if (coef >= old_coef_l0) out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);*/
		} else {
			out_lits.push_back(l), out_coefs.push_back(ceildiv(coef, old_coef_l0));
		}
	}
	out_w = ceildiv<long long>(w, old_coef_l0);
	assert(slack(out_lits.size(), out_lits, out_coefs, out_w) == 0);
}

void round_conflict(long long c) {
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		if (Level[-l] == -1) {
			if (confl_data.M[l] % c != 0) {
				confl_data.w -= confl_data.M[l], confl_data.M[l] = 0;
			} else confl_data.M[l] /= c;
			
			// partial weakening would instead do:
			/*confl_data.w -= confl_data.M[l] % c;
			confl_data.M[l] /= c;*/
		} else confl_data.M[l] = ceildiv(confl_data.M[l], c);
	}
	confl_data.w = ceildiv(confl_data.w, c);
	confl_data.slack = -ceildiv(-confl_data.slack, c);
}

template<class It1, class It2> void add_to_conflict(size_t size, It1 const&reason_lits,It2 const&reason_coefs,int reason_w){
	vector<long long>::iterator M = confl_data.M;
	long long & w = confl_data.w;
	w += reason_w;
	bool overflow = false;
	for(size_t it=0;it<size;it++){
		int l = reason_lits[it];
		int c = reason_coefs[it];
		assert(c>0);
		confl_data.use(abs(l));
		if (M[-l] > 0) {
			confl_data.used[abs(l)] = 2;
			if (c >= M[-l]) {
				if (Level[l] == decisionLevel()) confl_data.cnt_falsified_currentlvl--;
				M[l] = c - M[-l];
				w -= M[-l];
				M[-l] = 0;
				if (Level[-l] == decisionLevel() && M[l] > 0) confl_data.cnt_falsified_currentlvl++;
			} else {
				M[-l] -= c;
				w -= c;
			}
		} else {
			if (Level[-l] == decisionLevel() && M[l] == 0) confl_data.cnt_falsified_currentlvl++;
			M[l] += c;
		}
		if (M[l] > (int) 1e9) overflow = true;
	}
	if (w > (int) 1e9 || overflow) {
		// round to cardinality.
		long long d = 0;
		for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)d=max(d, confl_data.M[l]);
		round_conflict(d);
	}
}

int computeLBD(CRef cr) {
	Clause & C = ca[cr];
	set<int> levels;
	int * lits = C.lits();
	for (int i=0; i<(int)C.size(); i++) if (Level[-lits[i]] != -1) levels.insert(Level[-lits[i]]);
	return (int) levels.size();
}

void analyze(CRef confl, vector<int>& out_lits, vector<int>& out_coefs, int& out_w){
	Clause & C = ca[confl];
	if (C.learnt()) {
		claBumpActivity(C);
		if (C.lbd > 2) C.lbd = min(C.lbd, computeLBD(confl));
	}
	confl_data.reset();
	add_to_conflict(C.size(), C.lits(), C.coefs(), C.w);
	confl_data.slack = slack(C);
	vector<int> reason_lits; reason_lits.reserve(n);
	vector<int> reason_coefs; reason_coefs.reserve(n);
	int reason_w;
	while(1){
		if (decisionLevel() == 0) {
			exit_UNSAT();
		}
		int l = trail.back();
		if(confl_data.M[-l]) {
			confl_data.M[-l] = min(confl_data.M[-l], confl_data.w); // so that we don't round the conflict if w=1.
			if (confl_data.M[-l] > 1) {
				round_conflict(confl_data.M[-l]);
			}
			if (confl_data.cnt_falsified_currentlvl == 1) {
				break;
			} else {
				assert(Reason[l] != CRef_Undef);
				if (ca[Reason[l]].learnt()) {
					claBumpActivity(ca[Reason[l]]);
					if (ca[Reason[l]].lbd > 2) ca[Reason[l]].lbd = min(ca[Reason[l]].lbd, computeLBD(Reason[l]));
				}
				reason_lits.clear();
				reason_coefs.clear();
				round_reason(l, reason_lits, reason_coefs, reason_w);
				add_to_conflict(reason_lits.size(), reason_lits, reason_coefs, reason_w);
			}
		}
		int oldlvl=decisionLevel();
		undoOne();
		if(decisionLevel()<oldlvl){
			assert(confl_data.cnt_falsified_currentlvl == 0);
			for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]) {
				if (Level[-l] == decisionLevel()) confl_data.cnt_falsified_currentlvl++;
			}
		}
	}
	for(int x:confl_data.usedlist){
		varBumpActivity(x);
		if (confl_data.used[x] == 2) varBumpActivity(x);
	}
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		out_lits.push_back(l),out_coefs.push_back(min(confl_data.M[l],confl_data.w));
	}
	out_w=confl_data.w;
}

/**
 * Unit propagation with watched literals.
 * 
 * post condition: the propagation queue is empty (even if there was a conflict).
 */
CRef propagate() {
	CRef confl = CRef_Undef;
	while(qhead<(int)trail.size()){
		int p=trail[qhead++];
		Level[p] = decisionLevel();
		vector<Watch> & ws = adj[-p];
		vector<Watch>::iterator i, j, end;
		for(i = j = ws.begin(), end = ws.end(); i != end;){
			CRef cr = i->cref;
			i++;
			Clause & C = ca[cr];
			if(C.header.markedfordel)continue;
			int * lits = C.lits();
			int * coefs = C.coefs();
			bool watchlocked = false;
			for (int i=0; i<C.nwatch; i++) if (Level[-lits[i]] >= 0 && lits[i] != -p) watchlocked = true;
			if (!watchlocked) {
				int pos = 0; while (lits[pos] != -p) pos++;
				int c = coefs[pos];
				for(int it=C.nwatch;it<(int)C.size() && C.sumwatchcoefs-c < C.minsumwatch;it++)if(Level[-lits[it]]==-1){
					adj[lits[it]].push_back({cr});
					swap(lits[it],lits[C.nwatch]),swap(coefs[it],coefs[C.nwatch]);
					C.sumwatchcoefs += coefs[C.nwatch];
					C.nwatch++;
				}
				if (C.sumwatchcoefs-c >= C.minsumwatch) {
					swap(lits[pos],lits[C.nwatch-1]),swap(coefs[pos],coefs[C.nwatch-1]);
					C.sumwatchcoefs-=coefs[C.nwatch-1];
					C.nwatch--;
					continue;
				}
			}
			*j++ = {cr};
			long long s = slack(C.nwatch,lits,coefs,C.w);
			if(s<0){
				confl = cr;
				while (qhead < (int) trail.size()) Level[trail[qhead++]] = decisionLevel();
				while(i<end)*j++=*i++;
			}else{
				for(int it=0;it<C.nwatch;it++)if(Level[-lits[it]]==-1 && coefs[it] > s){
					NIMPL++;
					if (Level[lits[it]]==-1) {
						uncheckedEnqueue(lits[it], cr);
						NPROP++;
					}
				}
			}
		}
		ws.erase(j, end);
	}
	return confl;
}

int pickBranchLit(){
	int next = 0;

	// Activity based decision:
	while (next == 0 || Level[next] != -1 || Level[-next] != -1)
		if (order_heap.empty()){
			next = 0;
			break;
		}else
			next = order_heap.removeMax();

	return next == 0 ? 0 : phase[next];
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
	resizeLitMap(_Reason,Reason,nvars,CRef_Undef);
	resizeLitMap(_Level,Level,nvars,-1);
	activity.resize(nvars+1,0);
	phase.resize(nvars+1);
	tmpConstraint.resize(nvars+1);
	confl_data.resize(nvars+1);
	order_heap.resize(nvars);
	for(int i=n+1;i<=nvars;++i) phase[i] = -i, order_heap.insert(i);
	n = nvars;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Proto-constraint handling
void reduce_by_toplevel(vector<int>& lits, vector<int>& coefs, int& w){
	size_t i,j;
	for(i=j=0; i<lits.size(); i++){
		if(Level[ lits[i]]==0) w-=coefs[i]; else
		if(Level[-lits[i]]==0); else {
			lits[j]=lits[i];
			coefs[j]=coefs[i];
			j++;
		}
	}
	lits.erase(lits.begin()+j,lits.end());
	coefs.erase(coefs.begin()+j,coefs.end());
}

inline void saturate(vector<int>& coefs, int& w){
	for (int i = 0; i < (int) coefs.size(); i++) coefs[i] = min(coefs[i], w);
}

bool simplify_constraint(vector<int> &lits, vector<int> &coefs, int &w){
	reduce_by_toplevel(lits,coefs,w);
	if(w<=0) return true; // trivially satisfied constraint
	saturate(coefs,w); // as reduce_by_toplevel could have reduced w
	return false;
}

CRef learnConstraint(vector<int>& lits,vector<int>& coefs, int w){
	assert(lits.size()>0);
	CRef cr = ca.alloc(lits,coefs,w, true);
	Clause & C = ca[cr];
	C.lbd = computeLBD(cr);
	attachClause(cr);
	learnts.push_back(cr);
	LEARNEDLENGTHSUM+=lits.size();
	LEARNEDDEGREESUM+=w;
	if(w==1) ++NCLAUSESLEARNED;
	else{
		int c=coefs[0];
		bool isCardinality = true;
		for(int i=1; i<(int) coefs.size() && isCardinality; ++i) isCardinality=(coefs[i]==c);
		if(isCardinality) ++NCARDINALITIESLEARNED;
		else ++NGENERALSLEARNED;
	}
	return cr;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Parsers
void addConstraint(Constraint<int, long long>& c){
	assert(learnts.size()==0);
	std::vector<int> lits; std::vector<int> coefs; long long d=0; int w;
	c.getNormalForm(lits,coefs,d);
	if (abs(d) > (long long) 1e9) exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
	w=(int)d;
	bool trivial = simplify_constraint(lits,coefs,w);
	if(trivial) return; // already satisfied.
	long long som = 0;for(int c:coefs)som+=c;
	if(som < w)puts("c UNSAT trivially inconsistent constraint"),exit_UNSAT();
	for(size_t i=0;i<lits.size();i++)if(som-coefs[i] < w){
		//printf("propagate %d\n",lits[i]);
		uncheckedEnqueue(lits[i],CRef_Undef);
	}
	if(trivial) return; // already satisfied.
	CRef cr = ca.alloc(lits, coefs, w, false);
	attachClause(cr);
	clauses.push_back(cr);
	if (propagate() != CRef_Undef)puts("c UNSAT initial conflict"),exit_UNSAT();
}

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

// NOTE: must be called after adding the original constraints, as we implement the objective as a learnt constraint
void addObjective(Constraint<int, long long>& c) {
	std::vector<int> lits; std::vector<int> coefs;
	for(int v: c.vars) if(c.coefs[v]!=0) {
		lits.push_back(v);
		coefs.push_back(c.coefs[v]);
	}
	opt_coef_sum = 0;
	opt_normalize_add = 0;
	for(size_t i=0;i<lits.size();i++){
		if(coefs[i] < 0) lits[i]*=-1,coefs[i]*=-1,opt_normalize_add+=coefs[i];
		opt_coef_sum+=coefs[i];
		lits[i]=-lits[i];
		if (opt_coef_sum > (int) 1e9) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});
	}
	opt_K = 0; while ((1<<opt_K) <= opt_coef_sum) opt_K++;
	for(int i=0;i<opt_K;i++)lits.push_back(n+1+i),coefs.push_back(1<<i);
	setNbVariables(n+opt_K);

	if(lits.size()==0) {
		// Add dummy objective that evaluates to 0
		objective = ca.alloc({0, 0}, {0, 0}, 0, true);
	}else{
		objective = ca.alloc(lits, coefs, opt_coef_sum, true);
	}
	Clause& C = ca[objective];
	C.lbd = lits.size();
	attachClause(objective);
	learnts.push_back(objective);
}

void opb_read(istream & in) {
	Constraint<int,long long> objective_func;
	bool opt = false;
	bool first_constraint = true;
	_unused(first_constraint);
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
			if (opt_line) opt=true, objective_func=tmpConstraint;
			else {
				tmpConstraint.addRhs(read_number(line0.substr(line0.find("=") + 1)));
				addConstraint(tmpConstraint);
				// Handle equality case with two constraints
				if (line0.find(" = ") != string::npos) {
					tmpConstraint.invert();
					addConstraint(tmpConstraint);
				}
			}
		}
	}
	orig_n=n;
	if(opt) addObjective(objective_func);
}

void wcnf_read(istream & in, long long top) {
	std::vector<int> weights;
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			long long weight; is >> weight;
			if(weight==0) continue;
			tmpConstraint.reset();
			tmpConstraint.addRhs(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			if(weight<top){ // soft clause
				if(weight>1e9) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
				if(weight<0) exit_ERROR({"Negative clause weight: ",std::to_string(weight)});
				weights.push_back(weight);
				setNbVariables(n+1); // increases n to n+1
				tmpConstraint.addLhs(1,n);
			} // else hard clause
			addConstraint(tmpConstraint);
		}
	}
	orig_n = n-weights.size();
	tmpConstraint.reset();
	for(int i=0; i<(int) weights.size(); ++i) tmpConstraint.addLhs(weights[i],orig_n+1+i);
	addObjective(tmpConstraint);
}

void cnf_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			tmpConstraint.reset();
			tmpConstraint.addRhs(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			addConstraint(tmpConstraint);
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
	if (verbosity > 0) puts("c GARBAGE COLLECT");
	for(int l=-n; l<=n; l++) {
		size_t i, j;
		for(i=0,j=0;i<adj[l].size();i++){
			CRef cr = adj[l][i].cref;
			if(!ca[cr].markedfordel())adj[l][j++]=adj[l][i];
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
	for(int l=-n;l<=n;l++) if(Reason[l]!=CRef_Undef) update_ptr(Reason[l]);
	if(optimizing()) update_ptr(objective);
	#undef update_ptr
}

struct reduceDB_lt {
    bool operator () (CRef x, CRef y) { 
 
    // Main criteria... Like in MiniSat we keep all binary clauses
    if(ca[x].size()> 2 && ca[y].size()==2) return 1;
    
    if(ca[y].size()>2 && ca[x].size()==2) return 0;
    if(ca[x].size()==2 && ca[y].size()==2) return 0;
    
    // Second one  based on literal block distance
    if(ca[x].lbd> ca[y].lbd) return 1;
    if(ca[x].lbd< ca[y].lbd) return 0;    
    
    
    // Finally we can use old activity or size, we choose the last one
        return ca[x].act < ca[y].act;
	//return x->size() < y->size();

        //return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
    }    
};
void reduceDB(){
	size_t i, j;

	sort(learnts.begin(), learnts.end(), reduceDB_lt());
	if(ca[learnts[learnts.size() / 2]].lbd<=3) nbclausesbeforereduce += 1000;
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Clause& c = ca[learnts[i]];
		if (c.lbd>2 && c.size() > 2 && !locked(learnts[i]) && i < learnts.size() / 2)
			removeClause(learnts[i]);
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
	printf("c CPU time			  : %g s\n", cpuTime()-initial_time);
	printf("d decisions %d\n", NDECIDE);
	printf("d conflicts %d\n", NCONFL);
	printf("d propagations %lld\n", NPROP);
	printf("d average learned constraint length %.2f\n", NCONFL==0?0:(double)LEARNEDLENGTHSUM/NCONFL);
	printf("d average learned constraint degree %.2f\n", NCONFL==0?0:(double)LEARNEDDEGREESUM/NCONFL);
	printf("d clauses learned %lld\n", NCLAUSESLEARNED);
	printf("d cardinalities learned %lld\n", NCARDINALITIESLEARNED);
	printf("d general constraints learned %lld\n", NGENERALSLEARNED);
}

int last_sol_value;
vector<bool> last_sol;

bool checksol() {
	for(CRef cr: clauses){
		Clause& C = ca[cr];
		long long slack=-C.w;
		for(size_t j=0; j<C.size(); ++j){
			int l = C.lits()[j];
			slack+=((l>0)==last_sol[abs(l)])*C.coefs()[j];
		}
		if(slack<0) return false;
	}
	puts("c SATISFIABLE (checked)");
	return true;
}

void exit_SAT() {
	assert(checksol());
	print_stats();
	puts("s SATISFIABLE");
	printf("v");for(int i=1;i<=orig_n;i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(10);
}

void exit_UNSAT() {
	if(!last_sol.empty()) exit_OPT();
	print_stats();
	puts("s UNSATISFIABLE");
	exit(20);
}

void exit_INDETERMINATE() {
	if (!last_sol.empty()) exit_SAT();
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void exit_OPT() {
	assert(checksol());
	print_stats();
	cout << "s OPTIMUM FOUND" << endl;
	cout << "c objective function value " << last_sol_value << endl;
	printf("v");for(int i=1;i<=orig_n;i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(30);
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
	vector<string> opts = {"verbosity", "var-decay", "rinc", "rfirst"};
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
}

int curr_restarts=0;
long long nconfl_to_restart=0;
//reduceDB:
int cnt_reduceDB=1;

bool solve(vector<int> assumptions) {
	backjumpTo(0); // ensures assumptions are reset
	std::vector<unsigned int> assumptions_lim={0};
	assumptions_lim.reserve(assumptions.size());
	while (true) {
		CRef confl = propagate();
		if (confl != CRef_Undef) {
			have_confl:
			varDecayActivity();
			claDecayActivity();
			if (decisionLevel() == 0) {
				exit_UNSAT();
			}
			NCONFL++; nconfl_to_restart--;
			if(NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10d | #Learnt: %10d\n",NCONFL,(int)learnts.size());
					if(verbosity>2){
						// memory usage
						cout<<"c total clause space: "<<ca.cap*4/1024./1024.<<"MB"<<endl;
						cout<<"c total #watches: ";{int cnt=0;for(int l=-n;l<=n;l++)cnt+=(int)adj[l].size();cout<<cnt<<endl;}
						printf("c total #propagations: %lld / total #impl: %lld (eff. %.3lf)\n",NPROP,NIMPL,(double)NPROP/(double)NIMPL);
					}
				}
			}
			vector<int>lits;vector<int>coefs;int w;
			analyze(confl, lits, coefs, w);
			bool trivial = simplify_constraint(lits,coefs,w);
			_unused(trivial);
			assert(!trivial);
			// compute an assertion level
			// it may be possible to backjump further, but we don't do this
			int lvl = 0;
			for (int i=0; i<(int)lits.size(); i++)
				if (Level[-lits[i]] < decisionLevel())
					lvl = max(lvl, Level[-lits[i]]);
			assert(lvl < decisionLevel());
			backjumpTo(lvl);
			CRef cr = learnConstraint(lits,coefs,w);

			if (::slack(ca[cr]) == 0) {
				for (int i=0; i<(int)lits.size(); i++)
					if (Level[-lits[i]] == -1 && Level[lits[i]] == -1)
						uncheckedEnqueue(lits[i], cr);
			} else {
				// the learnt constraint is conflicting at the assertion level.
				// in this case, immediately enter a new conflict analysis again.
				confl = cr;
				goto have_confl;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				backjumpTo(0);
				double rest_base = luby(rinc, curr_restarts++);
				nconfl_to_restart = (long long) rest_base * rfirst;
			}
			//if ((int)learnts.size()-(int)trail.size() >= max_learnts)
			if(NCONFL >= cnt_reduceDB * nbclausesbeforereduce) {
				reduceDB();
				cnt_reduceDB++;
				nbclausesbeforereduce += incReduceDB;
			}
			int next = 0;
			if(assumptions_lim.size()>(unsigned int) decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			while(assumptions_lim.back()<assumptions.size()){
				int l = assumptions[assumptions_lim.back()];
				if (~Level[-l]) return false;
				if (~Level[l]){
					++assumptions_lim.back();
				}else{
					next = l;
					assumptions_lim.push_back(assumptions_lim.back());
					break;
				}
			}
			if(next==0) next = pickBranchLit();
			if(next==0) { assert(order_heap.empty()); return true; }
			newDecisionLevel();
			NDECIDE++;
			uncheckedEnqueue(next,CRef_Undef);
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
	for (int m = opt_coef_sum; m >= 0; m--) {
		vector<int> aux;
		for (int i = 0; i < opt_K; i++) {
			if (m & (1 << i)) aux.push_back(  n-opt_K+1 + i);
			else              aux.push_back(-(n-opt_K+1 + i));
		}
		if (solve(aux)) {
			last_sol.resize(n+1-opt_K);
			for (int i=1;i<=n-opt_K;i++)if(~Level[i])last_sol[i]=true;else last_sol[i]=false;
			if (optimizing()) {
				// m + sum(coeff[i]*~ell[i]) >= opt_coef_sum possible.
				// m + opt_coef_sum - sum(coeff[i]*ell[i]) >= opt_coef_sum possible.
				// sum(coeff[i]*ell[i]) <= m possible.
				// sum(coeff0[i]*x[i]) + opt_normalize_add <= m possible.
				// sum(coeff0[i]*x[i]) <= m - opt_normalize_add possible.
				int s = 0;
				Clause & C = ca[objective];
				for (int i=0; i<(int)C.size(); i++) if (abs(C.lits()[i]) <= n-opt_K) {
					if (~Level[C.lits()[i]]) s += C.coefs()[i];
				}
				assert(opt_coef_sum - s <= m);
				m = opt_coef_sum - s;
				last_sol_value = m - opt_normalize_add;
				cout << "o " << last_sol_value << endl;
			}
		} else break;
	}
	if (!optimizing()) exit_SAT();
	else exit_OPT();
}
