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
#include <sstream>
#include <fstream>
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

// ---------------------------------------------------------------------
// Exit and interrupt

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE(),exit_ERROR(const std::initializer_list<std::string>&);

bool asynch_interrupt = false;
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
// Internal datastructures

struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };
std::ostream& operator<<(std::ostream& os, CRef cr) { return os << cr.ofs; }

struct Watch {
	CRef cref;
	int idx; // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
	Watch(CRef cr, int i):cref(cr),idx(i){};
	bool operator==(const Watch& other)const{return other.cref==cref && other.idx==idx;}
};

enum DeletionStatus { LOCKED, UNLOCKED, FORCEDELETE, MARKEDFORDELETE };
enum WatchStatus { FOUNDNEW, FOUNDNONE, CONFLICTING };
enum SolveState { SAT, UNSAT, INPROCESSING };

// ---------------------------------------------------------------------
// Globals

// Parameters
int verbosity=1;
bool print_sol=false;
bool originalRoundToOne=false;
int opt_mode=4;
bool clauseProp=true;
bool cardProp=true;
bool idxProp=true;
bool supProp=true;
float countingProp=0.7;

double rinc=2;
long long rfirst=100;
long long nbconstrsbeforereduce=2000;
long long incReduceDB=300;
long long nconfl_to_restart=0;
int resize_factor=2;
double v_vsids_decay=0.95;
double v_vsids_inc=1.0;
double c_vsids_inc=1.0;
double c_vsids_decay=0.999;

// Variables
Stats stats;
std::shared_ptr<Logger> logger;

IntSet tmpSet;
IntSet actSet;

intConstr tmpConstraint;
longConstr conflConstraint; // functions as old confl_data
intConstr logConstraint;

double initial_time;
Var n = 0;
Var orig_n = 0;
std::vector<CRef> constraints;
std::unordered_map<ID,CRef> external;
std::vector<std::vector<Watch>> _adj={{}}; std::vector<std::vector<Watch>>::iterator adj;
std::vector<int> _Level={-1}; std::vector<int>::iterator Level;
std::vector<Lit> trail;
std::vector<int> trail_lim, Pos;
std::vector<CRef> Reason;
int qhead; // for unit propagation
Val last_sol_obj_val = std::numeric_limits<Val>::max();
inline bool foundSolution(){ return last_sol_obj_val<std::numeric_limits<Val>::max(); }
std::vector<bool> last_sol;
std::vector<Lit> phase;
std::vector<double> activity;
inline int decisionLevel() { return trail_lim.size(); }
ID crefID = 0;

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void propagate(Lit p, CRef from);
int sz_constr(int length);
struct Constr { // internal constraint optimized for fast propagation
	ID id;
	Val degree;
	// NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
	struct {
		unsigned original     : 1;
		unsigned learnt       : 1;
		unsigned counting     : 1;
		unsigned lbd          : 29;
		unsigned status       : 2;
		unsigned size         : 30;
	} header;
	long long ntrailpops;
	float act;
	unsigned int watchIdx;
	Val slack; // sum of non-falsified watches minus w
	int data[];

	inline bool isClause() const { return slack==std::numeric_limits<Val>::min(); }
	inline bool isCard() const { return slack==std::numeric_limits<Val>::min()+1; }
	inline bool isSimple() const { return slack<std::numeric_limits<Val>::min()+2; }
	inline int getMemSize() const { return sz_constr(size()+(isSimple()?0:size())); }
	inline unsigned int size() const { return header.size; }
	inline void setStatus(DeletionStatus ds){ header.status=(unsigned int) ds; }
	inline DeletionStatus getStatus() const { return (DeletionStatus) header.status; }
	inline void setLBD(unsigned int lbd){ header.lbd=std::min(header.lbd,lbd); }
	inline unsigned int lbd() const { return header.lbd; }
	inline bool original() const { return header.original; }
	inline bool learnt() const { return header.learnt; }
	inline bool isCounting() const { return header.counting; }
	inline void setCounting(bool c){ header.counting=(unsigned int) c; }
	inline Coef largestCoef() const { assert(!isSimple()); return std::abs(data[0]); }
	inline Coef coef(unsigned int i) const { return isSimple()?1:std::abs(data[i<<1]); }
	inline Lit lit(unsigned int i) const { return isSimple()?data[i]:data[(i<<1)+1]; }
	inline bool isWatched(unsigned int i) const { assert(!isSimple()); return data[i]<0; }
	inline void undoFalsified(int i) {
		assert(!isSimple());
		assert(isCounting() || isWatched(i));
		assert(isFalse(Level,data[i+1]));
		++stats.NWATCHLOOKUPSBJ;
		slack += abs(data[i]); // TODO: slack -= data[i] when only watched propagation
	}
	inline WatchStatus propagateWatch(CRef cr, int& idx, Lit p){
		assert(isFalse(Level,p));
		++stats.NWATCHLOOKUPS;

		if(isClause()){
			assert(idx<0);
			assert(p==data[0] || p==data[1]);
			assert(size()>1);
			int widx=0;
			Lit watch=data[0];
			Lit otherwatch=data[1];
			if(p==data[1]){
				widx=1;
				watch=data[1];
				otherwatch=data[0];
			}
			assert(p==watch);
			assert(p!=otherwatch);
			if(isTrue(Level,otherwatch)){
				idx=otherwatch-INF; // set new blocked literal
				return WatchStatus::FOUNDNONE; // constraint is satisfied
			}
			const unsigned int Csize=size();
			for(unsigned int i=2; i<Csize; ++i){
				Lit l = data[i];
				if(!isFalse(Level,l)){
					int mid = i/2+1;
					data[i]=data[mid];
					data[mid]=watch;
					data[widx]=l;
					adj[l].emplace_back(cr,otherwatch-INF);
					stats.NWATCHCHECKS+=i-1;
					return WatchStatus::FOUNDNEW;
				}
			}
			stats.NWATCHCHECKS+=Csize-2;
			assert(isFalse(Level,watch));
			for(unsigned int i=2; i<Csize; ++i) assert(isFalse(Level,data[i]));
			if(isFalse(Level,otherwatch)) return WatchStatus::CONFLICTING;
			else{ assert(!isTrue(Level,otherwatch)); ++stats.NPROPCLAUSE; propagate(otherwatch,cr); }
			++stats.NPROPCHECKS;
			return WatchStatus::FOUNDNONE;
		}

		assert(idx>=0);
		if(isCard()){
			assert(idx%2==1);
			unsigned int widx=idx;
			widx = widx>>1;
			assert(data[widx]==p);
			const unsigned int Csize=size();
			if(!idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=degree+1; }
			assert(watchIdx>degree);
			stats.NWATCHCHECKS-=watchIdx;
			for(; watchIdx<Csize; ++watchIdx){
				Lit l = data[watchIdx];
				if(!isFalse(Level,l)){
					unsigned int mid = (watchIdx+degree+1)/2; assert(mid<=watchIdx); assert(mid>degree);
					data[watchIdx]=data[mid];
					data[mid]=data[widx];
					data[widx]=l;
					adj[l].emplace_back(cr,(widx<<1)+1);
					stats.NWATCHCHECKS+=watchIdx+1;
					return WatchStatus::FOUNDNEW;
				}
			}
			stats.NWATCHCHECKS+=watchIdx;
			assert(isFalse(Level,data[widx]));
			for(unsigned int i=degree+1; i<Csize; ++i) assert(isFalse(Level,data[i]));
			for(unsigned int i=0; i<=degree; ++i) if(i!=widx && isFalse(Level,data[i])) return WatchStatus::CONFLICTING;
			for(unsigned int i=0; i<=degree; ++i){
				Lit l = data[i];
				if(i!=widx && !isTrue(Level,l)){ ++stats.NPROPCARD; propagate(l,cr); }
			}
			stats.NPROPCHECKS+=degree+1;
			return WatchStatus::FOUNDNONE;
		}

		assert(idx%2==0);
		assert(data[idx+1]==p);
		const unsigned int Csize2 = 2*size(); const Coef ClargestCoef = largestCoef();
		const Coef c = data[idx];

		if(isCounting()){ // use counting propagation
			slack-=c;
			if(slack<0) return WatchStatus::CONFLICTING;
			if(slack<ClargestCoef){
				if(!idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=0; }
				stats.NPROPCHECKS-=watchIdx>>1;
				for(; watchIdx<Csize2 && data[watchIdx]>slack; watchIdx+=2){
					const Lit l = data[watchIdx+1];
					if(isUnknown(Pos,l)){
						stats.NPROPCLAUSE+=(degree==1); stats.NPROPCARD+=(degree!=1 && ClargestCoef==1); ++stats.NPROPCOUNTING;
						propagate(l,cr);
					}
				}
				stats.NPROPCHECKS+=watchIdx>>1;
			}
			return WatchStatus::FOUNDNONE;
		}

		// use watched propagation
		if(!idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=0; }
		assert(c<0);
		slack+=c;
		if(!supProp || slack-c>=ClargestCoef){ // look for new watches if previously, slack was at least ClargestCoef
			stats.NWATCHCHECKS-=watchIdx>>1;
			for(; watchIdx<Csize2 && slack<ClargestCoef; watchIdx+=2){ // NOTE: first innermost loop of RoundingSat
				const Coef cf = data[watchIdx];
				const Lit l = data[watchIdx+1];
				if(cf>0 && !isFalse(Level,l)){
					slack+=cf;
					data[watchIdx]=-cf;
					adj[l].emplace_back(cr,watchIdx);
				}
			}
			stats.NWATCHCHECKS+=watchIdx>>1;
			if(slack<ClargestCoef){ assert(watchIdx==Csize2); watchIdx=0; }
		} // else we did not find enough watches last time, so we can skip looking for them now

		if(slack>=ClargestCoef){ data[idx]=-c; return WatchStatus::FOUNDNEW; }
		if(slack<0) return WatchStatus::CONFLICTING;
		// keep the watch, check for propagation
		stats.NPROPCHECKS-=watchIdx>>1;
		for(; watchIdx<Csize2 && std::abs(data[watchIdx])>slack; watchIdx+=2){ // NOTE: second innermost loop of RoundingSat
			const Lit l = data[watchIdx+1];
			if(isUnknown(Pos,l)){
				stats.NPROPCLAUSE+=(degree==1); stats.NPROPCARD+=(degree!=1 && ClargestCoef==1); ++stats.NPROPWATCH;
				propagate(l,cr);
			}
		}
		stats.NPROPCHECKS+=watchIdx>>1;
		return WatchStatus::FOUNDNONE;
	}

	template<class S, class L>
	inline void toConstraint(Constraint<S,L>& out) const {
		assert(out.isReset()); // don't use a Constraint used by other stuff
		out.addRhs(degree);
		for(size_t i=0;i<size();++i){ assert(coef(i)!=0); out.addLhs(coef(i), lit(i)); }
		out.degree=degree;
		if(out.plogger) out.resetBuffer(id);
	}
};
std::ostream & operator<<(std::ostream & o, const Constr& C) {
	C.toConstraint(logConstraint);
	o << C.id << ": " << logConstraint << " sl: " << logConstraint.getSlack(Level);
	logConstraint.reset();
	return o;
}
Val getSlack(Constr& C){
	C.toConstraint(logConstraint);
	Val slack = logConstraint.getSlack(Level);
	logConstraint.reset();
	return slack;
}

// ---------------------------------------------------------------------
// Memory. Maximum supported size of learnt constraint database is 16GB

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size){
	void* mem = realloc(ptr, size);
	if(mem == NULL && errno == ENOMEM) throw OutOfMemoryException();
	else return mem;
}
int sz_constr(int length) { return (sizeof(Constr)+sizeof(int)*length)/sizeof(uint32_t); }
struct {
	uint32_t* memory; // TODO: why not uint64_t?
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
			if (cap <= prev_cap) throw OutOfMemoryException();
		}

		assert(cap > 0);
		memory = (uint32_t*) xrealloc(memory, sizeof(uint32_t) * cap);
	}

	// TODO: allow constraints with 10^18 bit degree
	CRef alloc(intConstr& constraint, bool formula, bool learnt, bool locked){
		assert(constraint.getDegree()>0);
		assert(constraint.getDegree()<INF);
		assert(constraint.isSaturated());
		// as the constraint is saturated, the coefficients are between 1 and 1e9 as well.
		assert(!constraint.vars.empty());
		unsigned int length = constraint.vars.size();
		bool asClause = clauseProp && constraint.getDegree()==1;
		bool asCard = !asClause && cardProp && constraint.isCardinality();

		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		uint32_t old_at = at;
		at += sz_constr(length+((asClause||asCard)?0:length));
		capacity(at);
		Constr* constr = (Constr*)(memory+old_at);
		new (constr) Constr;
		constr->id = logger?logger->last_proofID:++crefID; assert(constr->id>0);
		constr->act = 0;
		constr->degree = constraint.getDegree();
		constr->header = {formula,learnt,0,0x1FFFFFFF,(unsigned int)(locked?LOCKED:UNLOCKED),length};
		constr->ntrailpops = -1;
		constr->slack = asClause?std::numeric_limits<Val>::min():(asCard?std::numeric_limits<Val>::min()+1:-constr->degree);
		constr->watchIdx = 0;
		assert(asClause == constr->isClause());
		assert(asCard == constr->isCard());
		for(unsigned int i=0; i<length; ++i){
			Var v = constraint.vars[i];
			assert(constraint.getLit(v)!=0);
			if(constr->isSimple()) constr->data[i]=constraint.getLit(v);
			else{
				constr->data[(i<<1)]=std::abs(constraint.coefs[v]);
				constr->data[(i<<1)+1]=constraint.getLit(v);
			}
		}
		return CRef{old_at};
	}
	Constr& operator[](CRef cr) { return (Constr&)*(memory+cr.ofs); }
	const Constr& operator[](CRef cr) const { return (Constr&)*(memory+cr.ofs); }
} ca;

// ---------------------------------------------------------------------
// VSIDS

struct{
	int cap=0;
	// segment tree (fast implementation of priority queue).
	std::vector<Var> tree = {-1,-1};
	void resize(int newsize) {
		if (cap >= newsize) return;
		// insert elements in such order that tie breaking remains intact
		std::vector<Var> variables;
		while (!empty()) variables.push_back(removeMax());
		tree.clear();
		while(cap<newsize) cap=cap*resize_factor+1;
		tree.resize(2*(cap+1), -1);
		for (Var x : variables) insert(x);
	}
	void percolateUp(Var x) {
		for(int at=x+cap+1; at>1; at>>=1){
			if(tree[at^1]==-1 || activity[x]>activity[tree[at^1]])tree[at>>1]=x;
			else break;
		}
	}
	bool empty() const { return tree[1] == -1; }
	bool inHeap(Var x) const { return tree[x+cap+1] != -1; }
	void insert(Var x) {
		assert(x<=cap);
		if (inHeap(x)) return;
		tree[x+cap+1] = x;
		percolateUp(x);
	}
	Var removeMax() {
		Var x = tree[1];
		assert(x != -1);
		tree[x+cap+1] = -1;
		for(int at=x+cap+1; at>1; at>>=1){
			if(tree[at^1] != -1 && (tree[at]==-1 || activity[tree[at^1]]>activity[tree[at]]))tree[at>>1]=tree[at^1];
			else tree[at>>1]=tree[at];
		}
		return x;
	}
} order_heap;

void vDecayActivity() { v_vsids_inc *= (1 / v_vsids_decay); }
void vBumpActivity(Var v){
	assert(v>0);
	if ( (activity[v] += v_vsids_inc) > 1e100 ) {
		// Rescale:
		for (Var x=1; x<=n; ++x)
			activity[x] *= 1e-100;
		v_vsids_inc *= 1e-100; }

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.percolateUp(v);
}

void cDecayActivity() { c_vsids_inc *= (1 / c_vsids_decay); }
void cBumpActivity (Constr& c) {
	c.act += c_vsids_inc;
	if(c.act > 1e20){ // Rescale:
		for (size_t i = 0; i < constraints.size(); i++) ca[constraints[i]].act *= 1e-20;
		c_vsids_inc *= 1e-20;
	}
}

// ---------------------------------------------------------------------
// Search

void uncheckedEnqueue(Lit p, CRef from){
	assert(!isTrue(Level,p));
	assert(!isFalse(Level,p));
	assert(isUnknown(Pos,p));
	Var v = std::abs(p);
	Reason[v] = from;
	if(decisionLevel()==0){
		Reason[v] = CRef_Undef; // no need to keep track of reasons for unit literals
		if(logger){
			Constr& C = ca[from];
			C.toConstraint(logConstraint);
			logConstraint.logUnit(Level,Pos,v,stats);
			logConstraint.reset();
			assert(logger->unitIDs.size()==trail.size()+1);
		}
	}
	Level[p] = decisionLevel();
	Pos[v] = (int) trail.size();
	trail.push_back(p);
}

CRef attachConstraint(intConstr& constraint, bool formula, bool learnt, bool locked){
	assert(constraint.isSortedInDecreasingCoefOrder());
	assert(constraint.isSaturated());
	assert(constraint.hasNoZeroes());
	assert(constraint.hasNoUnits(Level));
	assert(constraint.getDegree()>0);
	assert(constraint.vars.size()>0);

	if(logger) constraint.logProofLine("a", stats);
	CRef cr = ca.alloc(constraint,formula,learnt,locked);
	constraints.push_back(cr);
	Constr& C = ca[cr]; int* data = C.data;

	stats.LEARNEDLENGTHSUM+=C.size();
	stats.LEARNEDDEGREESUM+=C.degree;
	if(C.degree==1) ++stats.NCLAUSESLEARNED;
	else if(C.isCard() || C.largestCoef()==1) ++stats.NCARDINALITIESLEARNED;
	else ++stats.NGENERALSLEARNED;

	if(C.isSimple()){
		if(C.degree>=C.size()){
			assert(decisionLevel()==0);
			for(unsigned int i=0; i<C.size(); ++i){ assert(isUnknown(Pos,data[i])); propagate(data[i],cr); }
			return cr;
		}

		unsigned int watch=0;
		for(unsigned int i=0; i<C.size(); ++i){
			Lit l = data[i];
			if(!isFalse(Level,l)){
				data[i]=data[watch];
				data[watch++]=l;
				if(watch>C.degree+1) break;
			}
		}
		assert(watch>=C.degree); // we found enough watches to satisfy the constraint
		if(isFalse(Level,data[C.degree])){
			for(unsigned int i=0; i<C.degree; ++i){
				assert(!isFalse(Level,data[i]));
				if(!isTrue(Level,data[i])) propagate(data[i],cr);
			}
			for(unsigned int i=C.degree+1; i<C.size(); ++i){ // ensure last watch is last falsified literal
				Lit l = data[i];
				assert(isFalse(Level,l));
				if(Level[-l]>Level[-data[C.degree]]){ data[i]=data[C.degree]; data[C.degree]=l; }
			}
		}
		if(C.isClause()) for(unsigned int i=0; i<2; ++i) adj[data[i]].emplace_back(cr,data[1-i]-INF); // add blocked literal
		else for(unsigned int i=0; i<=C.degree; ++i) adj[data[i]].emplace_back(cr,(i<<1)+1); // add watch index
		return cr;
	}

	Val watchSum=-C.degree-C.largestCoef();
	unsigned int minWatches=0;
	for(; minWatches<2*C.size() && watchSum<0; minWatches+=2) watchSum+=data[minWatches];
	minWatches>>=1;
	assert(C.size()>0);
	assert(minWatches>0);
	C.setCounting(countingProp==1 || countingProp>(1-minWatches/(float)C.size()));

	if(C.isCounting()){ // use counting propagation
		++stats.NCOUNTING;
		for(unsigned int i=0; i<2*C.size(); i+=2){
			Lit l = data[i+1];
			adj[l].emplace_back(cr,i);
			if(!isFalse(Level,l) || Pos[std::abs(l)]>=qhead) C.slack+=data[i];
		}
		assert(C.slack>=0);
		if(C.slack<C.largestCoef()){ // propagate
			for(unsigned int i=0; i<2*C.size() && data[i]>C.slack; i+=2) if(isUnknown(Pos,data[i+1])) {
				propagate(data[i+1],cr);
			}
		}
		return cr;
	}

	// watched propagation
	++stats.NWATCHED;
	for(unsigned int i=0; i<2*C.size() && C.slack<C.largestCoef(); i+=2){
		Lit l = data[i+1];
		if(!isFalse(Level,l) || Pos[std::abs(l)]>=qhead){
			assert(!C.isWatched(i));
			C.slack+=data[i];
			data[i]=-data[i];
			adj[l].emplace_back(cr,i);
		}
	}
	assert(C.slack>=0);
	if(C.slack<C.largestCoef()){
		// set sufficient falsified watches
		std::vector<unsigned int> falsifiedIdcs;
		falsifiedIdcs.reserve(C.size());
		for(unsigned int i=0; i<2*C.size(); i+=2) if(isFalse(Level,data[i+1]) && Pos[std::abs(data[i+1])]<qhead) falsifiedIdcs.push_back(i);
		std::sort(falsifiedIdcs.begin(),falsifiedIdcs.end(),[&](unsigned i1,unsigned i2){
			return Pos[std::abs(data[i1+1])]>Pos[std::abs(data[i2+1])]; });
		Val diff = C.largestCoef()-C.slack;
		for(unsigned int i: falsifiedIdcs){
			assert(!C.isWatched(i));
			diff-=data[i];
			data[i]=-data[i];
			adj[data[i+1]].emplace_back(cr,i);
			if(diff<=0) break;
		}
		// perform initial propagation
		for(unsigned int i=0; i<2*C.size() && std::abs(data[i])>C.slack; i+=2) if(isUnknown(Pos,data[i+1])) {
			propagate(data[i+1],cr);
		}
	}
	return cr;
}

void undoOne(){
	assert(!trail.empty());
	++stats.NTRAILPOPS;
	Lit l = trail.back();
	if(qhead==(int)trail.size()){
		for(const Watch& w: adj[-l]) if(w.idx>=0 && w.idx%2==0) ca[w.cref].undoFalsified(w.idx);
		--qhead;
	}
	Var v = std::abs(l);
	trail.pop_back();
	Level[l] = -1;
	Pos[v] = -1;
	phase[v] = l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	order_heap.insert(v);
}

inline void backjumpTo(int level){
	assert(level>=0);
	while(decisionLevel()>level) undoOne();
}

inline void decide(Lit l){
	++stats.NDECIDE;
	trail_lim.push_back(trail.size());
	uncheckedEnqueue(l,CRef_Undef);
}

inline void propagate(Lit l, CRef reason){
	assert(reason!=CRef_Undef);
	++stats.NPROP;
	uncheckedEnqueue(l,reason);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void recomputeLBD(Constr& C) {
	if(C.lbd()<=2) return;
	assert(tmpSet.size()==0);
	for (int i=0; i<(int)C.size(); i++) if (isFalse(Level,C.lit(i))) tmpSet.add(Level[-C.lit(i)]);
	C.setLBD(1+tmpSet.size()); // +1 because, e.g., a binary learned clause contains 1 false literal but should have LBD 2
	tmpSet.reset();
}

void analyze(CRef confl){
	Constr& C = ca[confl];
	if (C.learnt()) {
		cBumpActivity(C);
		recomputeLBD(C);
	}

	C.toConstraint(conflConstraint);
	stats.NADDEDLITERALS+=conflConstraint.vars.size();
	conflConstraint.removeUnitsAndZeroes(Level,Pos);
	assert(actSet.size()==0); // will hold the literals that need their activity bumped
	for(Var v: conflConstraint.vars) actSet.add(conflConstraint.getLit(v));
	while(true){
		if(asynch_interrupt)exit_INDETERMINATE();
		if (decisionLevel() == 0) {
			if(logger) conflConstraint.logInconsistency(Level,Pos,stats);
			assert(conflConstraint.getSlack(Level)<0);
			exit_UNSAT();
		}
		Lit l = trail.back();
		assert(std::abs(conflConstraint.getCoef(-l))<INF);
		Coef confl_coef_l = conflConstraint.getCoef(-l);
		if(confl_coef_l>0) {
			if (conflConstraint.falsifiedAtLvlisOne(Level,decisionLevel())) break;
			assert(Reason[std::abs(l)] != CRef_Undef);
			if(originalRoundToOne){
				conflConstraint.roundToOne(Level,confl_coef_l,false);
				confl_coef_l=1;
			}
			Constr& reasonC = ca[Reason[std::abs(l)]];
			if (reasonC.learnt()) {
				cBumpActivity(reasonC);
				recomputeLBD(reasonC);
			}
			reasonC.toConstraint(tmpConstraint);
			stats.NADDEDLITERALS+=tmpConstraint.vars.size();
			tmpConstraint.removeUnitsAndZeroes(Level,Pos); // NOTE: also saturates
			tmpConstraint.weakenNonImplying(Level,tmpConstraint.getCoef(l),tmpConstraint.getSlack(Level),stats); // NOTE: also saturates
			assert(tmpConstraint.getCoef(l)>tmpConstraint.getSlack(Level));
			Coef slk = tmpConstraint.getSlack(Level);
			if(slk>0){
				Coef div = slk+1;
				if(originalRoundToOne){ tmpConstraint.weaken(-(tmpConstraint.getCoef(l)%div),l); tmpConstraint.saturate(); }
				tmpConstraint.roundToOne(Level,div,!originalRoundToOne);
			}
			assert(tmpConstraint.getSlack(Level)<=0);
			for(Var v: tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
			Coef reason_coef_l = tmpConstraint.getCoef(l);
			Coef gcd_coef_l = aux::gcd(reason_coef_l,confl_coef_l);
			conflConstraint.addUp(Level,tmpConstraint,confl_coef_l/gcd_coef_l,reason_coef_l/gcd_coef_l);
			tmpConstraint.reset();
			assert(conflConstraint.getCoef(-l)==0);
			assert(conflConstraint.getSlack(Level)<0);
		}
		undoOne();
	}
	assert(conflConstraint.getSlack(Level)<0);
	for(Lit l: actSet.keys) if(l!=0) vBumpActivity(std::abs(l));
	actSet.reset();
}

/**
 * Unit propagation with watched literals.
 *
 * post condition: all watches up to trail[qhead] have been propagated
 */
CRef runPropagation() {
	while(qhead<(int)trail.size()){
		Lit p=trail[qhead++];
		std::vector<Watch> & ws = adj[-p];
		for(int it_ws=0; it_ws<(int)ws.size(); ++it_ws){
			int idx = ws[it_ws].idx;
			if(idx<0 && isTrue(Level,idx+INF)){ assert(ca[ws[it_ws].cref].isClause()); continue; } // blocked literal check
			CRef cr = ws[it_ws].cref;
			Constr& C = ca[cr];
			if(C.getStatus()>=FORCEDELETE){ aux::swapErase(ws,it_ws--); continue; }
			WatchStatus wstat = C.propagateWatch(cr,ws[it_ws].idx,-p);
			if(wstat==WatchStatus::FOUNDNEW) aux::swapErase(ws,it_ws--);
			else if(wstat==WatchStatus::CONFLICTING){ // clean up current level and stop propagation
				++stats.NTRAILPOPS;
				for(int i=0; i<=it_ws; ++i){
					const Watch& w=ws[i];
					if(w.idx>=0 && w.idx%2==0) ca[w.cref].undoFalsified(w.idx);
				}
				--qhead;
				return cr;
			}
		}
	}
	return CRef_Undef;
}

Lit pickBranchLit(){
	Var next = 0;
	// Activity based decision:
	while (next == 0 || !isUnknown(Pos,next)){
		if (order_heap.empty()) return 0;
		else next = order_heap.removeMax();
	}
	assert(phase[0]==0);
	return phase[next];
}

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
	if (nvars >= INF) exit_ERROR({"Number of variables cannot exceed 10^9."});
	if (nvars <= n) return;
	aux::resizeIntMap(_adj,adj,nvars,resize_factor,{});
	aux::resizeIntMap(_Level,Level,nvars,resize_factor,-1);
	Pos.resize(nvars+1,-1);
	Reason.resize(nvars+1,CRef_Undef);
	activity.resize(nvars+1,0);
	phase.resize(nvars+1);
	last_sol.resize(nvars+1,false);
	tmpConstraint.resize(nvars+1);
	conflConstraint.resize(nvars+1);
	logConstraint.resize(nvars+1);
	order_heap.resize(nvars+1);
	for(Var v=n+1;v<=nvars;++v) phase[v] = -v, order_heap.insert(v);
	n = nvars;
}

// ---------------------------------------------------------------------
// Constraint addition

void learnConstraint(longConstr& confl){
	assert(confl.getDegree()>0);
	assert(confl.getDegree()<INF);
	assert(confl.isSaturated());
	confl.copyTo(tmpConstraint);
	assert(tmpConstraint.hasNoUnits(Level));
	tmpConstraint.removeZeroes();
	tmpConstraint.sortInDecreasingCoefOrder();
	int assertionLevel = tmpConstraint.getAssertionLevel(Level,Pos);
	assert(assertionLevel==0 || assertionLevel<decisionLevel());
	backjumpTo(assertionLevel);
	assert(qhead==(int)trail.size()); // jumped back sufficiently far to catch up with qhead
	Val slk = tmpConstraint.getSlack(Level);
	if(slk<0){
		if(logger) tmpConstraint.logInconsistency(Level,Pos,stats);
		assert(decisionLevel()==0);
		exit_UNSAT();
	}
	tmpConstraint.heuristicWeakening(Level,Pos,slk,stats);
	tmpConstraint.postProcess(Level,Pos,false,stats);
	assert(tmpConstraint.isSaturated());

	CRef cr = attachConstraint(tmpConstraint,false,true,false);
	tmpConstraint.reset();
	Constr& C = ca[cr];
	recomputeLBD(C);
}

CRef addInputConstraint(intConstr& c, bool original, bool locked){
	assert(decisionLevel()==0);
	if(logger) c.logAsInput();
	c.postProcess(Level,Pos,true,stats);
	if(c.getDegree()>=(Val) INF) exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
	if(c.getDegree()<=0) return CRef_Undef; // already satisfied.

	if(c.getSlack(Level)<0){
		puts("c Inconsistent input constraint");
		if(logger) c.logInconsistency(Level,Pos,stats);
		assert(decisionLevel()==0);
		exit_UNSAT();
	}

	CRef cr = attachConstraint(c,original,false,locked);
	CRef confl = runPropagation();
	if (confl != CRef_Undef){
		puts("c Input conflict");
		if(logger){
			ca[confl].toConstraint(logConstraint);
			logConstraint.logInconsistency(Level,Pos,stats);
			logConstraint.reset();
		}
		assert(decisionLevel()==0);
		assert(getSlack(ca[confl])<0);
		exit_UNSAT();
	}
	return cr;
}

// ---------------------------------------------------------------------
// Parsers

/*
 * The OPB parser does not support nonlinear constraints like "+1 x1 x2 +1 x3 x4 >= 1;"
 */
int read_number(const std::string & s) { // TODO: should also read larger numbers than int (e.g., capture large degree)
	long long answer = 0;
	for (char c : s) if ('0' <= c && c <= '9') {
		answer *= 10, answer += c - '0';
		if (answer >= INF) exit_ERROR({"Input formula contains absolute value larger than 10^9: ",s});
	}
	for (char c : s) if (c == '-') answer = -answer;
	return answer;
}

void opb_read(std::istream & in, intConstr& objective) {
	intConstr inverted;
	inverted.initializeLogging(logger);
	bool first_constraint = true; _unused(first_constraint);
	for (std::string line; getline(in, line);) {
		if (line.empty()) continue;
		else if (line[0] == '*') continue;
		else {
			for (char & c : line) if (c == ';') c = ' ';
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
			std::istringstream is (line);
			assert(tmpConstraint.isReset());
			std::vector<std::string> tokens;
			{ std::string tmp; while (is >> tmp) tokens.push_back(tmp); }
			if (tokens.size() % 2 != 0) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(long long)tokens.size(); i+=2) if (find(tokens[i].begin(),tokens[i].end(),'x')!=tokens[i].end()) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(long long)tokens.size(); i+=2) {
				std::string scoef = tokens[i];
				std::string var = tokens[i+1];
				Coef coef = read_number(scoef);
				bool negated = false;
				std::string origvar = var;
				if (!var.empty() && var[0] == '~') {
					negated = true;
					var = var.substr(1);
				}
				if (var.empty() || var[0] != 'x') exit_ERROR({"Invalid literal token: ",origvar});
				var = var.substr(1);
				Lit l = atoi(var.c_str());
				if (!(1 <= l && l <= n)) exit_ERROR({"Literal token out of variable range: ",origvar});
				if (negated) l = -l;
				tmpConstraint.addLhs(coef,l);
			}
			if(opt_line){
				tmpConstraint.copyTo(objective);
				tmpConstraint.reset();
			}else{
				tmpConstraint.addRhs(read_number(line0.substr(line0.find("=") + 1)));
				// Handle equality case with two constraints
				bool equality = line0.find(" = ") != std::string::npos;
				if(equality) tmpConstraint.copyTo(inverted,true);
				// NOTE: addInputConstraint modifies tmpConstraint, so the inverted version is stored first
				addInputConstraint(tmpConstraint,true,false);
				tmpConstraint.reset();
				if(equality){
					addInputConstraint(inverted,true,false);
					inverted.reset();
				}
			}
		}
	}
	orig_n=n;
}

void wcnf_read(std::istream & in, long long top, intConstr& objective) {
	assert(objective.isReset());
	for (std::string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			std::istringstream is (line);
			long long weight; is >> weight;
			if(weight==0) continue;
			assert(tmpConstraint.isReset());
			tmpConstraint.addRhs(1);
			Lit l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			if(weight<top){ // soft clause
				if(weight>=INF) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
				if(weight<0) exit_ERROR({"Negative clause weight: ",std::to_string(weight)});
				setNbVariables(n+1); // increases n to n+1
				objective.resize(n+1);
				objective.addLhs(weight,n);
				tmpConstraint.addLhs(1,n);
			} // else hard clause
			addInputConstraint(tmpConstraint,true,false);
			tmpConstraint.reset();
		}
	}
	orig_n = n-objective.vars.size();
}

void cnf_read(std::istream & in) {
	for (std::string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			std::istringstream is (line);
			assert(tmpConstraint.isReset());
			tmpConstraint.addRhs(1);
			Lit l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			addInputConstraint(tmpConstraint,true,false);
			tmpConstraint.reset();
		}
	}
	orig_n=n;
}

void file_read(std::istream & in, intConstr& objective) {
	for (std::string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		if (line[0] == 'p') {
			std::istringstream is (line);
			is >> line; // skip 'p'
			std::string type; is >> type;
			long long n; is >> n;
			setNbVariables(n);
			if(type=="cnf"){
				cnf_read(in);
				return;
			}else if(type == "wcnf"){
				is >> line; // skip nbConstraints
				long long top; is >> top;
				wcnf_read(in, top, objective);
				return;
			}
		} else if (line[0] == '*' && line.substr(0, 13) == "* #variable= ") {
			std::istringstream is (line.substr(13));
			long long n; is >> n;
			setNbVariables(n);
			opb_read(in,objective);
			return;
		}
	}
	exit_ERROR({"No supported format [opb, cnf, wcnf] detected."});
}

// ---------------------------------------------------------------------
// Garbage collection

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are deleted.
void garbage_collect(){
	assert(decisionLevel()==0); // so we don't need to update the pointer of Reason<CRef>
	if (verbosity > 0) puts("c GARBAGE COLLECT");
	for(Lit l=-n; l<=n; ++l) for(int i=0; i<(int)adj[l].size(); ++i){
		if(ca[adj[l][i].cref].getStatus()==MARKEDFORDELETE) aux::swapErase(adj[l],i--);
	}

	ca.wasted=0;
	ca.at=0;
	std::unordered_map<uint32_t,CRef> crefmap;
	for(int i=1; i<(int)constraints.size(); ++i) assert(constraints[i-1].ofs<constraints[i].ofs);
	for(CRef& cr: constraints){
		uint32_t offset = cr.ofs;
		int memSize = ca[cr].getMemSize();
		memmove(ca.memory+ca.at, ca.memory+cr.ofs, sizeof(uint32_t)*memSize);
		cr.ofs = ca.at;
		ca.at += memSize;
		crefmap[offset]=cr;
	}
	#define update_ptr(cr) cr=crefmap[cr.ofs];
	for(Lit l=-n;l<=n;l++) for(size_t i=0;i<adj[l].size();i++) update_ptr(adj[l][i].cref);
	for(auto& ext: external) update_ptr(ext.second);
	#undef update_ptr
}

void removeConstraint(Constr& C){
	assert(decisionLevel()==0);
	assert(C.getStatus()!=MARKEDFORDELETE);
	assert(C.getStatus()!=LOCKED);
	C.setStatus(MARKEDFORDELETE);
	ca.wasted += C.getMemSize();
}

void reduceDB(){
	if (verbosity > 0) puts("c INPROCESSING");
	assert(decisionLevel()==0);

	std::vector<CRef> learnts;
	learnts.reserve(constraints.size()/2);

	size_t totalLearnts=0;
	size_t promisingLearnts=0;
	for(CRef& cr: constraints){
		Constr& C = ca[cr];
		if(C.getStatus()==FORCEDELETE) removeConstraint(C);
		else if(C.getStatus()==UNLOCKED){
			Val eval = -C.degree;
			for(int j=0; j<(int)C.size() && eval<0; ++j) if(isUnit(Level,C.lit(j))) eval+=C.coef(j);
			if(eval>=0) removeConstraint(C); // remove constraints satisfied at level 0
		}
		if(C.learnt() && C.getStatus()==UNLOCKED){
			if(C.size()>2 && C.lbd()>2) learnts.push_back(cr); // Keep all binary clauses and short LBDs
			if(C.size()<=2 || C.lbd()<=3) ++promisingLearnts;
			++totalLearnts;
		}
	}

	if(promisingLearnts>totalLearnts/2) nbconstrsbeforereduce += 1000;
	else nbconstrsbeforereduce += 100;
	std::sort(learnts.begin(), learnts.end(), [&](CRef x, CRef y){
		return ca[x].lbd() > ca[y].lbd() || (ca[x].lbd() == ca[y].lbd() && ca[x].act < ca[y].act);
	});
	for (size_t i=0; i<std::min(totalLearnts/2,learnts.size()); ++i) removeConstraint(ca[learnts[i]]);

	size_t i=0; size_t j=0;
	for(; i<constraints.size(); ++i) if(ca[constraints[i]].getStatus()!=MARKEDFORDELETE) constraints[j++]=constraints[i];
	constraints.resize(j);
	if ((double) ca.wasted / (double) ca.at > 0.2) garbage_collect();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
double luby(double y, int i){
	// Find the finite subsequence that contains index 'i', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < i+1; seq++, size = 2*size+1);
	while(size != i+1){
		size = (size-1)>>1;
		seq--;
		assert(size!=0);
		i = i % size;
	}
	return std::pow(y, seq);
}

// ---------------------------------------------------------------------
// Main

void print_stats() {
	double timespent = aux::cpuTime()-initial_time;
	printf("c CPU time			  : %g s\n", timespent);
	printf("c deterministic time %lld %.2e\n", stats.getDetTime(),(double)stats.getDetTime());
	printf("c propagations %lld\n", stats.NPROP);
	printf("c decisions %lld\n", stats.NDECIDE);
	printf("c conflicts %lld\n", stats.NCONFL);
	printf("c restarts %lld\n", stats.NRESTARTS);
	printf("c inprocessing phases %lld\n", stats.NCLEANUP);
	printf("c clauses %lld\n", stats.NCLAUSESLEARNED);
	printf("c cardinalities %lld\n", stats.NCARDINALITIESLEARNED);
	printf("c watched constraints %lld\n", stats.NWATCHED);
	printf("c counting constraints %lld\n", stats.NCOUNTING);
	printf("c general constraints %lld\n", stats.NGENERALSLEARNED);
	printf("c average constraint length %.2f\n", stats.NCONFL==0?0:(double)stats.LEARNEDLENGTHSUM/stats.NCONFL);
	printf("c average constraint degree %.2f\n", stats.NCONFL==0?0:(double)stats.LEARNEDDEGREESUM/stats.NCONFL);
	printf("c gcd simplifications %lld\n", stats.NGCD);
	printf("c detected cardinalities %lld\n", stats.NCARDDETECT);
	printf("c weakened non-implied lits %lld\n", stats.NWEAKENEDNONIMPLIED);
	printf("c weakened non-implying lits %lld\n", stats.NWEAKENEDNONIMPLYING);
	printf("c auxiliary variables introduced %d\n", n-orig_n);
	if(opt_mode>0){
		printf("c solutions found %lld\n", stats.NSOLS);
		printf("c cores constructed %lld\n", stats.NCORES);
		printf("c core cardinality constraints returned %lld\n", stats.NCORECARDINALITIES);
	}
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

Val lhs(Constr& C, const std::vector<bool>& sol){
	Val result = 0;
	for(size_t j=0; j<C.size(); ++j){
		Lit l = C.lit(j);
		result+=((l>0)==sol[std::abs(l)])*C.coef(j);
	}
	return result;
}

bool checksol() {
	for(CRef cr: constraints){
		Constr& C = ca[cr];
		if(C.original() && lhs(C,last_sol)<C.degree) return false;
	}
	puts("c SATISFIABLE (checked)");
	return true;
}

void printSol(){
	assert(checksol());
	if(!print_sol) return;
	printf("v");
	for(Var v=1; v<=orig_n; ++v) printf(last_sol[v]?" x%d":" -x%d",v);
	printf("\n");
}

void exit_SAT() {
	if(logger) logger->flush();
	print_stats();
	if(foundSolution()) std::cout << "o " << last_sol_obj_val << std::endl;
	puts("s SATISFIABLE");
	printSol();
	exit(10);
}

void exit_UNSAT() {
	if(logger) logger->flush();
	print_stats();
	if(foundSolution()){
		std::cout << "o " << last_sol_obj_val << std::endl;
		std::cout << "s OPTIMUM FOUND" << std::endl;
		printSol();
		exit(30);
	}else{
		puts("s UNSATISFIABLE");
		exit(20);
	}
}

void exit_INDETERMINATE() {
	if(foundSolution()) exit_SAT();
	if(logger) logger->flush();
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void exit_ERROR(const std::initializer_list<std::string>& messages){
	if(logger) logger->flush();
	print_stats();
	std::cout << "Error: ";
	for(const std::string& m: messages) std::cout << m;
	std::cout << std::endl;
	exit(1);
}

void usage(char* name) {
	printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", name);
	printf("\n");
	printf("Options:\n");
	printf("  --help           Prints this help message.\n");
	printf("  --print-sol=arg  Prints the solution if found (default %d).\n",print_sol);
	printf("  --verbosity=arg  Set the verbosity of the output (default %d).\n",verbosity);
	printf("\n");
	printf("  --var-decay=arg  Set the VSIDS decay factor (0.5<=arg<1; default %lf).\n",v_vsids_decay);
	printf("  --rinc=arg       Set the base of the Luby restart sequence (float >=1; default %lf).\n",rinc);
	printf("  --rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %lld).\n",rfirst);
	printf("  --original-rto=arg Set whether to use RoundingSat's original round-to-one conflict analysis (0 or 1; default %d).\n",originalRoundToOne);
	printf("  --opt-mode=arg   Set optimization mode: 0 linear, 1(2) (lazy) core-guided, 3(4) (lazy) hybrid (default %d).\n",opt_mode);
	printf("  --prop-counting=arg Counting propagation instead of watched propagation (float between 0 (no counting) and 1 (always counting)); default %lf).\n",countingProp);
	printf("  --prop-clause=arg Optimized two-watched propagation for clauses (0 or 1; default %d).\n",clauseProp);
	printf("  --prop-card=arg  Optimized watched propagation for cardinalities (0 or 1; default %d).\n",cardProp);
	printf("  --prop-idx=arg   Optimize index of watches during propagation (0 or 1; default %d).\n",idxProp);
	printf("  --prop-sup=arg   Avoid superfluous watch checks (0 or 1; default %d).\n",supProp);
	printf("  --proof-log=arg  Set a filename for the proof logs (string).\n");
}

typedef bool (*func)(double);
template <class T>
void getOptionNum(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, func test, T& val){
	if (opt_val.count(option)) {
		double v = atof(opt_val.at(option).c_str());
		if (test(v)) val=v;
		else exit_ERROR({"Invalid value for ",option,": ",opt_val.at(option),".\nCheck usage with --help option."});
	}
}
void getOptionStr(const std::unordered_map<std::string, std::string>& opt_val, const std::string& option, std::string& val){
	if(opt_val.count(option)) val=opt_val.at(option);
}

std::string read_options(int argc, char**argv) {
	std::string filename;
	for(int i=1;i<argc;i++){
		if (!strcmp(argv[i], "--help")) {
			usage(argv[0]);
			exit(1);
		}
	}
	std::vector<std::string> opts={"print-sol","verbosity", "var-decay", "rinc", "rfirst", "original-rto", "opt-mode",
																"prop-counting", "prop-clause", "prop-card", "prop-idx", "prop-sup", "proof-log"};
	std::unordered_map<std::string, std::string> opt_val;
	for(int i=1;i<argc;i++){
		if (std::string(argv[i]).substr(0,2) != "--") filename = argv[i];
		else {
			bool found = false;
			for(std::string& key : opts) {
				if (std::string(argv[i]).substr(0,key.size()+3)=="--"+key+"=") {
					found = true;
					opt_val[key] = std::string(argv[i]).substr(key.size()+3);
				}
			}
			if (!found) exit_ERROR({"Unknown option: ",argv[i],".\nCheck usage with --help option."});
		}
	}
	getOptionNum(opt_val,"print-sol",[](double x)->bool{return x==0 || x==1;},print_sol);
	getOptionNum(opt_val,"verbosity",[](double)->bool{return true;},verbosity);
	getOptionNum(opt_val,"var-decay",[](double x)->bool{return x>=0.5 && x<1;},v_vsids_decay);
	getOptionNum(opt_val,"rinc",[](double x)->bool{return x>=1;},rinc);
	getOptionNum(opt_val,"rfirst",[](double x)->bool{return x>=1;},rfirst);
	getOptionNum(opt_val,"original-rto",[](double x)->bool{return x==0 || x==1;},originalRoundToOne);
	getOptionNum(opt_val,"opt-mode",[](double x)->bool{return x==0 || x==1 || x==2 || x==3 || x==4;},opt_mode);
	getOptionNum(opt_val,"prop-counting",[](double x)->bool{return x>=0 || x<=1;},countingProp);
	getOptionNum(opt_val,"prop-clause",[](double x)->bool{return x==0 || x==1;},clauseProp);
	getOptionNum(opt_val,"prop-card",[](double x)->bool{return x==0 || x==1;},cardProp);
	getOptionNum(opt_val,"prop-idx",[](double x)->bool{return x==0 || x==1;},idxProp);
	getOptionNum(opt_val,"prop-sup",[](double x)->bool{return x==0 || x==1;},supProp);
	std::string proof_log_name="";
	getOptionStr(opt_val,"proof-log",proof_log_name);
	if(!proof_log_name.empty()) logger=std::make_shared<Logger>(proof_log_name);
	return filename;
}

template<class SMALL, class LARGE>
LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core){
	LARGE slack = -core.getRhs();
	for(Var v: core.vars) if(assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v]>0)) slack+=core.coefs[v];
	return slack;
}

void extractCore(const IntSet& assumptions, CRef confl, intConstr& outCore, Lit l_assump=0){
	assert(confl!=CRef_Undef);

	if(l_assump!=0){ // l_assump is an assumption propagated to the opposite value
		assert(assumptions.has(l_assump));
		assert(isFalse(Level,l_assump));
		int pos = Pos[std::abs(l_assump)];
		while((int)trail.size()>pos) undoOne();
		assert(isUnknown(Pos,l_assump));
		decide(l_assump);
	}

	// Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
	// For this, we first copy the trail, then backjump to 0, then rebuild the trail.
	// Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
	std::vector<Lit> decisions; // holds the decisions
	decisions.reserve(decisionLevel());
	std::vector<Lit> props; // holds the propagations
	props.reserve(trail.size());
	assert(trail_lim.size()>0);
	for(int i=trail_lim[0]; i<(int)trail.size(); ++i){
		Lit l = trail[i];
		if(assumptions.has(l)) decisions.push_back(l);
		else props.push_back(l);
	}
	backjumpTo(0);

	for(Lit l: decisions) decide(l);
	for(Lit l: props) propagate(l,Reason[std::abs(l)]);

	ca[confl].toConstraint(conflConstraint);
	stats.NADDEDLITERALS+=conflConstraint.vars.size();
	conflConstraint.removeUnitsAndZeroes(Level,Pos);
	assert(conflConstraint.getSlack(Level)<0);

	// analyze conflict
	Val assumpslk = assumpSlack(assumptions,conflConstraint);
	while(assumpslk>=0){
		Lit l = trail.back();
		assert(std::abs(conflConstraint.getCoef(-l))<INF);
		Coef confl_coef_l = conflConstraint.getCoef(-l);
		if(confl_coef_l>0) {
			ca[Reason[std::abs(l)]].toConstraint(tmpConstraint);
			stats.NADDEDLITERALS+=tmpConstraint.vars.size();
			tmpConstraint.removeUnitsAndZeroes(Level,Pos);
			tmpConstraint.weakenNonImplying(Level,tmpConstraint.getCoef(l),tmpConstraint.getSlack(Level),stats); // NOTE: also saturates
			assert(tmpConstraint.getCoef(l)>tmpConstraint.getSlack(Level));
			Coef slk = tmpConstraint.getSlack(Level);
			if(slk>0){
				Coef div = slk+1;
				if(originalRoundToOne){ tmpConstraint.weaken(-(tmpConstraint.getCoef(l)%div),l); tmpConstraint.saturate(); }
				tmpConstraint.roundToOne(Level,div,!originalRoundToOne);
			}
			assert(tmpConstraint.getSlack(Level)<=0);
			Coef reason_coef_l = tmpConstraint.getCoef(l);
			Coef gcd_coef_l = aux::gcd(reason_coef_l,confl_coef_l);
			conflConstraint.addUp(Level,tmpConstraint,confl_coef_l/gcd_coef_l,reason_coef_l/gcd_coef_l);
			tmpConstraint.reset();
			assert(conflConstraint.getCoef(-l)==0);
			assert(conflConstraint.getSlack(Level)<0);
			assumpslk = assumpSlack(assumptions,conflConstraint);
		}
		assert(decisionLevel()==(int)decisions.size());
		undoOne();
	}
	assert(conflConstraint.getDegree()>0);
	assert(conflConstraint.getDegree()<INF);
	assert(conflConstraint.isSaturated());
	conflConstraint.copyTo(outCore);
	conflConstraint.reset();

	// weaken non-falsifieds
	for(Var v: outCore.vars) if(!assumptions.has(-outCore.getLit(v))) outCore.weaken(-outCore.coefs[v],v);
	outCore.postProcess(Level,Pos,true,stats);
	assert(assumpSlack(assumptions,outCore)<0);
	backjumpTo(0);
}

SolveState solve(const IntSet& assumptions, intConstr& out) {
	out.reset();
	backjumpTo(0); // ensures assumptions are reset
	std::vector<int> assumptions_lim={0};
	assumptions_lim.reserve((int)assumptions.size()+1);
	while (true) {
		CRef confl = runPropagation();
		if (confl != CRef_Undef) {
			if(decisionLevel() == 0){
				if(logger){
					ca[confl].toConstraint(logConstraint);
					logConstraint.logInconsistency(Level,Pos,stats);
					logConstraint.reset();
				}
				assert(getSlack(ca[confl])<0);
				exit_UNSAT();
			}
			vDecayActivity();
			cDecayActivity();
			stats.NCONFL++; nconfl_to_restart--;
			if(stats.NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10lld | #Constraints: %10lld\n",stats.NCONFL,(long long)constraints.size());
//					print_stats();
					if(verbosity>2){
						// memory usage
						std::cout<<"c total constraint space: "<<ca.cap*4/1024./1024.<<"MB"<<std::endl;
						std::cout<<"c total #watches: ";{long long cnt=0;for(Lit l=-n;l<=n;l++)cnt+=(long long)adj[l].size();std::cout<<cnt<<std::endl;}
					}
				}
			}

			if(decisionLevel()>=(int)assumptions_lim.size()){
				analyze(confl);
				learnConstraint(conflConstraint);
				conflConstraint.reset();
			}else{
				extractCore(assumptions,confl,out);
				return SolveState::UNSAT;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				backjumpTo(0);
				double rest_base = luby(rinc, ++stats.NRESTARTS);
				nconfl_to_restart = (long long) rest_base * rfirst;
				if(stats.NCONFL >= (stats.NCLEANUP+1)*nbconstrsbeforereduce) {
					++stats.NCLEANUP;
					reduceDB();
					while(stats.NCONFL >= stats.NCLEANUP*nbconstrsbeforereduce) nbconstrsbeforereduce += incReduceDB;
					return SolveState::INPROCESSING;
				}
			}
			Lit next = 0;
			if((int)assumptions_lim.size()>decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			if(assumptions_lim.back()<(int)assumptions.size()){
				for(int i=(decisionLevel()==0?0:trail_lim.back()); i<(int)trail.size(); ++i){
					Lit l = trail[i];
					if(assumptions.has(-l)){ // found conflicting assumption
						if(isUnit(Level,l)) backjumpTo(0), out.reset(); // negated assumption is unit
						else extractCore(assumptions,Reason[std::abs(l)],out,-l);
						return SolveState::UNSAT;
					}
				}
			}
			while(assumptions_lim.back()<(int)assumptions.size()){
				assert(decisionLevel()==(int)assumptions_lim.size()-1);
				Lit l_assump = assumptions.keys[assumptions_lim.back()];
				assert(!isFalse(Level,l_assump)); // otherwise above check should have caught this
				if (isTrue(Level,l_assump)){ // assumption already propagated
					++assumptions_lim.back();
				}else{ // unassigned assumption
					next = l_assump;
					assumptions_lim.push_back(assumptions_lim.back()+1);
					break;
				}
			}
			if(next==0) next = pickBranchLit();
			if(next==0){
				assert(order_heap.empty());
				for (Var v=1; v<=n; ++v) last_sol[v]=isTrue(Level,v);
				backjumpTo(0);
				return SolveState::SAT;
			}
			decide(next);
		}
	}
}

ID replaceExternal(CRef cr, ID old=0){
	if(old!=0){
		auto old_cr=external.find(old);
		assert(old_cr!=external.end());
		ca[old_cr->second].setStatus(FORCEDELETE);
		external.erase(old_cr);
	}
	if(cr==CRef_Undef) return 0;
	ID result = ca[cr].id;
	external[result]=cr;
	assert(ca[cr].getStatus()==LOCKED);
	return result;
}

inline void printObjBounds(Val lower, Val upper){
	if(foundSolution()) printf("c bounds %10lld >= %10lld\n",upper,lower);
	else printf("c bounds          - >= %10lld\n",lower);
}

ID handleNewSolution(const intConstr& origObj, ID& lastUpperBound){
	Val prev_val = last_sol_obj_val; _unused(prev_val);
	last_sol_obj_val = -origObj.getRhs();
	for(Var v: origObj.vars) last_sol_obj_val+=origObj.coefs[v]*last_sol[v];
	assert(last_sol_obj_val<prev_val);

	origObj.copyTo(tmpConstraint,true);
	tmpConstraint.addRhs(-last_sol_obj_val+1);
	CRef cr = addInputConstraint(tmpConstraint,false,true);
	tmpConstraint.reset();
	lastUpperBound = replaceExternal(cr,lastUpperBound);
	return ca[cr].id;
}

struct LazyVar{
	int mult; // TODO: add long long to int check?
	Val rhs;
	std::vector<Lit> lhs;
	std::vector<Var> introducedVars;
	ID atLeastID=0;
	ID atMostID=0;

	LazyVar(intConstr& core, Var startvar, int m):
		mult(m),rhs(core.getDegree()),introducedVars{startvar}{
		assert(core.isCardinality());
		lhs.reserve(core.vars.size());
		for(Var v: core.vars) lhs.push_back(core.getLit(v));
	}
	~LazyVar(){
		replaceExternal(CRef_Undef,atLeastID);
		replaceExternal(CRef_Undef,atMostID);
	}

	Var getCurrentVar() const { return introducedVars.back(); }
	void addVar(Var v) { introducedVars.push_back(v); }

	void addAtLeastConstraint(intConstr& out) const {
		// X >= k + y1 + ... + yi
		assert(out.isReset());
		out.addRhs(rhs);
		for(Lit l: lhs) out.addLhs(1,l);
		for(Var v: introducedVars) out.addLhs(-1,v);
		CRef cr = addInputConstraint(out,false,true);
		out.reset();
		replaceExternal(cr,atLeastID);
	}

	void addAtMostConstraint(intConstr& out) const {
		// X =< k + y1 + ... + yi-1 + (n-k-(i-1))yi
		assert(out.isReset());
		out.addRhs(-rhs);
		for(Lit l: lhs) out.addLhs(-1,l);
		for(Var v: introducedVars) out.addLhs(1,v);
		out.addLhs(lhs.size()-rhs-introducedVars.size(), getCurrentVar());
		CRef cr = addInputConstraint(out,false,true);
		out.reset();
		replaceExternal(cr,atMostID);
	}

	void addSymBreakingConstraint(intConstr& out, Var prevvar) const {
		// y-- + ~y >= 1 (equivalent to y-- >= y)
		assert(introducedVars.size()>1);
		assert(out.isReset());
		out.addRhs(1);
		out.addLhs(1,prevvar);
		out.addLhs(1,-getCurrentVar());
		addInputConstraint(out,false,true);
		out.reset();
	}
};

std::ostream & operator<<(std::ostream & o, const LazyVar* lv) {
	for(Var v: lv->introducedVars) o << v << " ";
	o << "| ";
	for(Lit l: lv->lhs) o << "+x" << l << " ";
	o << ">= " << lv->rhs;
	return o;
}

void checkLazyVariables(longConstr& reformObj, intConstr& core, std::vector<LazyVar*>& lazyVars){
	for(int i=0; i<(int)lazyVars.size(); ++i){
		LazyVar* lv=lazyVars[i];
		if(reformObj.getLit(lv->getCurrentVar())==0){
			// add auxiliary variable
			long long newN = n+1;
			setNbVariables(newN);
			reformObj.resize(newN+1);
			Var oldvar = lv->getCurrentVar();
			lv->addVar(newN);
			// reformulate the objective
			reformObj.addLhs(lv->mult,newN);
			// add necessary lazy constraints
			lv->addAtLeastConstraint(tmpConstraint);
			lv->addAtMostConstraint(tmpConstraint);
			lv->addSymBreakingConstraint(tmpConstraint,oldvar);
			if(lv->introducedVars.size()+lv->rhs==lv->lhs.size()){ aux::swapErase(lazyVars,i--); delete lv; continue; }
		}
	}
	core.resize(n+1);
}
ID addLowerBound(const intConstr& origObj, Val lowerBound, ID& lastLowerBound){
	origObj.copyTo(tmpConstraint);
	tmpConstraint.addRhs(lowerBound);
	CRef cr = addInputConstraint(tmpConstraint,false,true);
	tmpConstraint.reset();
	lastLowerBound = replaceExternal(cr,lastLowerBound);
	return ca[cr].id;
}
ID handleInconsistency(longConstr& reformObj, intConstr& core, Val& lower_bound,
                         std::vector<LazyVar*>& lazyVars, const intConstr& origObj, ID& lastLowerBound){
	// take care of derived unit lits and remove zeroes
	reformObj.removeUnitsAndZeroes(Level,Pos,false);
	Val prev_lower = lower_bound; _unused(prev_lower);
	lower_bound = -reformObj.getDegree();
	if(core.getDegree()==0){ // apparently only unit assumptions were derived
		assert(lower_bound>prev_lower);
		checkLazyVariables(reformObj,core,lazyVars);
		return addLowerBound(origObj,lower_bound,lastLowerBound);
	}
	// figure out an appropriate core
	core.simplifyToCardinality(false);

	// adjust the lower bound
	if(core.getDegree()>1) ++stats.NCORECARDINALITIES;
	long long mult = INF;
	for(Var v: core.vars){
		assert(reformObj.getLit(v)!=0);
		mult=std::min<long long>(mult,std::abs(reformObj.coefs[v]));
	}
	assert(mult<INF); assert(mult>0);
	lower_bound+=core.getDegree()*mult;

	if((opt_mode==2 || opt_mode==4) && core.vars.size()-core.getDegree()>1){
		// add auxiliary variable
		long long newN = n+1;
		setNbVariables(newN);
		core.resize(newN+1);
		reformObj.resize(newN+1);
		// reformulate the objective
		core.copyTo(tmpConstraint,true);
		reformObj.addUp(Level,tmpConstraint,mult,1,false);
		tmpConstraint.reset();
		reformObj.addLhs(mult,newN); // add only one variable for now
		assert(lower_bound==-reformObj.getDegree());
		// add first lazy constraint
		LazyVar* lv = new LazyVar(core,newN,mult);
		lazyVars.push_back(lv);
		lv->addAtLeastConstraint(tmpConstraint);
		lv->addAtMostConstraint(tmpConstraint);
	}else{
		// add auxiliary variables
		long long oldN = n;
		long long newN = oldN-core.getDegree()+core.vars.size();
		setNbVariables(newN);
		core.resize(newN+1);
		reformObj.resize(newN+1);
		// reformulate the objective
		for(Var v=oldN+1; v<=newN; ++v) core.addLhs(-1,v);
		core.copyTo(tmpConstraint,true);
		reformObj.addUp(Level,tmpConstraint,mult,1,false);
		assert(lower_bound==-reformObj.getDegree());
		// add channeling constraints
		addInputConstraint(tmpConstraint,false,true);
		tmpConstraint.reset();
		core.copyTo(tmpConstraint);
		addInputConstraint(tmpConstraint,false,true);
		tmpConstraint.reset();
		for(Var v=oldN+1; v<newN; ++v){ // add symmetry breaking constraints
			assert(tmpConstraint.isReset());
			tmpConstraint.addRhs(1);
			tmpConstraint.addLhs(1,v);
			tmpConstraint.addLhs(1,-v-1);
			addInputConstraint(tmpConstraint,false,true);
			tmpConstraint.reset();
		}
	}
	checkLazyVariables(reformObj,core,lazyVars);
	return addLowerBound(origObj,lower_bound,lastLowerBound);
}

void optimize(intConstr& origObj, intConstr& core){
	assert(origObj.vars.size() > 0);
	// NOTE: -origObj.getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
	origObj.removeUnitsAndZeroes(Level,Pos,false);
	Val lower_bound = -origObj.getDegree();

	Val opt_coef_sum = 0;
	for (Var v: origObj.vars) opt_coef_sum+=std::abs(origObj.coefs[v]);
	if (opt_coef_sum >= (Val)INF) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."}); // TODO: remove restriction

	longConstr reformObj;
	origObj.copyTo(reformObj);
	ID origUpperBound = 0;
	ID origLowerBound = 0;
	ID lastUpperBound = 0;
	ID lastLowerBound = 0;

	IntSet assumps;
	std::vector<LazyVar*> lazyVars;
	size_t upper_time=0, lower_time=0;
	SolveState reply = SolveState::UNSAT;
	while(true){
		size_t current_time=stats.getDetTime();
		if(reply!=SolveState::INPROCESSING) printObjBounds(lower_bound,last_sol_obj_val);
		assumps.reset();
		if(opt_mode==1 || opt_mode==2 || (opt_mode>2 && lower_time<upper_time)){ // use core-guided step
			reformObj.removeZeroes();
			for(Var v: reformObj.vars) { assert(reformObj.getLit(v)!=0); assumps.add(-reformObj.getLit(v)); }
			std::sort(assumps.keys.begin(),assumps.keys.end(),[&](Lit l1,Lit l2){
				return reformObj.getCoef(-l1)>reformObj.getCoef(-l2) ||
				       (reformObj.getCoef(-l1)==reformObj.getCoef(-l2) && std::abs(l1)<std::abs(l2));
			});
		}
		assert(last_sol_obj_val>lower_bound);
		reply = solve(assumps,core);
		assert(decisionLevel()==0);
		if(assumps.size()==0) upper_time+=stats.getDetTime()-current_time;
		else lower_time+=stats.getDetTime()-current_time;
		if(reply==SolveState::SAT){
			++stats.NSOLS;
			origUpperBound = handleNewSolution(origObj,lastUpperBound);
			assert((opt_mode!=1 && opt_mode!=2) || lower_bound==last_sol_obj_val);
		}	else if(reply==SolveState::UNSAT) {
			++stats.NCORES;
			if(core.getSlack(Level)<0){
				if(logger) core.logInconsistency(Level,Pos,stats);
				assert(decisionLevel()==0);
				exit_UNSAT();
			}
			origLowerBound = handleInconsistency(reformObj,core,lower_bound,lazyVars,origObj,lastLowerBound);
		} // else reply==SolveState::INPROCESSING, keep looping
		if(lower_bound>=last_sol_obj_val){
			printObjBounds(lower_bound,last_sol_obj_val);
			assert(lastUpperBound>0);
			assert(lastLowerBound>0);
			if(logger){
				longConstr coreAggregate;
				coreAggregate.initializeLogging(logger);
				coreAggregate.resize(n+1);
				origObj.copyTo(tmpConstraint,true);
				tmpConstraint.addRhs(1-last_sol_obj_val);
				tmpConstraint.resetBuffer(origUpperBound-1); // -1 to get the unprocessed formula line
				coreAggregate.addUp(Level,tmpConstraint,1,1,false);
				tmpConstraint.reset();
				origObj.copyTo(tmpConstraint);
				tmpConstraint.addRhs(lower_bound);
				tmpConstraint.resetBuffer(origLowerBound-1); // -1 to get the unprocessed formula line
				coreAggregate.addUp(Level,tmpConstraint,1,1,false);
				tmpConstraint.reset();
				assert(coreAggregate.getSlack(Level)<0);
				assert(decisionLevel()==0);
				coreAggregate.logInconsistency(Level,Pos,stats);
			}
			exit_UNSAT();
		}
	}
}

int main(int argc, char**argv){
	initial_time = aux::cpuTime();
	init();
	intConstr objective;
	intConstr inconsistency;

	signal(SIGINT, SIGINT_exit);
	signal(SIGTERM,SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);

	std::string filename = read_options(argc, argv);
	tmpConstraint.initializeLogging(logger);
	conflConstraint.initializeLogging(logger);
	logConstraint.initializeLogging(logger);
	inconsistency.initializeLogging(logger);

	if (!filename.empty()) {
		std::ifstream fin(filename);
		if (!fin) exit_ERROR({"Could not open ",filename});
		file_read(fin,objective);
	} else {
		if (verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
		file_read(std::cin,objective);
	}
	if(logger) logger->formula_out << "* INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW\n";
	std::cout << "c #variables=" << orig_n << " #constraints=" << constraints.size() << std::endl;

	signal(SIGINT, SIGINT_interrupt);
	signal(SIGTERM,SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);

	if(objective.vars.size() > 0) optimize(objective,inconsistency);
	else while(true){
		SolveState reply = solve({},inconsistency);
		if(reply==SolveState::SAT) exit_SAT();
		else if(reply==SolveState::UNSAT){
			if(logger) inconsistency.logInconsistency(Level,Pos,stats);
			assert(decisionLevel()==0);
			assert(inconsistency.getSlack(Level)<0);
			exit_UNSAT();
		}
	}
}
