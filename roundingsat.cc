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

#define _unused(x) ((void)(x)) // marks variables unused in release mode

template<class T, class U>
std::ostream& operator<<(std::ostream& os, const std::pair<T,U>& p){ os << p.first << "," << p.second; return os; }
template<class T, class U>
std::ostream& operator<<(std::ostream& os, const std::unordered_map<T,U>& m){
	for(const auto& e: m) os<<e<<";";
	return os;
}
std::ostream& operator<<(std::ostream& os, __int128 x){
	if(x<0){ os << "-"; x = -x; }
	uint64_t tenPow18 = 1000000000000000000;
	uint64_t x1 = x%tenPow18; x/=tenPow18;
	if(x>0){
		uint64_t x2 = x%tenPow18; x/=tenPow18;
		if(x>0) os << (unsigned short) (x%tenPow18);
		os << x2;
	}
	return os << x1;
}

namespace std {
	template<> class numeric_limits<__int128> {
	public:
		static __int128 max() {
			__int128 x;
			x = 170141183460469;
			x*=1000000000000000;
			x+= 231731687303715;
			x*=1000000000;
			x+= 884105727;
			return x; // which is 2^127-1
		};
		static __int128 min() {return -max()+1; };
		const  static bool is_specialized = true;
	};
}

template<class T> inline void swapErase(T& indexable, size_t index){
	indexable[index]=indexable.back();
	indexable.pop_back();
}

template<class T, class U> inline bool contains(const T& v, const U& x){
	return std::find(v.cbegin(),v.cend(),x)!=v.cend();
}

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

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
static inline double cpuTime() {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

// ---------------------------------------------------------------------
// Typedefs
using ID=uint64_t;
using Var=int;
using Lit=int;
using Coef=int;

// ---------------------------------------------------------------------
// Global variables

const int resize_factor=2;
const Coef INF=1e9+1;

double initial_time;
long long NTRAILPOPS=0, NWATCHLOOKUPS=0, NWATCHCHECKS=0, NADDEDLITERALS=0;
long long NCONFL=0, NDECIDE=0, NPROP=0, NPROPCLAUSE=0;
inline long long getDetTime(){ return 1+NADDEDLITERALS+NWATCHLOOKUPS+NWATCHCHECKS+NPROP+NTRAILPOPS+NDECIDE; }
__int128 LEARNEDLENGTHSUM=0, LEARNEDDEGREESUM=0;
long long NCLAUSESLEARNED=0, NCARDINALITIESLEARNED=0, NGENERALSLEARNED=0;
long long NGCD=0, NCARDDETECT=0, NCORECARDINALITIES=0, NCORES=0, NSOLS=0;
long long NWEAKENEDNONIMPLYING=0, NWEAKENEDNONIMPLIED=0;
double rinc=2;
long long rfirst=100;
long long nbconstrsbeforereduce=2000;
long long incReduceDB=300;
long long cnt_reduceDB=0;
bool originalRoundToOne=false;
int opt_mode=4;
long long curr_restarts=0;
long long nconfl_to_restart=0;
bool print_sol = false;
std::string proof_log_name;
bool logProof(){ return !proof_log_name.empty(); }
std::ofstream proof_out; std::ofstream formula_out;
ID last_proofID = 0; ID last_formID = 0;
std::vector<ID> unitIDs;
long long logStartTime=0;
unsigned int prop_mode=2;
inline bool countingProp(){ return prop_mode & 1; }
inline bool clauseProp(){ return prop_mode & 2; }
inline bool puebloProp(){ return prop_mode & 4; }

struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };
std::ostream& operator<<(std::ostream& os, CRef cr) { return os << cr.ofs; }

int verbosity = 1;
Var n = 0;
Var orig_n = 0;
std::vector<CRef> constraints;
std::unordered_map<ID,CRef> external;
struct Watch {
	CRef cref;
	int idx; // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
	Watch(CRef cr, int i):cref(cr),idx(i){};
	bool operator==(const Watch& other)const{return other.cref==cref && other.idx==idx;}
};

std::vector<std::vector<Watch>> _adj={{}}; std::vector<std::vector<Watch>>::iterator adj;
std::vector<int> _Level={-1}; std::vector<int>::iterator Level;
inline bool isTrue(Lit l){ return ~Level[l]; }
inline bool isFalse(Lit l){ return ~Level[-l]; }
inline bool isUnit(Lit l){ return Level[l]==0; }
std::vector<Lit> trail;
std::vector<int> trail_lim, Pos;
inline bool isUnknown(Lit l){ return Pos[std::abs(l)]==-1; }
std::vector<CRef> Reason;
int qhead; // for unit propagation
int last_sol_obj_val = INF;
inline bool foundSolution(){return last_sol_obj_val<INF;}
std::vector<bool> last_sol;
std::vector<Lit> phase;
inline void newDecisionLevel() { trail_lim.push_back(trail.size()); }
inline int decisionLevel() { return trail_lim.size(); }

enum DeletionStatus { LOCKED, UNLOCKED, FORCEDELETE, MARKEDFORDELETE };
enum WatchStatus { FOUNDNEW, FOUNDNONE, CONFLICTING };

void propagate(Lit p, CRef from);
struct Constr;
std::ostream & operator<<(std::ostream & o, const Constr& C);
int sz_constr(int length);
struct Constr {
	ID id;
	float act;
	Coef degree;
	// NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
	struct {
		unsigned original     : 1;
		unsigned learnt       : 1;
		unsigned lbd          : 30;
		unsigned status       : 2;
		unsigned size         : 30;
	} header;
	long long ntrailpops;
	long long slack; // sum of non-falsified watches minus w.
	// NOTE: will never be larger than 2 * non-falsified watch, so fits in 32 bit for the n-watched literal scheme
	// TODO: is above really true? Definitely not for counting propagation...
	unsigned int watchIdx;
	int data[];

	inline bool isClause() const { return (int)watchIdx==-1; }
	inline int getMemSize() const { return sz_constr(size()+(isClause()?0:size())); }
	inline unsigned int size() const { return header.size; }
	inline void setStatus(DeletionStatus ds){ header.status=(unsigned int) ds; }
	inline DeletionStatus getStatus() const { return (DeletionStatus) header.status; }
	inline void setLBD(unsigned int lbd){ header.lbd=std::min(header.lbd,lbd); }
	inline unsigned int lbd() const { return header.lbd; }
	inline bool original() const { return header.original; }
	inline bool learnt() const { return header.learnt; }
	inline Coef largestCoef() const { return std::abs(data[0]); }
	inline Coef coef(unsigned int i) const { return isClause()?1:std::abs(data[i<<1]); }
	inline Lit lit(unsigned int i) const { return isClause()?data[i]:data[(i<<1)+1]; }
	inline bool isWatched(unsigned int i) const { assert(i%2==0); return data[i]<0; }
	inline void undoFalsified(int i) {
		assert(!isClause());
		assert(i>=0);
		assert(i%2==0);
		assert(countingProp() || isWatched(i));
		assert(isFalse(data[i+1]));
		++NWATCHLOOKUPS;
		slack += abs(data[i]); // TODO: slack -= data[i] when only watched propagation
	}
	inline WatchStatus propagateWatch(CRef cr, int& idx, Lit p){
		assert(isFalse(p));
		++NWATCHLOOKUPS;

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
			if(isTrue(otherwatch)){
				idx=otherwatch-INF; // set new blocked literal
				return WatchStatus::FOUNDNONE; // constraint is satisfied
			}
			const int Csize=size();
			int i=2;
			for(int i=2; i<Csize; ++i){
				Lit l = data[i];
				if(!isFalse(l)){
					int mid = i/2+1;
					data[i]=data[mid];
					data[mid]=watch;
					data[widx]=l;
					adj[l].emplace_back(cr,otherwatch-INF);
					NWATCHCHECKS+=i-2;
					return WatchStatus::FOUNDNEW;
				}
			}
			NWATCHCHECKS+=i-2;
			assert(isFalse(watch));
			if(!isFalse(otherwatch)){
				for(int i=2; i<Csize; ++i) assert(isFalse(data[i]));
				++NPROPCLAUSE;
				propagate(otherwatch,cr);
				return WatchStatus::FOUNDNONE;
			}else{
				for(int i=0; i<Csize; ++i) assert(isFalse(data[i]));
				return WatchStatus::CONFLICTING;
			}
		}

		assert(idx>=0);
		assert(idx%2==0);
		const unsigned int Csize2 = 2*size(); const Coef ClargestCoef = largestCoef();
		const Coef c = data[idx];

		if(countingProp()){ // use counting propagation
			slack-=c;
			if(slack<0) return WatchStatus::CONFLICTING;
			if(slack<ClargestCoef){
				if(puebloProp() || ntrailpops<NTRAILPOPS){ ntrailpops=NTRAILPOPS; watchIdx=0; }
				NWATCHCHECKS-=watchIdx;
				for(; watchIdx<Csize2 && data[watchIdx]>slack; watchIdx+=2){
					const Lit l = data[watchIdx+1];
					if(isUnknown(l)) { NPROPCLAUSE+=(degree==1); propagate(l,cr); }
				}
				NWATCHCHECKS+=watchIdx;
			}
			return WatchStatus::FOUNDNONE;
		}

		// use watched propagation
		if(puebloProp() || ntrailpops<NTRAILPOPS){ ntrailpops=NTRAILPOPS; watchIdx=0; }
		assert(c<0);
		slack+=c;
		if(puebloProp() || slack-c>=ClargestCoef){ // look for new watches if previously, slack was at least ClargestCoef
			NWATCHCHECKS-=watchIdx;
			for(; watchIdx<Csize2 && slack<ClargestCoef; watchIdx+=2){ // NOTE: first innermost loop of RoundingSat
				const Coef cf = data[watchIdx];
				const Lit l = data[watchIdx+1];
				if(cf>0 && !isFalse(l)){
					slack+=cf;
					data[watchIdx]=-cf;
					adj[l].emplace_back(cr,watchIdx);
				}
			}
			NWATCHCHECKS+=watchIdx;
			if(slack<ClargestCoef){ assert(watchIdx==Csize2); watchIdx=0; }
		} // else we did not find enough watches last time, so we can skip looking for them now

		if(slack>=ClargestCoef){
			data[idx]=-c;
			return WatchStatus::FOUNDNEW;
		}else if(slack>=0){ // keep the watch, check for propagation
			for(; watchIdx<Csize2 && std::abs(data[watchIdx])>slack; watchIdx+=2){ // NOTE: second innermost loop of RoundingSat
				const Lit l = data[watchIdx+1];
				if(isUnknown(l)){ NPROPCLAUSE+=(degree==1); propagate(l,cr); }
			}
			return WatchStatus::FOUNDNONE;
		}else return WatchStatus::CONFLICTING;
	}
};

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

template <class T>
inline T ceildiv(const T& p,const T& q){ assert(q>0); assert(p>=0); return (p+q-1)/q; } // NOTE: potential overflow
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

template<class T>
inline std::string proofMult(T mult){
	return (mult==1?"":std::to_string(mult)+" * ");
}

template<class SMALL, class LARGE> // LARGE should be able to fit sums of SMALL
struct Constraint{
	LARGE degree = 0;
	LARGE rhs = 0;
	std::vector<Var> vars;
	std::vector<SMALL> coefs;
	std::stringstream proofBuffer;
	static constexpr SMALL _unused_(){ return std::numeric_limits<SMALL>::max(); }
	static constexpr LARGE _invalid_(){ return std::numeric_limits<LARGE>::min(); }

	Constraint(){
		assert(std::numeric_limits<SMALL>::is_specialized);
		assert(std::numeric_limits<LARGE>::is_specialized);
		reset();
	}

	inline void resize(size_t s){ if(s>coefs.size()) coefs.resize(s,_unused_()); }

	void resetBuffer(ID proofID){
		proofBuffer.clear();
		proofBuffer.str(std::string());
		proofBuffer << proofID << " ";
	}

	bool isReset() const { return vars.size()==0 && rhs==0; }
	void reset(){
		for(Var v: vars) coefs[v]=_unused_();
		vars.clear();
		rhs=0; degree = 0;
		if(logProof()) resetBuffer(1); // NOTE: proofID 1 equals the constraint 0 >= 0
	}

	void init(const Constr& C){
		assert(isReset()); // don't use a Constraint used by other stuff
		addRhs(C.degree);
		for(size_t i=0;i<C.size();++i){ assert(C.coef(i)!=0); addLhs(C.coef(i), C.lit(i)); }
		degree=C.degree;
		if(logProof()) resetBuffer(C.id);
	}

	inline void addRhs(LARGE r){ rhs+=r; if(degree!=_invalid_()) degree+=r; }
	inline LARGE getRhs() const { return rhs; }
	inline LARGE getDegree() {
		if(degree!=_invalid_()) return degree;
		degree = rhs;
		for (Var v: vars) degree -= std::min<SMALL>(0,coefs[v]); // considering negative coefficients
		return degree;
	}
	inline SMALL getCoef(Lit l) const {
		assert(std::abs(l)<coefs.size());
		return coefs[std::abs(l)]==_unused_()?0:(l<0?-coefs[-l]:coefs[l]);
	}
	inline Lit getLit(Lit l) const { // NOTE: answer of 0 means coef 0 or not in vars
		Var v = std::abs(l);
		if(v>=(Var)coefs.size()) return 0;
		SMALL c = coefs[v];
		if(c==0 || c==_unused_()) return 0;
		else if(c<0) return -v;
		else return v;
	}
	inline bool falsified(Var v) const {
		assert(v>0);
		assert((getLit(v)!=0 && !isFalse(getLit(v)))==(coefs[v]>0 && !isFalse(v)) || (coefs[v]<0 && !isTrue(v)));
		return ((coefs[v]>0 && isFalse(v)) || (coefs[v]<0 && isTrue(v)));
	}
	LARGE getSlack() const {
		LARGE slack = -rhs;
		for(Var v: vars) if(isTrue(v) || (!isFalse(v) && coefs[v]>0)) slack+=coefs[v];
		return slack;
	}

	// NOTE: erasing variables with coef 0 in addLhs would lead to invalidated iteration (e.g., for loops that weaken)
	void addLhs(SMALL c, Lit l){ // treats negative literals as 1-v
		assert(l!=0);
		degree=_invalid_();
		Var v = l;
		if(l<0){ rhs -= c; c = -c; v = -l; }
		assert(v<(Var)coefs.size());
		if(coefs[v]==_unused_()) vars.push_back(v), coefs[v]=0;
		coefs[v]+=c;
	}
	inline void weaken(SMALL m, Lit l){ // add m*(l>=0) if m>0 and -m*(-l>=-1) if m<0
		if(m==0) return;
		if(logProof()){
			if(m>0) proofBuffer << (l<0?"~x":"x") << std::abs(l) <<  " " << proofMult(m) << "+ ";
			else proofBuffer << (l<0?"x":"~x") << std::abs(l) <<  " " << proofMult(-m) << "+ ";
		}
		addLhs(m,l); // resets degree // TODO: optimize this method by not calling addLhs
		if(m<0) addRhs(m);
	}

	// @post: preserves order of vars
	void removeUnitsAndZeroes(bool doSaturation=true){
		if(logProof()){
			for(Var v: vars){
				Lit l = getLit(v); SMALL c = getCoef(l);
				if(isUnit(l)) proofBuffer << (l<0?"x":"~x") << v << " " << proofMult(c) << "+ ";
				else if (isUnit(-l)) proofBuffer << unitIDs[Pos[v]] << " " << proofMult(c) << "+ ";
			}
		}
		int j=0;
		for(int i=0; i<(int)vars.size(); ++i){
			Var v=vars[i];
			SMALL c=coefs[v];
			if(c==0) coefs[v]=_unused_();
			else if(isUnit(v)){
				rhs-=c;
				if(degree!=_invalid_() && c>0) degree-=c;
				coefs[v]=_unused_();
			}else if(isUnit(-v)){
				if(degree!=_invalid_() && c<0) degree+=c;
				coefs[v]=_unused_();
			}else vars[j++]=v;
		}
		vars.resize(j);
		if(doSaturation) saturate();
	}
	bool hasNoUnits() const {
		for(Var v: vars) if(isUnit(v) || isUnit(-v)) return false;
		return true;
	}

	// @post: mutates order of vars
	void removeZeroes() {
		for(int i=0; i<(int)vars.size(); ++i){
			Var v=vars[i];
			if(coefs[v]==0){
				coefs[v]=_unused_();
				swapErase(vars,i--);
			}
		}
	}
	bool hasNoZeroes() const {
		for(Var v: vars) if(coefs[v]==0) return false;
		return true;
	}

	// @post: preserves order of vars
	void saturate(const std::vector<Var>& vs){
		if(logProof() && !isSaturated()) proofBuffer << "s "; // log saturation only if it modifies the constraint
		LARGE w = getDegree();
		if(w<=0){ // NOTE: does not call reset(0), as we do not want to reset the buffer
			for(Var v: vars) coefs[v]=_unused_();
			vars.clear(); rhs=0; degree=0;
			return;
		}
		for (Var v: vs){
			if(coefs[v]<-w) rhs-=coefs[v]+w, coefs[v]=-w;
			else coefs[v]=std::min<LARGE>(coefs[v],w);
		}
		assert(isSaturated());
	}
	void saturate(){ saturate(vars); }
	bool isSaturated() {
		LARGE w = getDegree();
		for(Var v:vars) if(std::abs(coefs[v])>w) return false;
		return true;
	}

	template<class S, class L>
	void copyTo(Constraint<S,L>& out, bool inverted=false) const {
		assert(out.isReset());
		int mult=(inverted?-1:1);
		out.rhs=mult*rhs;
		out.vars=vars;
		out.resize(coefs.size());
		for(Var v: vars) out.coefs[v]=mult*coefs[v];
		if(inverted || degree==_invalid_()) out.degree=out._invalid_();
		else out.degree=degree;
		if(logProof()){
			out.proofBuffer.str(std::string());
			out.proofBuffer << proofBuffer.str() << proofMult(mult);
		}
	}

	template<class S, class L>
	void add(Constraint<S,L>& c, SMALL mult=1, bool saturateAndReduce=true){
		assert(!saturateAndReduce || isSaturated());
		assert(c._unused_()<=_unused_()); // don't add large stuff into small stuff
		assert(mult>=0);
		if(logProof()) proofBuffer << c.proofBuffer.str() << proofMult(mult) << "+ ";
		LARGE old_degree = getDegree();
		degree+=(LARGE)mult*(LARGE)c.getDegree();
		rhs+=(LARGE)mult*(LARGE)c.getRhs();
		for(Var v: c.vars){
			assert(v<(Var)coefs.size());
			assert(v>0);
			SMALL val = mult*c.coefs[v];
			if(coefs[v]==_unused_()){
				vars.push_back(v);
				coefs[v]=val;
			}else{
				SMALL cf = coefs[v];
				if((cf<0)!=(val<0)) degree -= std::min(std::abs(cf),std::abs(val));
				coefs[v]=cf+val;
			}
		}
		if(!saturateAndReduce) return;
		if(old_degree>getDegree()){ NADDEDLITERALS+=vars.size(); removeZeroes(); saturate(); }
		else{ NADDEDLITERALS+= c.vars.size(); saturate(c.vars); } // only saturate changed vars
		if(getDegree() > (LARGE)1e9){ removeZeroes(); roundToOne(ceildiv<LARGE>(getDegree(), 1e9), !originalRoundToOne); }
		assert(getDegree() <= (LARGE)1e9);
		assert(isSaturated());
	}

	void roundToOne(const SMALL d, bool partial){
		assert(isSaturated());
		assert(d>0);
		if(d==1) return;
		for(Var v:vars){
			assert(!isUnit(-v));
			assert(!isUnit( v));
			if(coefs[v]%d!=0){
				if(!falsified(v)){
					if(partial) weaken(-coefs[v]%d,v); // partial weakening
					else weaken(-coefs[v],v);
				}else{
					assert((!isTrue(v))==(coefs[v]>0));
					if(coefs[v]<0){
						SMALL weakening = d+(coefs[v]%d);
						coefs[v]-=weakening;
						rhs-=weakening;
					}else coefs[v]+=d-(coefs[v]%d);
				}
			}
			assert(coefs[v]%d==0);
			coefs[v]/=d;
		}
		// NOTE: as all coefficients are divisible by d, we can ceildiv the rhs instead of the degree
		rhs=ceildiv_safe<LARGE>(rhs,d);
		degree=_invalid_();
		saturate(); // NOTE: needed, as weakening can change degree significantly
		if(logProof()) proofBuffer << d << " d s ";
	}

	bool divideByGCD(){
		assert(isSaturated());
		assert(isSortedInDecreasingCoefOrder());
		assert(hasNoZeroes());
		if(vars.size()==0) return false;
		if(std::abs(coefs[vars[0]])>1e9) return false; // TODO: large coefs currently unsupported
		unsigned int _gcd = std::abs(coefs[vars.back()]);
		for(Var v: vars){
			_gcd = gcd(_gcd,(unsigned int) std::abs(coefs[v]));
			if(_gcd==1) return false;
		}
		assert(_gcd>1); assert(_gcd<(unsigned int)INF);
		for (Var v: vars) coefs[v] /= (Coef)_gcd;
		// NOTE: as all coefficients are divisible, we can ceildiv the rhs instead of the degree
		rhs=ceildiv_safe<LARGE>(rhs,_gcd);
		if(degree!=_invalid_()) degree=ceildiv_safe<LARGE>(degree,_gcd);
		if(logProof()) proofBuffer << _gcd << " d ";
		return true;
	}

	// NOTE: only equivalence preserving operations!
	void postProcess(bool sortFirst){
		removeUnitsAndZeroes(); // NOTE: also saturates
		if(sortFirst) sortInDecreasingCoefOrder();
		if(divideByGCD()) ++NGCD;
		if(simplifyToCardinality(true)) ++NCARDDETECT;
	}

	bool falsifiedCurrentLvlIsOne() const {
		bool result = false;
		for(int i=0; i<(int)vars.size(); ++i){
			Var v = vars[i];
			if((coefs[v]>0 && Level[-v]==decisionLevel()) || (coefs[v]<0 && Level[v]==decisionLevel())){
				if(result) return false;
				else result=true;
			}
		}
		return result;
	}

	// @return: earliest decision level that propagates a variable
	int getAssertionLevel() const {
		assert(getSlack()<0);
		if(decisionLevel()==0) return 0;

		// calculate slack at level -1
		LARGE slack = -rhs;
		for(Var v: vars) if(coefs[v]>0) slack+=coefs[v];
		if(slack<0) return 0;

		assert(hasNoZeroes());
		assert(isSortedInDecreasingCoefOrder());

		// create useful datastructures
		std::vector<Lit> litsByPos;
		litsByPos.reserve(vars.size());
		for(Var v: vars){
			Lit l = getLit(v); assert(l!=0);
			if(isFalse(l)) litsByPos.push_back(-l);
		}
		std::sort(litsByPos.begin(),litsByPos.end(),[&](Lit l1,Lit l2){ return Pos[std::abs(l1)]<Pos[std::abs(l2)]; });

		// calculate earliest propagating decision level by decreasing slack one decision level at a time
		auto posIt = litsByPos.cbegin();
		auto coefIt = vars.cbegin();
		int assertionLevel = 0;
		while(true){
			while(posIt!=litsByPos.cend() && Level[*posIt]<=assertionLevel){
				slack-=std::abs(coefs[std::abs(*posIt)]);
				++posIt;
			}
			if(slack<0){ assertionLevel=std::max(assertionLevel-1,0); break; }
			while((unsigned int)assertionLevel>=(unsigned int)Level[getLit(*coefIt)]) ++coefIt;
			// NOTE: unsigned int cast ensures assertionLevel < -1
			assert(coefIt!=vars.cend());
			if(slack<std::abs(coefs[*coefIt])) break;
			++assertionLevel;
		}
		assert(assertionLevel<decisionLevel());
		return assertionLevel;
	}

	// @post: preserves order after removeZeroes()
	void weakenNonImplied(LARGE slack){
		for(Var v: vars) if(coefs[v]!=0 && std::abs(coefs[v])<=slack && !falsified(v)){
			weaken(-coefs[v],v);
			++NWEAKENEDNONIMPLIED;
		}
	}
	// @post: preserves order after removeZeroes()
	bool weakenNonImplying(SMALL propCoef, LARGE slack){
		assert(hasNoZeroes());
		assert(isSortedInDecreasingCoefOrder());
		long long oldCount = NWEAKENEDNONIMPLYING;
		for(int i=vars.size()-1; i>=0 && slack+std::abs(coefs[vars[i]])<propCoef; --i){
			Var v = vars[i];
			if(falsified(v)){
				SMALL c = coefs[v];
				slack+=std::abs(c);
				weaken(-c,v);
				++NWEAKENEDNONIMPLYING;
			}
		}
		bool changed = oldCount!=NWEAKENEDNONIMPLYING;
		if(changed) saturate();
		return changed;
	}
	// @post: preserves order after removeZeroes()
	void heuristicWeakening(LARGE slk){
		if (slk<0) return; // no propagation, no idea what to weaken
		assert(isSortedInDecreasingCoefOrder());
		Var v_prop = -1;
		for(int i=vars.size()-1; i>=0; --i){
			Var v = vars[i];
			if(std::abs(coefs[v])>slk && isUnknown(v)){ v_prop=v; break; }
		}
		if(v_prop==-1) return; // no propagation, no idea what to weaken
		if(weakenNonImplying(std::abs(coefs[v_prop]),slk)) slk = getSlack(); // slack changed
		assert(getSlack()<std::abs(coefs[v_prop]));
		weakenNonImplied(slk);
	}

	// @post: preserves order of vars
	bool simplifyToCardinality(bool equivalencePreserving){
		assert(isSaturated());
		assert(isSortedInDecreasingCoefOrder());
		assert(hasNoZeroes());
		if(vars.size()==0 || std::abs(coefs[vars[0]])==1) return false; // already cardinality
		const LARGE w = getDegree();
		if(w<=0) return false;

		int largeCoefsNeeded=0;
		LARGE largeCoefSum=0;
		while(largeCoefsNeeded<(int)vars.size() && largeCoefSum<w){
			largeCoefSum+=std::abs(coefs[vars[largeCoefsNeeded]]);
			++largeCoefsNeeded;
		}
		assert(largeCoefsNeeded>0);
		if(largeCoefSum<w){
			for(Var v: vars) weaken(-coefs[v],v);
			return true; // trivial inconsistency
		}

		int skippable=vars.size(); // counting backwards
		if(equivalencePreserving){
			LARGE smallCoefSum=0;
			for(int i=1; i<=largeCoefsNeeded; ++i) smallCoefSum+=std::abs(coefs[vars[vars.size()-i]]);
			if(smallCoefSum<w) return false;
			// else, we have an equivalent cardinality constraint
		}else{
			LARGE wiggleroom=w-largeCoefSum+std::abs(coefs[vars[largeCoefsNeeded-1]]);
			assert(wiggleroom>0);
			while(skippable>0 && wiggleroom>std::abs(coefs[vars[skippable-1]])){
				--skippable;
				wiggleroom-=std::abs(coefs[vars[skippable]]);
			}
		}
		assert(skippable>=largeCoefsNeeded);

		if(logProof()){
			SMALL div_coef = std::abs(coefs[vars[largeCoefsNeeded-1]]);
			for(int i=0; i<largeCoefsNeeded; ++i){ // partially weaken large vars
				Lit l = getLit(vars[i]);
				SMALL d = getCoef(l)-div_coef;
				proofBuffer << (l>0?"~x":"x") << std::abs(l) << " " << proofMult(d) << "+ ";
			}
			for(int i=skippable; i<(int)vars.size(); ++i){ // weaken small vars
				Lit l = getLit(vars[i]);
				SMALL d = getCoef(l);
				proofBuffer << (l>0?"~x":"x") << std::abs(l) << " " << proofMult(d) << "+ ";
			}
			if(div_coef>1) proofBuffer << div_coef << " d ";
		}
		rhs=largeCoefsNeeded;
		degree=largeCoefsNeeded;
		vars.resize(skippable);
		for(int i=0; i<(int)vars.size(); ++i){
			SMALL& c = coefs[vars[i]];
			if(c<0){ c=-1; --rhs; }
			else c=1;
		}
		return true;
	}
	bool isCardinality() const {
		for(Var v: vars) if(std::abs(coefs[v])>1) return false;
		return true;
	}

	// @pre: reducible to unit over v
	void reduceToUnit(Var v_unit){
		removeUnitsAndZeroes();
		assert(getLit(v_unit)!=0);
		for(Var v: vars) if(v!=v_unit) weaken(-coefs[v],v);
		assert(getDegree()>0);
		LARGE d = std::max<LARGE>(std::abs(coefs[v_unit]),getDegree());
		if(d>1) proofBuffer << d << " d ";
		if(coefs[v_unit]>0){ coefs[v_unit]=1; rhs=1;}
		else{ coefs[v_unit]=-1; rhs=0; }
		degree=1;
	}

	void sortInDecreasingCoefOrder() {
		std::sort(vars.begin(),vars.end(),[&](Var v1,Var v2){ return std::abs(coefs[v1])>std::abs(coefs[v2]); });
	}
	bool isSortedInDecreasingCoefOrder() const {
		for(int i=1; i<(int)vars.size(); ++i) if(std::abs(coefs[vars[i-1]])<std::abs(coefs[vars[i]])) return false;
		return true;
	}

	void logAsInput(){
		toStreamAsOPB(formula_out);
		proof_out << "l " << ++last_formID << "\n";
		resetBuffer(++last_proofID); // ensure consistent proofBuffer
	}

	void logProofLine(std::string info){
		_unused(info);
		if(logStartTime<getDetTime()){
			proof_out << "p " << proofBuffer.str() << "0\n";
			resetBuffer(++last_proofID); // ensure consistent proofBuffer
			#if !NDEBUG
			proof_out << "* " << getDetTime() << " " << info << "\n";
			proof_out << "e " << last_proofID << " ";
			toStreamAsOPB(proof_out);
			#endif
		}else{
			logAsInput();
		}
	}

	void logInconsistency(){
		removeUnitsAndZeroes();
		logProofLine("i");
		proof_out << "c " << last_proofID << " 0" << std::endl;
	}

	void toStreamAsOPB(std::ofstream& o) {
		for(Var v: vars){
			Lit l = getLit(v);
			if(l==0) continue;
			SMALL c=getCoef(l);
			assert(c>0);
			o << "+" << c << (l<0?" ~x":" x") << v << " ";
		}
		o << ">= " << getDegree() << " ;\n";
	}
};
using intConstr = Constraint<int,long long>;
using longConstr = Constraint<long long,__int128>;

intConstr tmpConstraint;
longConstr confl_data;
intConstr logConstraint;

template<class S, class L>
std::ostream & operator<<(std::ostream & o, Constraint<S,L>& C) {
	std::vector<Var> vars = C.vars;
	std::sort(vars.begin(),vars.end(), [](Var v1, Var v2) { return v1<v2; });
	for(Var v: vars){
		Lit l = C.getLit(v);
		if(l==0) continue;
		o << C.getCoef(l) << "x" << l << ":" << (isTrue(l)?"t":(isFalse(l)?"f":"u")) << "@" << std::max(Level[l],Level[-l]) << "," << Pos[std::abs(l)] << " ";
	}
	o << ">= " << C.getDegree();
	return o;
}
std::ostream & operator<<(std::ostream & o, const Constr& C) {
	logConstraint.init(C);
	o << C.id << ": " << logConstraint << " sl: " << logConstraint.getSlack();
	logConstraint.reset();
	return o;
}
long long getSlack(Constr& C){
	logConstraint.init(C);
	long long slack = logConstraint.getSlack();
	logConstraint.reset();
	return slack;
}

struct IntSet{ // TODO: parametrize type // TODO: external data structure
private:
	std::vector<bool> _values={false};
	std::vector<bool>::iterator values=_values.begin();
	static constexpr bool _unused_(){ return false; }

public:
	std::vector<int> keys;

	IntSet(){}
	IntSet(int size, const std::vector<int>& ints) { resize(size); for(int i: ints) add(i); }

	void reset(){
		for(int k: keys) values[k]=_unused_();
		keys.clear();
	}

	inline void resize(int size){ resizeLitMap(_values,values,size,_unused_()); }
	inline size_t size() const { return keys.size(); }

	inline bool has(int key) const { return _values.size()>2*std::abs(key) && values[key]!=_unused_(); }
	void add(int key){
		if(_values.size()<=2*std::abs(key)) resize(std::abs(key));
		if(values[key]!=_unused_()) return;
		values[key]=true;
		keys.push_back(key);
	}
};

IntSet tmpSet;
IntSet actSet;

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

	CRef alloc(intConstr& constraint, ID proofID, bool formula, bool learnt, bool locked){
		assert(proofID!=0);
		assert(constraint.getDegree()>0);
		assert(constraint.getDegree()<=1e9);
		assert(constraint.isSaturated());
		// as the constraint is saturated, the coefficients are between 1 and 1e9 as well.
		assert(!constraint.vars.empty());
		unsigned int length = constraint.vars.size();
		bool asClause = clauseProp() && (constraint.getDegree()==1);

		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		uint32_t old_at = at;
		at += sz_constr(length+(asClause?0:length));
		capacity(at);
		Constr* constr = (Constr*)(memory+old_at);
		new (constr) Constr;
		constr->id = proofID;
		constr->act = 0;
		constr->degree = constraint.getDegree();
		constr->header = {formula,learnt,length,(unsigned int)(locked?LOCKED:UNLOCKED),length};
		constr->ntrailpops = 0;
		constr->slack = -constr->degree;
		constr->watchIdx = -asClause;
		assert((constr->degree==1 && clauseProp())==((int)constr->watchIdx==-1));
		for(unsigned int i=0; i<length; ++i){
			Var v = constraint.vars[i];
			assert(constraint.getLit(v)!=0);
			if(asClause) constr->data[i]=constraint.getLit(v);
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

std::vector<double> activity;
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

double v_vsids_decay=0.95;
double v_vsids_inc=1.0;
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
		order_heap.percolateUp(v); }

double c_vsids_inc=1.0;
double c_vsids_decay=0.999;
void cDecayActivity() { c_vsids_inc *= (1 / c_vsids_decay); }
void cBumpActivity (Constr& c) {
		if ( (c.act += c_vsids_inc) > 1e20 ) {
			// Rescale:
			for (size_t i = 0; i < constraints.size(); i++)
				ca[constraints[i]].act *= 1e-20;
			c_vsids_inc *= 1e-20; } }

// ---------------------------------------------------------------------
// Search

void uncheckedEnqueue(Lit p, CRef from){
	assert(!isTrue(p));
	assert(!isFalse(p));
	assert(isUnknown(p));
	Var v = std::abs(p);
	Reason[v] = from;
	if(decisionLevel()==0){
		Reason[v] = CRef_Undef; // no need to keep track of reasons for unit literals
		if(logProof()){
			Constr& C = ca[from];
			logConstraint.init(C);
			logConstraint.reduceToUnit(v);
			logConstraint.logProofLine("u");
			logConstraint.reset();
			assert(unitIDs.size()==trail.size());
			unitIDs.push_back(last_proofID);
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
	assert(constraint.hasNoUnits());
	assert(constraint.getDegree()>0);
	assert(constraint.vars.size()>0);

	if(logProof()) constraint.logProofLine("a");
	else ++last_proofID; // proofID's function as CRef ID's
	CRef cr = ca.alloc(constraint,last_proofID,formula,learnt,locked);
	constraints.push_back(cr);
	Constr& C = ca[cr]; int* data = C.data;

	if(C.size()==1){
		assert(decisionLevel()==0);
		assert(isUnknown(data[1-clauseProp()]));
		propagate(data[1-clauseProp()],cr);
		return cr;
	}

	if(C.isClause()){
		for(unsigned int i=1; i<C.size(); ++i){
			Lit l = data[i];
			if(!isFalse(l)){
				if(isFalse(data[0])){ data[i]=data[0]; data[0]=l; }
				else{ data[i]=data[1]; data[1]=l; break; }
			}
		}
		assert(!isFalse(data[0]));
		if(isFalse(data[1])){
			if(!isTrue(data[0])) propagate(data[0],cr);
			for(unsigned int i=2; i<C.size(); ++i){ // ensure second watch is last falsified literal
				Lit l = data[i];
				assert(isFalse(l));
				if(Level[-l]>Level[-data[1]]){ data[i]=data[1]; data[1]=l; }
			}
		}
		for(int i=0; i<2; ++i) adj[data[i]].emplace_back(cr,data[1-i]-INF);
		return cr;
	}

	if(countingProp()){ // use counting propagation
		for(unsigned int i=0; i<2*C.size(); i+=2){
			Lit l = data[i+1];
			adj[l].emplace_back(cr,i);
			if(!isFalse(l) || Pos[std::abs(l)]>=qhead) C.slack+=data[i];
		}
		assert(C.slack>=0);
		if(C.slack<C.largestCoef()){ // propagate
			for(unsigned int i=0; i<2*C.size() && data[i]>C.slack; i+=2) if(isUnknown(data[i+1])) {
				propagate(data[i+1],cr);
			}
		}
		return cr;
	}

	// watched propagation
	for(unsigned int i=0; i<2*C.size() && C.slack<C.largestCoef(); i+=2){
		Lit l = data[i+1];
		if(!isFalse(l) || Pos[std::abs(l)]>=qhead){
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
		for(unsigned int i=0; i<2*C.size(); i+=2) if(isFalse(data[i+1]) && Pos[std::abs(data[i+1])]<qhead) falsifiedIdcs.push_back(i);
		std::sort(falsifiedIdcs.begin(),falsifiedIdcs.end(),[&](unsigned i1,unsigned i2){
			return Pos[std::abs(data[i1+1])]>Pos[std::abs(data[i2+1])]; });
		long long diff = C.largestCoef()-C.slack;
		for(unsigned int i: falsifiedIdcs){
			assert(!C.isWatched(i));
			diff-=data[i];
			data[i]=-data[i];
			adj[data[i+1]].emplace_back(cr,i);
			if(diff<=0) break;
		}
		// perform initial propagation
		for(unsigned int i=0; i<2*C.size() && std::abs(data[i])>C.slack; i+=2) if(isUnknown(data[i+1])) {
			propagate(data[i+1],cr);
		}
	}
	return cr;
}

void undoOne(){
	assert(!trail.empty());
	++NTRAILPOPS;
	Lit l = trail.back();
	if(qhead==(int)trail.size()){
		for(const Watch& w: adj[-l]) if(w.idx>=0) ca[w.cref].undoFalsified(w.idx);
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
	++NDECIDE;
	newDecisionLevel();
	uncheckedEnqueue(l,CRef_Undef);
}

inline void propagate(Lit l, CRef reason){
	assert(reason!=CRef_Undef);
	++NPROP;
	uncheckedEnqueue(l,reason);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void recomputeLBD(Constr& C) {
	if(C.lbd()<=2) return;
	assert(tmpSet.size()==0);
	for (int i=0; i<(int)C.size(); i++) if (isFalse(C.lit(i))) tmpSet.add(Level[-C.lit(i)]);
	C.setLBD(tmpSet.size());
	tmpSet.reset();
}

void analyze(CRef confl){
	Constr& C = ca[confl];
	if (C.learnt()) {
		cBumpActivity(C);
		recomputeLBD(C);
	}

	confl_data.init(C);
	confl_data.removeUnitsAndZeroes();
	assert(actSet.size()==0); // will hold the literals that need their activity bumped
	for(Var v: confl_data.vars) actSet.add(confl_data.getLit(v));
	while(true){
		if(asynch_interrupt)exit_INDETERMINATE();
		if (decisionLevel() == 0) {
			if(logProof()) confl_data.logInconsistency();
			assert(confl_data.getSlack()<0);
			exit_UNSAT();
		}
		Lit l = trail.back();
		assert(std::abs(confl_data.getCoef(-l))<INF);
		Coef confl_coef_l = confl_data.getCoef(-l);
		if(confl_coef_l>0) {
			if (confl_data.falsifiedCurrentLvlIsOne()) {
				break;
			} else {
				assert(Reason[std::abs(l)] != CRef_Undef);
				if(originalRoundToOne){
					confl_data.roundToOne(confl_coef_l,false);
					confl_coef_l=1;
				}
				Constr& reasonC = ca[Reason[std::abs(l)]];
				if (reasonC.learnt()) {
					cBumpActivity(reasonC);
					recomputeLBD(reasonC);
				}
				tmpConstraint.init(reasonC);
				tmpConstraint.removeUnitsAndZeroes(); // NOTE: also saturates
				tmpConstraint.weakenNonImplying(tmpConstraint.getCoef(l),tmpConstraint.getSlack()); // NOTE: also saturates
				assert(tmpConstraint.getCoef(l)>tmpConstraint.getSlack());
				tmpConstraint.roundToOne(tmpConstraint.getCoef(l),!originalRoundToOne);
				assert(tmpConstraint.getCoef(l)==1);
				assert(tmpConstraint.getSlack()<=0);
				for(Var v: tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
				confl_data.add(tmpConstraint,confl_coef_l);
				tmpConstraint.reset();
				assert(confl_data.getCoef(-l)==0);
				assert(confl_data.getSlack()<0);
			}
		}
		undoOne();
	}
	assert(confl_data.getSlack()<0);
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
			if(idx<0 && isTrue(idx+INF)){ assert(ca[ws[it_ws].cref].isClause()); continue; } // blocked literal check
			CRef cr = ws[it_ws].cref;
			Constr& C = ca[cr];
			if(C.getStatus()>=FORCEDELETE){ swapErase(ws,it_ws--); continue; }
			WatchStatus wstat = C.propagateWatch(cr,ws[it_ws].idx,-p);
			if(wstat==WatchStatus::FOUNDNEW) swapErase(ws,it_ws--);
			else if(wstat==WatchStatus::CONFLICTING){ // clean up current level and stop propagation
				++NTRAILPOPS;
				for(int i=0; i<=it_ws; ++i){
					const Watch& w=ws[i];
					if(w.idx>=0) ca[w.cref].undoFalsified(w.idx);
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
	while (next == 0 || !isUnknown(next)){
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
	if (nvars > 1e9) exit_ERROR({"Number of variables cannot exceed 1e9."});
	if (nvars <= n) return;
	resizeLitMap(_adj,adj,nvars,{});
	resizeLitMap(_Level,Level,nvars,-1);
	Pos.resize(nvars+1,-1);
	Reason.resize(nvars+1,CRef_Undef);
	activity.resize(nvars+1,0);
	phase.resize(nvars+1);
	last_sol.resize(nvars+1,false);
	tmpConstraint.resize(nvars+1);
	confl_data.resize(nvars+1);
	logConstraint.resize(nvars+1);
	order_heap.resize(nvars+1);
	for(Var v=n+1;v<=nvars;++v) phase[v] = -v, order_heap.insert(v);
	n = nvars;
}

// ---------------------------------------------------------------------
// Constraint addition

void learnConstraint(longConstr& confl){
	assert(confl.getDegree()>0);
	assert(confl.getDegree()<=1e9);
	assert(confl.isSaturated());
	confl.copyTo(tmpConstraint);
	assert(tmpConstraint.hasNoUnits());
	tmpConstraint.removeZeroes();
	tmpConstraint.sortInDecreasingCoefOrder();
	backjumpTo(tmpConstraint.getAssertionLevel());
	assert(qhead==(int)trail.size()); // jumped back sufficiently far to catch up with qhead
	long long slk = tmpConstraint.getSlack();
	if(slk<0){
		if(logProof()) tmpConstraint.logInconsistency();
		assert(decisionLevel()==0);
		exit_UNSAT();
	}
	tmpConstraint.heuristicWeakening(slk);
	tmpConstraint.postProcess(false);
	assert(tmpConstraint.isSaturated());

	CRef cr = attachConstraint(tmpConstraint,false,true,false);
	tmpConstraint.reset();
	Constr& C = ca[cr];
	recomputeLBD(C);

	LEARNEDLENGTHSUM+=C.size();
	LEARNEDDEGREESUM+=C.degree;
	if(C.degree==1) ++NCLAUSESLEARNED;
	else if(C.largestCoef()==1) ++NCARDINALITIESLEARNED;
	else ++NGENERALSLEARNED;
}

CRef addInputConstraint(intConstr& c, bool original, bool locked){
	assert(decisionLevel()==0);
	if(logProof()) c.logAsInput();
	c.postProcess(true);
	if(c.getDegree()>(long long) 1e9) exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
	if(c.getDegree()<=0) return CRef_Undef; // already satisfied.

	if(c.getSlack()<0){
		puts("c Inconsistent input constraint");
		if(logProof()) c.logInconsistency();
		assert(decisionLevel()==0);
		exit_UNSAT();
	}

	CRef cr = attachConstraint(c,original,false,locked);
	CRef confl = runPropagation();
	if (confl != CRef_Undef){
		puts("c Input conflict");
		if(logProof()){
			logConstraint.init(ca[confl]);
			logConstraint.logInconsistency();
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
int read_number(const std::string & s) {
	long long answer = 0;
	for (char c : s) if ('0' <= c && c <= '9') {
		answer *= 10, answer += c - '0';
		if (answer > (int) 1e9) exit_ERROR({"Input formula contains absolute value larger than 10^9: ",s});
	}
	for (char c : s) if (c == '-') answer = -answer;
	return answer;
}

void opb_read(std::istream & in, intConstr& objective) {
	intConstr inverted;
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
				if(weight>1e9) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
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
		if(ca[adj[l][i].cref].getStatus()==MARKEDFORDELETE) swapErase(adj[l],i--);
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
			long long eval = -C.degree;
			for(int j=0; j<(int)C.size() && eval<0; ++j) if(isUnit(C.lit(j))) eval+=C.coef(j);
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
double luby(double y, Var x){
	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);
	while(size != x+1){
		size = (size-1)>>1;
		seq--;
		assert(size!=0);
		x = x % size;
	}
	return pow(y, seq);
}

// ---------------------------------------------------------------------
// Main

void print_stats() {
	double timespent = cpuTime()-initial_time;
	printf("c CPU time			  : %g s\n", timespent);
	printf("c deterministic time %lld %.2e\n", getDetTime(),(double)getDetTime());
	printf("c propagations %lld\n", NPROP);
	printf("c decisions %lld\n", NDECIDE);
	printf("c conflicts %lld\n", NCONFL);
	printf("c restarts %lld\n", curr_restarts);
	printf("c inprocessing phases %lld\n", cnt_reduceDB);
	printf("c clauses learned %lld\n", NCLAUSESLEARNED);
	printf("c cardinalities learned %lld\n", NCARDINALITIESLEARNED);
	printf("c general constraints learned %lld\n", NGENERALSLEARNED);
	printf("c average learned constraint length %.2f\n", NCONFL==0?0:(double)LEARNEDLENGTHSUM/NCONFL);
	printf("c average learned constraint degree %.2f\n", NCONFL==0?0:(double)LEARNEDDEGREESUM/NCONFL);
	printf("c gcd simplifications %lld\n", NGCD);
	printf("c detected cardinalities %lld\n", NCARDDETECT);
	printf("c weakened non-implied lits %lld\n", NWEAKENEDNONIMPLIED);
	printf("c weakened non-implying lits %lld\n", NWEAKENEDNONIMPLYING);
	printf("c auxiliary variables introduced %d\n", n-orig_n);
	if(opt_mode>0){
		printf("c solutions found %lld\n", NSOLS);
		printf("c cores constructed %lld\n", NCORES);
		printf("c core cardinality constraints returned %lld\n", NCORECARDINALITIES);
	}
	printf("c clausal propagations %lld\n", NPROPCLAUSE);
	printf("c watch lookups %lld\n", NWATCHLOOKUPS);
	printf("c watch checks %lld\n", NWATCHCHECKS);
	printf("c constraint additions %lld\n", NADDEDLITERALS);
	printf("c trail pops %lld\n", NTRAILPOPS);
}

long long lhs(Constr& C, const std::vector<bool>& sol){
	long long result = 0;
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
	print_stats();
	if(foundSolution()) std::cout << "o " << last_sol_obj_val << std::endl;
	puts("s SATISFIABLE");
	printSol();
	exit(10);
}

void exit_UNSAT() {
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
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void exit_ERROR(const std::initializer_list<std::string>& messages){
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
	printf("  --rinc=arg       Set the base of the Luby restart sequence (floating point number >=1; default %lf).\n",rinc);
	printf("  --rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %lld).\n",rfirst);
	printf("  --original-rto=arg Set whether to use RoundingSat's original round-to-one conflict analysis (0 or 1; default %d).\n",originalRoundToOne);
	printf("  --opt-mode=arg   Set optimization mode: 0 linear, 1(2) (lazy) core-guided, 3(4) (lazy) hybrid (default %d).\n",opt_mode);
	printf("  --prop-mode=arg  Set propagation mode: 0-7: bit 1 toggles watched/counting, bit 2 toggles clausal, bit 3 toggles Pueblo (default %d).\n",prop_mode);
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
																"prop-mode", "proof-log"};
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
	getOptionNum(opt_val,"prop-mode",[](double x)->bool{return 0<=x && x<=7 && round(x)==x;},prop_mode);
	getOptionStr(opt_val,"proof-log",proof_log_name);
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
		assert(isFalse(l_assump));
		int pos = Pos[std::abs(l_assump)];
		while((int)trail.size()>pos) undoOne();
		assert(isUnknown(l_assump));
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

	confl_data.init(ca[confl]);
	confl_data.removeUnitsAndZeroes();
	assert(confl_data.getSlack()<0);

	// analyze conflict
	long long assumpslk = assumpSlack(assumptions,confl_data);
	while(assumpslk>=0){
		Lit l = trail.back();
		assert(std::abs(confl_data.getCoef(-l))<INF);
		Coef confl_coef_l = confl_data.getCoef(-l);
		if(confl_coef_l>0) {
			tmpConstraint.init(ca[Reason[std::abs(l)]]);
			tmpConstraint.removeUnitsAndZeroes();
			tmpConstraint.weakenNonImplying(tmpConstraint.getCoef(l),tmpConstraint.getSlack()); // NOTE: also saturates
			assert(tmpConstraint.getCoef(l)>tmpConstraint.getSlack());
			tmpConstraint.roundToOne(tmpConstraint.getCoef(l),true);
			assert(tmpConstraint.getCoef(l)==1);
			assert(tmpConstraint.getSlack()<=0);
			confl_data.add(tmpConstraint,confl_coef_l);
			tmpConstraint.reset();
			assert(confl_data.getCoef(-l)==0);
			assert(confl_data.getSlack()<0);
			assumpslk = assumpSlack(assumptions,confl_data);
		}
		assert(decisionLevel()==(int)decisions.size());
		undoOne();
	}
	assert(confl_data.getDegree()>0);
	assert(confl_data.getDegree()<=1e9);
	assert(confl_data.isSaturated());
	confl_data.copyTo(outCore);
	confl_data.reset();

	// weaken non-falsifieds
	for(Var v: outCore.vars) if(!assumptions.has(-outCore.getLit(v))) outCore.weaken(-outCore.coefs[v],v);
	outCore.postProcess(true);
	assert(assumpSlack(assumptions,outCore)<0);
	backjumpTo(0);
}

enum SolveState { SAT, UNSAT, INPROCESSING };

SolveState solve(const IntSet& assumptions, intConstr& out) {
	out.reset();
	backjumpTo(0); // ensures assumptions are reset
	std::vector<int> assumptions_lim={0};
	assumptions_lim.reserve((int)assumptions.size()+1);
	while (true) {
		CRef confl = runPropagation();
		if (confl != CRef_Undef) {
			if(decisionLevel() == 0){
				if(logProof()){
					logConstraint.init(ca[confl]);
					logConstraint.logInconsistency();
					logConstraint.reset();
				}
				assert(getSlack(ca[confl])<0);
				exit_UNSAT();
			}
			vDecayActivity();
			cDecayActivity();
			NCONFL++; nconfl_to_restart--;
			if(NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10lld | #Constraints: %10lld\n",NCONFL,(long long)constraints.size());
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
				learnConstraint(confl_data);
				confl_data.reset();
			}else{
				extractCore(assumptions,confl,out);
				return SolveState::UNSAT;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				backjumpTo(0);
				double rest_base = luby(rinc, curr_restarts++);
				nconfl_to_restart = (long long) rest_base * rfirst;
				if(NCONFL >= (cnt_reduceDB+1)*nbconstrsbeforereduce) {
					++cnt_reduceDB;
					reduceDB();
					while(NCONFL >= cnt_reduceDB*nbconstrsbeforereduce) nbconstrsbeforereduce += incReduceDB;
					return SolveState::INPROCESSING;
				}
			}
			Lit next = 0;
			if((int)assumptions_lim.size()>decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			if(assumptions_lim.back()<(int)assumptions.size()){
				for(int i=(decisionLevel()==0?0:trail_lim.back()); i<(int)trail.size(); ++i){
					Lit l = trail[i];
					if(assumptions.has(-l)){ // found conflicting assumption
						if(isUnit(l)) backjumpTo(0), out.reset(); // negated assumption is unit
						else extractCore(assumptions,Reason[std::abs(l)],out,-l);
						return SolveState::UNSAT;
					}
				}
			}
			while(assumptions_lim.back()<(int)assumptions.size()){
				assert(decisionLevel()==(int)assumptions_lim.size()-1);
				Lit l_assump = assumptions.keys[assumptions_lim.back()];
				assert(!isFalse(l_assump)); // otherwise above check should have caught this
				if (isTrue(l_assump)){ // assumption already propagated
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
				for (Var v=1; v<=n; ++v) last_sol[v]=isTrue(v);
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

inline void printObjBounds(long long lower, long long upper){
	if(upper<INF) printf("c bounds %10lld >= %10lld\n",upper,lower);
	else printf("c bounds          - >= %10lld\n",lower);
}

ID handleNewSolution(const intConstr& origObj, ID& lastUpperBound){
	Coef prev_val = last_sol_obj_val; _unused(prev_val); // TODO: degree of constraint should be long long
	last_sol_obj_val = -origObj.getRhs();
	for(Var v: origObj.vars) last_sol_obj_val+=origObj.coefs[v]*last_sol[v];
	assert(last_sol_obj_val<prev_val);

	origObj.copyTo(tmpConstraint,true);
	tmpConstraint.addRhs(-last_sol_obj_val+1);
	ID origUpperBound = last_proofID+1;
	CRef cr = addInputConstraint(tmpConstraint,false,true);
	tmpConstraint.reset();
	lastUpperBound = replaceExternal(cr,lastUpperBound);
	return origUpperBound;
}

struct LazyVar{
	int mult; // TODO: add long long to int check?
	Coef rhs;
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
			if(lv->introducedVars.size()+lv->rhs==lv->lhs.size()){ swapErase(lazyVars,i--); delete lv; continue; }
		}
	}
	core.resize(n+1);
}
ID addLowerBound(const intConstr& origObj, Coef lowerBound, ID& lastLowerBound){
	origObj.copyTo(tmpConstraint);
	tmpConstraint.addRhs(lowerBound);
	ID origLowerBound = last_proofID+1;
	CRef cr = addInputConstraint(tmpConstraint,false,true);
	tmpConstraint.reset();
	lastLowerBound = replaceExternal(cr,lastLowerBound);
	return origLowerBound;
}
ID handleInconsistency(longConstr& reformObj, intConstr& core, long long& lower_bound,
                         std::vector<LazyVar*>& lazyVars, const intConstr& origObj, ID& lastLowerBound){
	// take care of derived unit lits and remove zeroes
	reformObj.removeUnitsAndZeroes(false);
	long long prev_lower = lower_bound; _unused(prev_lower);
	lower_bound = -reformObj.getDegree();
	if(core.getDegree()==0){ // apparently only unit assumptions were derived
		assert(lower_bound>prev_lower);
		checkLazyVariables(reformObj,core,lazyVars);
		return addLowerBound(origObj,lower_bound,lastLowerBound);
	}
	// figure out an appropriate core
	core.simplifyToCardinality(false);

	// adjust the lower bound
	if(core.getDegree()>1) ++NCORECARDINALITIES;
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
		reformObj.add(tmpConstraint,mult,false);
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
		reformObj.add(tmpConstraint,mult,false);
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
	origObj.removeUnitsAndZeroes(false);
	long long lower_bound = -origObj.getDegree();

	long long opt_coef_sum = 0;
	for (Var v: origObj.vars) opt_coef_sum+=std::abs(origObj.coefs[v]);
	if (opt_coef_sum > (long long)1e9) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});

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
		size_t current_time=getDetTime();
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
		if(assumps.size()==0) upper_time+=getDetTime()-current_time;
		else lower_time+=getDetTime()-current_time;
		if(reply==SolveState::SAT){
			++NSOLS;
			origUpperBound = handleNewSolution(origObj,lastUpperBound);
			assert((opt_mode!=1 && opt_mode!=2) || lower_bound==last_sol_obj_val);
		}	else if(reply==SolveState::UNSAT) {
			++NCORES;
			if(core.getSlack()<0){
				if(logProof()) core.logInconsistency();
				assert(decisionLevel()==0);
				exit_UNSAT();
			}
			origLowerBound = handleInconsistency(reformObj,core,lower_bound,lazyVars,origObj,lastLowerBound);
		} // else reply==SolveState::INPROCESSING, keep looping
		if(lower_bound>=last_sol_obj_val){
			printObjBounds(lower_bound,last_sol_obj_val);
			assert(lastUpperBound>0);
			assert(lastLowerBound>0);
			if(logProof()){
				longConstr coreAggregate;
				coreAggregate.resize(n+1);
				origObj.copyTo(tmpConstraint,true);
				tmpConstraint.addRhs(1-last_sol_obj_val);
				tmpConstraint.resetBuffer(origUpperBound);
				coreAggregate.add(tmpConstraint,1,false);
				tmpConstraint.reset();
				origObj.copyTo(tmpConstraint);
				tmpConstraint.addRhs(lower_bound);
				tmpConstraint.resetBuffer(origLowerBound);
				coreAggregate.add(tmpConstraint,1,false);
				tmpConstraint.reset();
				coreAggregate.logInconsistency();
				assert(coreAggregate.getSlack()<0);
				assert(decisionLevel()==0);
			}
			exit_UNSAT();
		}
	}
}

int main(int argc, char**argv){
	initial_time = cpuTime();
	init();
	intConstr objective;
	intConstr inconsistency;

	signal(SIGINT, SIGINT_exit);
	signal(SIGTERM,SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);

	std::string filename = read_options(argc, argv);
	if(logProof()){
		formula_out = std::ofstream(proof_log_name+".formula");
		formula_out << "* #variable= 0 #constraint= 0\n";
		formula_out << " >= 0 ;\n"; ++last_formID;
		proof_out = std::ofstream(proof_log_name+".proof");
		proof_out << "pseudo-Boolean proof version 1.0\n";
		proof_out << "l 1\n"; ++last_proofID;
	}
	if (!filename.empty()) {
		std::ifstream fin(filename);
		if (!fin) exit_ERROR({"Could not open ",filename});
		file_read(fin,objective);
	} else {
		if (verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
		file_read(std::cin,objective);
	}
	if(logProof()) formula_out << "* INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW\n";
	std::cout << "c #variables=" << orig_n << " #constraints=" << constraints.size() << std::endl;

	signal(SIGINT, SIGINT_interrupt);
	signal(SIGTERM,SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);

	if(objective.vars.size() > 0) optimize(objective,inconsistency);
	else while(true){
		SolveState reply = solve({},inconsistency);
		if(reply==SolveState::SAT) exit_SAT();
		else if(reply==SolveState::UNSAT){
			if(logProof()) inconsistency.logInconsistency();
			assert(decisionLevel()==0);
			assert(inconsistency.getSlack()<0);
			exit_UNSAT();
		}
	}
}
