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
#include <map>

#define _unused(x) ((void)(x)) // marks variables unused in release mode

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

template<class T> inline bool contains(const std::vector<T>& v, const T& x){
	return std::find(v.cbegin(),v.cend(),x)!=v.cend();
}

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE(),exit_ERROR(const std::initializer_list<std::string>&);

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
static inline double cpuTime() {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

// ---------------------------------------------------------------------
// Global variables

const int resize_factor=2;
const int INF=1e9+1;

double initial_time;
long long NBACKJUMP=0, DETERMINISTICTIME=1;
long long NCONFL=0, NDECIDE=0, NPROP=0;
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
int opt_mode=0;
long long curr_restarts=0;
long long nconfl_to_restart=0;
bool print_sol = false;
std::string proof_log_name;
bool logProof(){ return !proof_log_name.empty(); }
std::ofstream proof_out; std::ofstream formula_out;
long long last_proofID = 0; long long last_formID = 0;
std::vector<long long> unitIDs;
long long logStartTime=0;

struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};
const CRef CRef_Undef = { UINT32_MAX };
std::ostream& operator<<(std::ostream& os, CRef cr) { return os << cr.ofs; }

int verbosity = 1;
// currently, the maximum number of variables is hardcoded (variable N), and most arrays are of fixed size.
int n = 0;
int orig_n = 0;
std::vector<CRef> formula_constrs, learnts, external;
struct Watch {
	CRef cref;
	unsigned int idx;
	Watch(CRef cr, unsigned int i):cref(cr),idx(i){};
	bool operator==(const Watch& other)const{return other.cref==cref && other.idx==idx;}
};

std::vector<std::vector<Watch>> _adj={{}}; std::vector<std::vector<Watch>>::iterator adj;
std::vector<int> _Level={-1}; std::vector<int>::iterator Level;
std::vector<int> trail, trail_lim, Pos;
std::vector<CRef> Reason;
int qhead; // for unit propagation
int last_sol_obj_val = INF;
inline bool foundSolution(){return last_sol_obj_val<INF;}
std::vector<bool> last_sol;
std::vector<int> phase;
inline void newDecisionLevel() { trail_lim.push_back(trail.size()); }
inline int decisionLevel() { return trail_lim.size(); }

enum DeletionStatus { LOCKED, UNLOCKED, FORCEDELETE, MARKEDFORDELETE };
enum WatchStatus { FOUNDNEW, FOUNDNONE, CONFLICTING };

void uncheckedEnqueue(int p, CRef from);
struct Constr {
	long long id;
	float act;
	int degree;
	// NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
	struct {
		unsigned unused       : 1;
		unsigned learnt       : 1;
		unsigned lbd          : 30;
		unsigned status       : 2;
		unsigned size         : 30;
	} header;
	long long nbackjump;
	long long slack; // sum of non-falsified watches minus w.
	// NOTE: will never be larger than 2 * non-falsified watch, so fits in 32 bit for the n-watched literal scheme
	// TODO: is above really true?
	unsigned int watchIdx;
	int data[];

	inline unsigned int size() const { return header.size; }
	inline void setStatus(DeletionStatus ds){ header.status=(unsigned int) ds; }
	inline DeletionStatus getStatus() const { return (DeletionStatus) header.status; }
	inline void setLBD(unsigned int lbd){ header.lbd=std::min(header.lbd,lbd); }
	inline unsigned int lbd() const { return header.lbd; }
	inline bool learnt() const { return header.learnt; }
	inline int largestCoef() const { return std::abs(data[0]); }
	inline int coef(unsigned int i) const { return std::abs(data[i<<1]); }
	inline int lit(unsigned int i) const { return data[(i<<1)+1]; }
	inline bool isWatched(unsigned int i) const { assert(i%2==0); return data[i]<0; }
	inline void undoFalsified(unsigned int i) {
		assert(i%2==0);
		assert(isWatched(i));
		slack -= data[i];
		watchIdx=0;
	}
	inline WatchStatus propagateWatch(CRef cr, unsigned int idx){
		assert(idx%2==0);
		const unsigned int Csize2 = 2*size(); const int ClargestCoef = largestCoef();
		const int c = data[idx];
		assert(c<0);
		slack+=c;
		if(slack-c>=ClargestCoef){ // look for new watches if previously, slack was at least ClargestCoef
			if(nbackjump<NBACKJUMP){ nbackjump=NBACKJUMP; watchIdx=0; }
			DETERMINISTICTIME-=watchIdx;
			for(; watchIdx<Csize2 && slack<ClargestCoef; watchIdx+=2){ // NOTE: first innermost loop of RoundingSat
				const int cf = data[watchIdx];
				const int l = data[watchIdx+1];
				if(cf>0 && Level[-l]==-1){
					slack+=cf;
					data[watchIdx]=-cf;
					adj[l].emplace_back(cr,watchIdx);
				}
			}
			DETERMINISTICTIME+=watchIdx;
			if(slack<ClargestCoef){ assert(watchIdx==Csize2); watchIdx=0; }
		} // else we did not find enough watches last time, so we can skip looking for them now

		if(slack>=ClargestCoef){
			data[idx]=-c;
			return WatchStatus::FOUNDNEW;
		}else if(slack>=0){ // keep the watch, check for propagation
			DETERMINISTICTIME-=watchIdx;
			for(; watchIdx<Csize2 && std::abs(data[watchIdx])>slack; watchIdx+=2){ // NOTE: second innermost loop of RoundingSat
				const int l = data[watchIdx+1];
				if(Pos[std::abs(l)]==-1) uncheckedEnqueue(l,cr);
			}
			DETERMINISTICTIME+=watchIdx;
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
	std::vector<int> vars;
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

	void resetBuffer(long long proofID){
		proofBuffer.clear();
		proofBuffer.str(std::string());
		proofBuffer << proofID << " ";
	}

	bool isReset() const { return vars.size()==0 && rhs==0; }
	void reset(){
		for(int v: vars) coefs[v]=_unused_();
		vars.clear();
		rhs=0; degree = 0;
		if(logProof()) resetBuffer(1); // NOTE: proofID 1 equals the constraint 0 >= 0
	}

	void init(Constr& C){
		assert(isReset()); // don't use a Constraint used by other stuff
		addRhs(C.degree);
		for(size_t i=0;i<C.size();++i){ assert(C.coef(i)!=0); addLhs(C.coef(i), C.lit(i)); } // resets degree
		if(logProof()) resetBuffer(C.id);
	}

	inline void addRhs(LARGE r){ rhs+=r; if(degree!=_invalid_()) degree+=r; }
	inline LARGE getRhs() const { return rhs; }
	inline LARGE getDegree() {
		if(degree!=_invalid_()) return degree;
		degree = rhs;
		for (int v: vars) degree -= std::min<SMALL>(0,coefs[v]); // considering negative coefficients
		return degree;
	}
	inline SMALL getCoef(int l) const {
		assert(std::abs(l)<coefs.size());
		return coefs[std::abs(l)]==_unused_()?0:(l<0?-coefs[-l]:coefs[l]);
	}
	inline int getLit(int l) const { // NOTE: answer of 0 means coef 0 or not in vars
		int v = std::abs(l);
		if(v>=(int)coefs.size()) return 0;
		SMALL c = coefs[v];
		if(c==0 || c==_unused_()) return 0;
		else if(c<0) return -v;
		else return v;
	}
	inline bool falsified(int v) const {
		assert(v>0);
		assert((getLit(v)!=0 && Level[-getLit(v)]==-1)==(coefs[v]>0 && Level[-v]==-1) || (coefs[v]<0 && Level[v]==-1));
		return !((coefs[v]>0 && Level[-v]==-1) || (coefs[v]<0 && Level[v]==-1)); // TODO: simplify
	}
	LARGE getSlack() const {
		LARGE slack = -rhs;
		for(int v: vars) if(Level[v]!=-1 || (Level[-v]==-1 && coefs[v]>0)) slack+=coefs[v];
		return slack;
	}

	// NOTE: erasing variables with coef 0 in addLhs would lead to invalidated iteration (e.g., for loops that weaken)
	void addLhs(SMALL c, int l){ // treats negative literals as 1-v
		assert(l!=0);
		degree=_invalid_();
		int v = l;
		if(l<0){ rhs -= c; c = -c; v = -l; }
		assert(v<(int)coefs.size());
		if(coefs[v]==_unused_()) vars.push_back(v), coefs[v]=0;
		coefs[v]+=c;
	}
	inline void weaken(SMALL m, int l){ // add m*(l>=0) if m>0 and -m*(-l>=-1) if m<0
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
			for(int v: vars){
				int l = getLit(v); SMALL c = getCoef(l);
				if(Level[l]==0) proofBuffer << (l<0?"x":"~x") << v << " " << proofMult(c) << "+ ";
				else if (Level[-l]==0) proofBuffer << unitIDs[Pos[v]] << " " << proofMult(c) << "+ ";
			}
		}
		int j=0;
		for(int i=0; i<(int)vars.size(); ++i){
			int v=vars[i];
			if(coefs[v]==0) coefs[v]=_unused_();
			else if(Level[v]==0){
				rhs-=coefs[v];
				degree=_invalid_();
				coefs[v]=_unused_();
			}else if(Level[-v]==0){
				degree = _invalid_();
				coefs[v] = _unused_();
			}else vars[j++]=v;
		}
		vars.resize(j);
		if(doSaturation) saturate();
	}
	bool hasNoUnits() const {
		for(int v: vars) if(Level[v]==0 || Level[-v]==0) return false;
		return true;
	}

	// @post: mutates order of vars
	void removeZeroes() {
		for(int i=0; i<(int)vars.size(); ++i){
			int v=vars[i];
			if(coefs[v]==0){
				coefs[v]=_unused_();
				swapErase(vars,i--);
			}
		}
	}
	bool hasNoZeroes() const {
		for(int v: vars) if(coefs[v]==0) return false;
		return true;
	}

	// @post: preserves order of vars
	void saturate(){
		if(logProof() && !isSaturated()) proofBuffer << "s "; // log saturation only if it modifies the constraint
		LARGE w = getDegree();
		if(w<=0){ // NOTE: does not call reset(0), as we do not want to reset the buffer
			for(int v: vars) coefs[v]=_unused_();
			vars.clear(); rhs=0; degree=0;
			return;
		}
		for (int v: vars){
			if(coefs[v]<-w) rhs-=coefs[v]+w, coefs[v]=-w;
			else coefs[v]=std::min<LARGE>(coefs[v],w);
		}
		assert(isSaturated());
	}
	bool isSaturated() {
		LARGE w = getDegree();
		for(int v:vars) if(std::abs(coefs[v])>w) return false;
		return true;
	}

	template<class S, class L>
	void copyTo(Constraint<S,L>& out, bool inverted=false) const {
		assert(out.isReset());
		int mult=(inverted?-1:1);
		out.rhs=mult*rhs;
		out.vars=vars;
		out.resize(coefs.size());
		for(int v: vars) out.coefs[v]=mult*coefs[v];
		out.degree=out._invalid_();
		if(logProof()){
			out.proofBuffer.str(std::string());
			out.proofBuffer << proofBuffer.str() << proofMult(mult);
		}
	}

	template<class S, class L>
	void add(const Constraint<S,L>& c, SMALL mult=1, bool saturateAndReduce=true){
		assert(c._unused_()<=_unused_()); // don't add large stuff into small stuff
		if(logProof()) proofBuffer << c.proofBuffer.str() << proofMult(mult) << "+ ";
		for(int v: c.vars) addLhs(mult*c.coefs[v],v);
		addRhs((LARGE)mult*(LARGE)c.getRhs());
		degree=_invalid_();
		if(!saturateAndReduce) return;
		removeZeroes();
		saturate();
		if(getDegree() > (LARGE)1e9) roundToOne(ceildiv<LARGE>(getDegree(),1e9),!originalRoundToOne);
		assert(getDegree() <= (LARGE)1e9);
	}

	void roundToOne(const SMALL d, bool partial){
		assert(isSaturated());
		assert(d>0);
		if(d==1) return;
		for(int v:vars){
			assert(Level[-v]!=0);
			assert(Level[ v]!=0);
			if(coefs[v]%d!=0){
				if(!falsified(v)){
					if(partial) weaken(-coefs[v]%d,v); // partial weakening
					else weaken(-coefs[v],v);
				}else{
					assert((Level[v]==-1)==(coefs[v]>0));
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
		for(int v: vars){
			_gcd = gcd(_gcd,(unsigned int) std::abs(coefs[v]));
			if(_gcd==1) return false;
		}
		assert(_gcd>1); assert(_gcd<(unsigned int)INF);
		for (int v: vars) coefs[v] /= (int)_gcd;
		// NOTE: as all coefficients are divisible, we can ceildiv the rhs instead of the degree
		rhs=ceildiv_safe<LARGE>(rhs,_gcd);
		degree=_invalid_();

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
			int v = vars[i];
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
		for(int v: vars) if(coefs[v]>0) slack+=coefs[v];
		if(slack<0) return 0;

		assert(hasNoZeroes());
		assert(isSortedInDecreasingCoefOrder());

		// create useful datastructures
		std::vector<int> litsByPos;
		litsByPos.reserve(vars.size());
		for(int v: vars){
			int l = getLit(v); assert(l!=0);
			if(~Level[-l]) litsByPos.push_back(-l);
		}
		std::sort(litsByPos.begin(),litsByPos.end(),[&](int l1,int l2){ return Pos[std::abs(l1)]<Pos[std::abs(l2)]; });

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
		for(int v: vars) if(coefs[v]!=0 && std::abs(coefs[v])<=slack && !falsified(v)){
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
			int v = vars[i];
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
		int v_prop = -1;
		for(int i=vars.size()-1; i>=0; --i){
			int v = vars[i];
			if(std::abs(coefs[v])>slk && Pos[v]==-1){ v_prop=v; break; }
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
			for(int v: vars) weaken(-coefs[v],v);
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
				int l = getLit(vars[i]);
				SMALL d = getCoef(l)-div_coef;
				proofBuffer << (l>0?"~x":"x") << std::abs(l) << " " << proofMult(d) << "+ ";
			}
			for(int i=skippable; i<(int)vars.size(); ++i){ // weaken small vars
				int l = getLit(vars[i]);
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
		for(int v: vars) if(std::abs(coefs[v])>1) return false;
		return true;
	}

	// @pre: reducible to unit over v
	void reduceToUnit(int v_unit){
		removeUnitsAndZeroes();
		assert(getLit(v_unit)!=0);
		for(int v: vars) if(v!=v_unit) weaken(-coefs[v],v);
		assert(getDegree()>0);
		LARGE d = std::max<LARGE>(std::abs(coefs[v_unit]),getDegree());
		if(d>1) proofBuffer << d << " d ";
		if(coefs[v_unit]>0){ coefs[v_unit]=1; rhs=1;}
		else{ coefs[v_unit]=-1; rhs=0; }
		degree=1;
	}

	void sortInDecreasingCoefOrder() {
		std::sort(vars.begin(),vars.end(),[&](int v1,int v2){ return std::abs(coefs[v1])>std::abs(coefs[v2]); });
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
		if(logStartTime<DETERMINISTICTIME){
			proof_out << "p " << proofBuffer.str() << "0\n";
			resetBuffer(++last_proofID); // ensure consistent proofBuffer
			#if !NDEBUG
			proof_out << "* " << DETERMINISTICTIME << " " << info << "\n";
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
		for(int v: vars){
			int l = getLit(v);
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
	std::vector<int> vars = C.vars;
	sort(vars.begin(),vars.end(), [](S v1, S v2) { return v1<v2; });
	for(int v: vars){
		int l = C.getLit(v);
		if(l==0) continue;
		o << C.getCoef(l) << "x" << l << ":" << ((~Level[l])?"t":((~Level[-l])?"f":"u")) << "@" << std::max(Level[l],Level[-l]) << "," << Pos[std::abs(l)] << " ";
	}
	o << ">= " << C.getDegree();
	return o;
}
std::ostream & operator<<(std::ostream & o, Constr& C) {
	logConstraint.init(C);
	o << logConstraint;
	logConstraint.reset();
	return o;
}
long long getSlack(Constr& C){
	logConstraint.init(C);
	long long slack = logConstraint.getSlack();
	logConstraint.reset();
	return slack;
}

struct IntSet{
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
static inline void* xrealloc(void *ptr, size_t size)
{
	void* mem = realloc(ptr, size);
	if (mem == NULL && errno == ENOMEM){
		throw OutOfMemoryException();
	}else
		return mem;
}
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
	int sz_constr(int length) { return (sizeof(Constr)+sizeof(int)*length+sizeof(int)*length)/sizeof(uint32_t); }

	CRef alloc(intConstr& constraint, long long proofID, bool learnt, bool locked){
		assert(constraint.getDegree()>0);
		assert(constraint.getDegree()<=1e9);
		assert(constraint.isSaturated());
		// as the constraint is saturated, the coefficients are between 1 and 1e9 as well.
		assert(!constraint.vars.empty());
		unsigned int length = constraint.vars.size();

		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		uint32_t old_at = at;
		at += sz_constr(length);
		capacity(at);
		Constr* constr = (Constr*)(memory+old_at);
		new (constr) Constr;
		constr->id = proofID;
		constr->act = 0;
		constr->degree = constraint.getDegree();
		constr->header = {0,learnt,length,(unsigned int)(locked?LOCKED:UNLOCKED),length};
		constr->nbackjump = 0;
		constr->slack = -constr->degree;
		constr->watchIdx = 0;
		for(unsigned int i=0; i<length; ++i){
			int v = constraint.vars[i];
			assert(constraint.getLit(v)!=0);
			constr->data[(i<<1)]=std::abs(constraint.coefs[v]);
			constr->data[(i<<1)+1]=constraint.getLit(v);
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
	std::vector<int> tree = {-1,-1};
	void resize(int newsize) {
		if (cap >= newsize) return;
		// insert elements in such order that tie breaking remains intact
		std::vector<int> variables;
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
	bool empty() const { return tree[1] == -1; }
	bool inHeap(int v) const { return tree[v+cap+1] != -1; }
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

double v_vsids_decay=0.95;
double v_vsids_inc=1.0;
void vDecayActivity() { v_vsids_inc *= (1 / v_vsids_decay); }
void vBumpActivity(int v){
	assert(v>0);
	if ( (activity[v] += v_vsids_inc) > 1e100 ) {
		// Rescale:
		for (int i = 1; i <= n; i++)
			activity[i] *= 1e-100;
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
			for (size_t i = 0; i < learnts.size(); i++)
				ca[learnts[i]].act *= 1e-20;
			c_vsids_inc *= 1e-20; } }

// ---------------------------------------------------------------------
// Search

void uncheckedEnqueue(int p, CRef from=CRef_Undef){
	assert(Pos[std::abs(p)]==-1);
	int v = std::abs(p);
	Reason[v] = from;
	++NPROP;
	if(decisionLevel()==0){
		Reason[v] = CRef_Undef; // no need to keep track of reasons for unit literals
		assert(from!=CRef_Undef);
		++DETERMINISTICTIME; // NOTE: helps for proof log debugging
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

CRef attachConstraint(intConstr& constraint, bool learnt, bool locked=false){
	assert(constraint.isSortedInDecreasingCoefOrder());
	assert(constraint.isSaturated());
	assert(constraint.hasNoZeroes());
	assert(constraint.hasNoUnits());

	if(logProof()) constraint.logProofLine("a");
	CRef cr = ca.alloc(constraint,last_proofID,learnt,locked);
	if (learnt) learnts.push_back(cr);
	else formula_constrs.push_back(cr);
	Constr& C = ca[cr]; int* data = C.data;

	for(unsigned int i=0; i<2*C.size() && C.slack<C.largestCoef(); i+=2){
		int l = data[i+1];
		if(Level[-l]==-1 || Pos[std::abs(l)]>=qhead){
			assert(!C.isWatched(i));
			C.slack+=data[i];
			data[i]=-data[i];
			adj[l].push_back({cr,i});
		}
	}
	assert(C.slack>=0);
	if(C.slack<C.largestCoef()){
		// set sufficient falsified watches
		std::vector<int> falsifieds;
		falsifieds.reserve(C.size());
		for(unsigned int i=0; i<2*C.size(); i+=2) if(~Level[-data[i+1]] && Pos[std::abs(data[i+1])]<qhead) falsifieds.push_back(i);
		std::sort(falsifieds.begin(),falsifieds.end(),[&](unsigned i1,unsigned i2){
			return Pos[std::abs(data[i1+1])]>Pos[std::abs(data[i2+1])]; });
		long long diff = C.largestCoef()-C.slack;
		for(unsigned int i: falsifieds){
			assert(!C.isWatched(i));
			diff-=data[i];
			data[i]=-data[i];
			adj[data[i+1]].push_back({cr,i});
			if(diff<=0) break;
		}
		// perform initial propagation
		for(unsigned int i=0; i<2*C.size() && std::abs(data[i])>C.slack; i+=2) if(Pos[std::abs(data[i+1])]==-1) {
			uncheckedEnqueue(data[i+1],cr);
		}
	}
	return cr;
}

void undoOne(){
	assert(!trail.empty());
	int l = trail.back();
	if(qhead==(int)trail.size()){
		for(const Watch& w: adj[-l]) ca[w.cref].undoFalsified(w.idx);
		--qhead;
		++NBACKJUMP;
	}
	int v = std::abs(l);
	trail.pop_back();
	Level[l] = -1;
	Pos[v] = -1;
	phase[v] = l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	order_heap.insert(v);
}

void backjumpTo(int level){
	assert(level>=0);
	while(decisionLevel()>level) undoOne();
}

void decide(int l){
	newDecisionLevel();
	uncheckedEnqueue(l);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

void recomputeLBD(Constr& C) {
	if(C.lbd()<=2) return;
	assert(tmpSet.size()==0);
	for (int i=0; i<(int)C.size(); i++) if (~Level[-C.lit(i)]) tmpSet.add(Level[-C.lit(i)]);
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
	for(int v: confl_data.vars) actSet.add(confl_data.getLit(v));
	while(true){
		if (decisionLevel() == 0) {
			if(logProof()) confl_data.logInconsistency();
			assert(confl_data.getSlack()<0);
			exit_UNSAT();
		}
		int l = trail.back();
		assert(std::abs(confl_data.getCoef(-l))<INF);
		int confl_coef_l = confl_data.getCoef(-l);
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
				for(int v: tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
				confl_data.add(tmpConstraint,confl_coef_l);
				tmpConstraint.reset();
				assert(confl_data.getCoef(-l)==0);
				assert(confl_data.getSlack()<0);
			}
		}
		undoOne();
	}
	assert(confl_data.getSlack()<0);
	for(int l: actSet.keys) if(l!=0) vBumpActivity(std::abs(l));
	actSet.reset();
}

/**
 * Unit propagation with watched literals.
 *
 * post condition: all watches up to trail[qhead] have been propagated
 */
CRef propagate() {
	++DETERMINISTICTIME; // NOTE: helps for proof log debugging
	while(qhead<(int)trail.size()){
		int p=trail[qhead++];
		std::vector<Watch> & ws = adj[-p];
		for(int it_ws=0; it_ws<(int)ws.size(); ++it_ws){
			++DETERMINISTICTIME;
			CRef cr = ws[it_ws].cref;
			Constr& C = ca[cr];
			if(C.getStatus()>=FORCEDELETE){ swapErase(ws,it_ws--); continue; }
			WatchStatus wstat = C.propagateWatch(cr,ws[it_ws].idx);
			if(wstat==WatchStatus::FOUNDNEW) swapErase(ws,it_ws--);
			else if(wstat==WatchStatus::CONFLICTING){ // clean up current level and stop propagation
				for(int i=0; i<=it_ws; ++i){ const Watch& w=ws[i]; ca[w.cref].undoFalsified(w.idx); }
				--qhead;
				return cr;
			}
		}
	}
	return CRef_Undef;
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
	for(int i=n+1;i<=nvars;++i) phase[i] = -i, order_heap.insert(i);
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

	CRef cr = attachConstraint(tmpConstraint,true);
	tmpConstraint.reset();
	Constr& C = ca[cr];
	recomputeLBD(C);

	LEARNEDLENGTHSUM+=C.size();
	LEARNEDDEGREESUM+=C.degree;
	if(C.degree==1) ++NCLAUSESLEARNED;
	else if(C.largestCoef()==1) ++NCARDINALITIESLEARNED;
	else ++NGENERALSLEARNED;
}

CRef addInputConstraint(intConstr& c, bool initial=false){
	assert(decisionLevel()==0);
	assert(learnts.size()==0 || !initial);
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

	CRef result = attachConstraint(c,!initial,true);
	CRef confl = propagate();
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
	return result;
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
				int coef = read_number(scoef);
				bool negated = false;
				std::string origvar = var;
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
			if(opt_line){
				tmpConstraint.copyTo(objective);
				tmpConstraint.reset();
			}else{
				tmpConstraint.addRhs(read_number(line0.substr(line0.find("=") + 1)));
				// Handle equality case with two constraints
				bool equality = line0.find(" = ") != std::string::npos;
				if(equality) tmpConstraint.copyTo(inverted,true);
				// NOTE: addInputConstraint modifies tmpConstraint, so the inverted version is stored first
				addInputConstraint(tmpConstraint,true);
				tmpConstraint.reset();
				if(equality){
					addInputConstraint(inverted,true);
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
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			if(weight<top){ // soft clause
				if(weight>1e9) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
				if(weight<0) exit_ERROR({"Negative clause weight: ",std::to_string(weight)});
				setNbVariables(n+1); // increases n to n+1
				objective.resize(n+1);
				objective.addLhs(weight,n);
				tmpConstraint.addLhs(1,n);
			} // else hard clause
			addInputConstraint(tmpConstraint,true);
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
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			addInputConstraint(tmpConstraint,true);
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
	for(int l=-n; l<=n; l++) {
		size_t i, j;
		for(i=0,j=0;i<adj[l].size();i++){
			CRef cr = adj[l][i].cref;
			if(ca[cr].getStatus()!=MARKEDFORDELETE) adj[l][j++]=adj[l][i];
		}
		adj[l].erase(adj[l].begin()+j,adj[l].end());
	}
	// constraints, learnts, adj[-n..n], reason[-n..n].
	uint32_t ofs_learnts=0;for(CRef cr:formula_constrs)ofs_learnts+=ca.sz_constr(ca[cr].size());
	sort(learnts.begin(), learnts.end(), [](CRef x,CRef y){return x.ofs<y.ofs;}); // we have to sort here, because reduceDB shuffles them.
	ca.wasted=0;
	ca.at=ofs_learnts;
	std::vector<CRef> learnts_old = learnts;
	for(CRef & cr : learnts){
		size_t length = ca[cr].size();
		memmove(ca.memory+ca.at, ca.memory+cr.ofs, sizeof(uint32_t)*ca.sz_constr(length));
		cr.ofs = ca.at;
		ca.at += ca.sz_constr(length);
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
	Constr& c = ca[cr];
	assert(c.getStatus()!=MARKEDFORDELETE);
	assert(c.getStatus()!=LOCKED);
	c.setStatus(MARKEDFORDELETE);
	ca.wasted += ca.sz_constr(c.size());
}

void reduceDB(){
	if (verbosity > 0) puts("c INPROCESSING");

	assert(decisionLevel()==0);
	size_t i, j;

	sort(learnts.begin(), learnts.end(), reduceDB_lt());
	if(ca[learnts[learnts.size() / 2]].lbd()<=3) nbconstrsbeforereduce += 1000;
	// Don't delete binary or locked constraints. From the rest, delete constraints from the first half
	// and constraints with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Constr& c = ca[learnts[i]];
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
double luby(double y, int x){
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

void print_stats() {
	double timespent = cpuTime()-initial_time;
	printf("c CPU time			  : %g s\n", timespent);
	printf("c deterministic time %lld %.2e\n", DETERMINISTICTIME,(double)DETERMINISTICTIME);
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
}

long long lhs(Constr& C, const std::vector<bool>& sol){
	long long result = 0;
	for(size_t j=0; j<C.size(); ++j){
		int l = C.lit(j);
		result+=((l>0)==sol[std::abs(l)])*C.coef(j);
	}
	return result;
}

bool checksol() {
	for(CRef cr: formula_constrs){
		Constr& C = ca[cr];
		if(lhs(C,last_sol)<C.degree) return false;
	}
	puts("c SATISFIABLE (checked)");
	return true;
}

void printSol(){
	assert(checksol());
	if(print_sol){
		printf("v");for(int i=1;i<=orig_n;i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n"); }
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
	printf("  --proof-log=arg  Set a filename for the proof logs (string).\n");
}

typedef bool (*func)(double);
template <class T>
void getOptionNum(const std::map<std::string, std::string>& opt_val, const std::string& option, func test, T& val){
	if (opt_val.count(option)) {
		double v = atof(opt_val.at(option).c_str());
		if (test(v)) val=v;
		else exit_ERROR({"Invalid value for ",option,": ",opt_val.at(option),".\nCheck usage with --help option."});
	}
}
void getOptionStr(const std::map<std::string, std::string>& opt_val, const std::string& option, std::string& val){
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
	std::vector<std::string> opts={"print-sol","verbosity", "var-decay", "rinc", "rfirst", "original-rto", "opt-mode", "proof-log"};
	std::map<std::string, std::string> opt_val;
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
	getOptionStr(opt_val,"proof-log",proof_log_name);
	return filename;
}

template<class SMALL, class LARGE>
LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core){
	LARGE slack = -core.getRhs();
	for(int v: core.vars) if(assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v]>0)) slack+=core.coefs[v];
	return slack;
}

void extractCore(const IntSet& assumptions, CRef confl, intConstr& outCore, int l_assump=0){
	assert(confl!=CRef_Undef);

	if(l_assump!=0){ // l_assump is an assumption propagated to the opposite value
		assert(assumptions.has(l_assump));
		assert(~Level[-l_assump]);
		int pos = Pos[std::abs(l_assump)];
		while((int)trail.size()>pos) undoOne();
		assert(Pos[std::abs(l_assump)]==-1);
		decide(l_assump);
	}

	// Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
	// For this, we first copy the trail, then backjump to 0, then rebuild the trail.
	// Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
	std::vector<int> decisions; // holds the decisions
	decisions.reserve(decisionLevel());
	std::vector<int> props; // holds the propagations
	props.reserve(trail.size());
	assert(trail_lim.size()>0);
	for(int i=trail_lim[0]; i<(int)trail.size(); ++i){
		int l = trail[i];
		if(assumptions.has(l)) decisions.push_back(l);
		else props.push_back(l);
	}
	backjumpTo(0);

	for(int l: decisions) decide(l);
	for(int l: props) { assert(Reason[std::abs(l)]!=CRef_Undef); uncheckedEnqueue(l,Reason[std::abs(l)]); }

	confl_data.init(ca[confl]);
	confl_data.removeUnitsAndZeroes();
	assert(confl_data.getSlack()<0);

	// analyze conflict
	long long assumpslk = assumpSlack(assumptions,confl_data);
	while(assumpslk>=0){
		int l = trail.back();
		assert(std::abs(confl_data.getCoef(-l))<INF);
		int confl_coef_l = confl_data.getCoef(-l);
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
	for(int v: outCore.vars) if(!assumptions.has(-outCore.getLit(v))) outCore.weaken(-outCore.coefs[v],v);
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
		CRef confl = propagate();
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
					printf("c #Conflicts: %10lld | #Learnt: %10lld\n",NCONFL,(long long)learnts.size());
//					print_stats();
					if(verbosity>2){
						// memory usage
						std::cout<<"c total constraint space: "<<ca.cap*4/1024./1024.<<"MB"<<std::endl;
						std::cout<<"c total #watches: ";{long long cnt=0;for(int l=-n;l<=n;l++)cnt+=(long long)adj[l].size();std::cout<<cnt<<std::endl;}
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
			int next = 0;
			if((int)assumptions_lim.size()>decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			if(assumptions_lim.back()<(int)assumptions.size()){
				for(int i=(decisionLevel()==0?0:trail_lim.back()); i<(int)trail.size(); ++i){
					int l = trail[i];
					if(assumptions.has(-l)){ // found conflicting assumption
						if(Level[l]==0) backjumpTo(0), out.reset(); // negated assumption is unit
						else extractCore(assumptions,Reason[std::abs(l)],out,-l);
						return SolveState::UNSAT;
					}
				}
			}
			while(assumptions_lim.back()<(int)assumptions.size()){
				assert(decisionLevel()==(int)assumptions_lim.size()-1);
				int l_assump = assumptions.keys[assumptions_lim.back()];
				assert(Level[-l_assump]==-1); // otherwise above check should have caught this
				if (~Level[l_assump]){ // assumption already propagated
					++assumptions_lim.back();
				}else{ // unassigned assumption
					next = l_assump;
					assumptions_lim.push_back(assumptions_lim.back()+1);
					break;
				}
			}
			if(next==0) next = pickBranchLit();
			if(next==0) {
				assert(order_heap.empty());
				for (int i = 1; i <= n; ++i)last_sol[i] = ~Level[i];
				backjumpTo(0);
				return SolveState::SAT;
			}
			decide(next);
			++NDECIDE;
		}
	}
}

inline void printObjBounds(long long lower, long long upper){
	if(upper<INF) printf("c bounds %10lld >= %10lld\n",upper,lower);
	else printf("c bounds          - >= %10lld\n",lower);
}

void handleNewSolution(const intConstr& origObj, long long& lastObjectiveBoundID){
	int prev_val = last_sol_obj_val; _unused(prev_val);
	last_sol_obj_val = -origObj.getRhs();
	for(int v: origObj.vars) last_sol_obj_val+=origObj.coefs[v]*last_sol[v];
	assert(last_sol_obj_val<prev_val);

	origObj.copyTo(tmpConstraint,true);
	tmpConstraint.addRhs(-last_sol_obj_val+1);
	lastObjectiveBoundID=last_proofID+1; // The next constraint added to the proof will be the unaltered upper bound
	CRef cr = addInputConstraint(tmpConstraint);
	tmpConstraint.reset();
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
	// core
	std::vector<int> lhs;
	std::vector<int> introducedVars;
	int rhs;
	// info
	int mult; // TODO: add long long to int check?
	int idx;
	int nvars;

	LazyVar(intConstr& core, int startvar, int m):
		introducedVars{startvar},rhs(core.getDegree()),mult(m),idx(0),nvars(core.vars.size()-rhs){
		assert(core.isCardinality());
		lhs.reserve(core.vars.size());
		for(int v: core.vars) lhs.push_back(core.getLit(v));
	}

	int getCurrentVar() const { return introducedVars.back(); }
	void addVar(int v) { introducedVars.push_back(v); }

	void getAtLeastConstraint(intConstr& out) const {
		// X >= (k+i+1)yi (equivalent to yi ==> X>=k+i+1)
		assert(out.isReset());
		for(int l: lhs) out.addLhs(1,l);
		out.addLhs(-(rhs+idx+1),getCurrentVar());
	}

	void getAtMostConstraint(intConstr& out) const {
		// ~X >= (n-k-i)~yi (equivalent to ~yi ==> X=<k+i)
		assert(out.isReset());
		for(int l: lhs) out.addLhs(1,-l);
		out.addLhs(-(lhs.size()-rhs-idx),-getCurrentVar());
	}

	void getSymBreakingConstraint(intConstr& out, int prevvar) const {
		// y-- + ~y >= 1 (equivalent to y-- >= y)
		assert(idx>0);
		assert(out.isReset());
		out.addRhs(1);
		out.addLhs(1,prevvar);
		out.addLhs(1,-getCurrentVar());
	}
};

std::ostream & operator<<(std::ostream & o, const LazyVar* lv) {
	o << lv->idx << " " << lv->nvars << " | ";
	for(int v: lv->introducedVars) o << v << " ";
	o << "| ";
	for(int l: lv->lhs) o << "+x" << l << " ";
	o << ">= " << lv->rhs;
	return o;
}

void checkLazyVariables(longConstr& reformObj, intConstr& core,
		std::vector<LazyVar*>& lazyVars, longConstr& coreAggregate){ // introduce new lazy variables if needed
	for(int i=0; i<(int)lazyVars.size(); ++i){
		LazyVar* lv=lazyVars[i];
		if(reformObj.getLit(lv->getCurrentVar())==0){
			lv->idx++;
			if(lv->idx==lv->nvars){ swapErase(lazyVars,i--); delete lv; continue; } // TODO: clean up CRefs in lv
			// add auxiliary variable
			long long newN = n+1;
			setNbVariables(newN);
			reformObj.resize(newN+1);
			int oldvar = lv->getCurrentVar();
			lv->addVar(newN);
			// reformulate the objective
			reformObj.addLhs(lv->mult,newN);
			// add necessary lazy constraints
			lv->getAtLeastConstraint(tmpConstraint);
			addInputConstraint(tmpConstraint);
			tmpConstraint.reset();
			lv->getAtMostConstraint(tmpConstraint);
			addInputConstraint(tmpConstraint);
			tmpConstraint.reset();
			assert(tmpConstraint.isReset());
			lv->getSymBreakingConstraint(tmpConstraint,oldvar);
			addInputConstraint(tmpConstraint);
			tmpConstraint.reset();
		}
	}
	core.resize(n+1);
	coreAggregate.resize(n+1);
}

void handleInconsistency(longConstr& reformObj, intConstr& core, long long& lower_bound,
                         std::vector<LazyVar*>& lazyVars, longConstr& coreAggregate, intConstr& origObj){
	// take care of derived unit lits and remove zeroes
	reformObj.removeUnitsAndZeroes(false);
	origObj.removeUnitsAndZeroes(false);
	coreAggregate.removeUnitsAndZeroes(false);
	long long prev_lower = lower_bound; _unused(prev_lower);
	lower_bound = -reformObj.getDegree();
	if(core.getDegree()==0){
		assert(lower_bound>prev_lower);
		checkLazyVariables(reformObj,core,lazyVars,coreAggregate);
		return; // apparently only unit assumptions were derived
	}
	// figure out an appropriate core
	core.simplifyToCardinality(false);

	// adjust the lower bound
	if(core.getDegree()>1) ++NCORECARDINALITIES;
	long long mult = INF;
	for(int v: core.vars){
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
		coreAggregate.resize(newN+1);
		reformObj.resize(newN+1);
		// reformulate the objective
		reformObj.add(core,-mult,false);
		reformObj.addLhs(mult,newN); // add only one variable for now
		assert(lower_bound==-reformObj.getDegree());
		// add first lazy constraint
		LazyVar* lv = new LazyVar(core,newN,mult);
		lazyVars.push_back(lv);
		lv->getAtLeastConstraint(tmpConstraint);
		addInputConstraint(tmpConstraint);
		tmpConstraint.reset();
		lv->getAtMostConstraint(tmpConstraint);
		addInputConstraint(tmpConstraint);
		tmpConstraint.reset();
	}else{
		// add auxiliary variables
		long long oldN = n;
		long long newN = oldN-core.getDegree()+core.vars.size();
		setNbVariables(newN);
		core.resize(newN+1);
		coreAggregate.resize(newN+1);
		reformObj.resize(newN+1);
		// reformulate the objective
		for(int v=oldN+1; v<=newN; ++v) core.addLhs(-1,v);
		core.copyTo(tmpConstraint,true);
		reformObj.add(tmpConstraint,mult,false);
		assert(lower_bound==-reformObj.getDegree());
		// add channeling constraints
		addInputConstraint(tmpConstraint);
		tmpConstraint.reset();
		core.copyTo(tmpConstraint);
		assert(tmpConstraint.isCardinality());
		addInputConstraint(tmpConstraint);
		// NOTE: addInputConstraint constructs the right proofID for tmpConstraint,
		// but coreAggregate's construction is only correct if tmpConstraint is not mutated by addInputConstraint.
		// Due to tmpConstraint being a simple cardinality, this is the case.
		coreAggregate.add(tmpConstraint,mult,false);
		tmpConstraint.reset();
		for(int v=oldN+1; v<newN; ++v){ // add symmetry breaking constraints
			assert(tmpConstraint.isReset());
			tmpConstraint.addRhs(1);
			tmpConstraint.addLhs(1,v);
			tmpConstraint.addLhs(1,-v-1);
			addInputConstraint(tmpConstraint);
			tmpConstraint.reset();
		}
	}
	checkLazyVariables(reformObj,core,lazyVars,coreAggregate);
}

void optimize(intConstr& origObj, intConstr& core){
	assert(origObj.vars.size() > 0);
	// NOTE: -origObj.getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
	origObj.removeUnitsAndZeroes(false);
	long long lower_bound = -origObj.getDegree();

	long long opt_coef_sum = 0;
	for (int v: origObj.vars) opt_coef_sum+=std::abs(origObj.coefs[v]);
	if (opt_coef_sum > (long long)1e9) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});

	longConstr reformObj;
	origObj.copyTo(reformObj);
	longConstr coreAggregate;
	coreAggregate.resize(n+1);
	long long lastObjectiveBoundID = 0;

	IntSet assumps;
	std::vector<LazyVar*> lazyVars;
	size_t upper_time=0, lower_time=0;
	SolveState reply = SolveState::UNSAT;
	while(true){
		size_t current_time=DETERMINISTICTIME;
		if(reply!=SolveState::INPROCESSING) printObjBounds(lower_bound,last_sol_obj_val);
		assumps.reset();
		if(opt_mode==1 || opt_mode==2 || (opt_mode>2 && lower_time<upper_time)){ // use core-guided step
			reformObj.removeZeroes();
			for(int v: reformObj.vars) { assert(reformObj.getLit(v)!=0); assumps.add(-reformObj.getLit(v)); }
			std::sort(assumps.keys.begin(),assumps.keys.end(),[&](int l1,int l2){
				return reformObj.getCoef(-l1)>reformObj.getCoef(-l2) ||
				       (reformObj.getCoef(-l1)==reformObj.getCoef(-l2) && std::abs(l1)<std::abs(l2));
			});
		}
		assert(last_sol_obj_val>lower_bound);
		reply = solve(assumps,core);
		assert(decisionLevel()==0);
		if(assumps.size()==0) upper_time+=DETERMINISTICTIME-current_time;
		else lower_time+=DETERMINISTICTIME-current_time;
		if(reply==SolveState::SAT){
			++NSOLS;
			handleNewSolution(origObj,lastObjectiveBoundID);
			assert((opt_mode!=1 && opt_mode!=2) || lower_bound==last_sol_obj_val);
		}	else if(reply==SolveState::UNSAT) {
			++NCORES;
			if(core.getSlack()<0){
				if(logProof()) core.logInconsistency();
				assert(decisionLevel()==0);
				exit_UNSAT();
			}
			handleInconsistency(reformObj,core,lower_bound,lazyVars,coreAggregate,origObj);
		} // else reply==SolveState::INPROCESSING, keep looping
		if(lower_bound>=last_sol_obj_val){
			printObjBounds(lower_bound,last_sol_obj_val);
			origObj.copyTo(tmpConstraint,true);
			tmpConstraint.addRhs(-last_sol_obj_val+1);
			tmpConstraint.resetBuffer(lastObjectiveBoundID); assert(lastObjectiveBoundID>0);
			coreAggregate.add(tmpConstraint,1,false);
			tmpConstraint.reset();
			coreAggregate.postProcess(true);
			if(logProof()) coreAggregate.logInconsistency();
			//assert(coreAggregate.getSlack()<0); // TODO: comment for lazy optimization
			assert(decisionLevel()==0);
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
	std::cout << "c #variables=" << orig_n << " #constraints=" << formula_constrs.size() << std::endl;

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
