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

#pragma once

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
#include "Options.hpp"
#include "globals.hpp"

struct Solver {

// ---------------------------------------------------------------------
// Internal datastructures

	struct CRef {
		uint32_t ofs;
		bool operator==(CRef const&o)const{return ofs==o.ofs;}
		bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
		bool operator< (CRef const&o)const{return ofs< o.ofs;}
		std::ostream& operator<<(std::ostream& os) { return os << ofs; }
	};
	const CRef CRef_Undef = { UINT32_MAX };


	struct Watch {
		CRef cref;
		int idx; // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
		Watch(CRef cr, int i):cref(cr),idx(i){};
		bool operator==(const Watch& other)const{return other.cref==cref && other.idx==idx;}
	};

	enum WatchStatus { FOUNDNEW, FOUNDNONE, CONFLICTING };

	// Variables

	IntSet tmpSet;
	IntSet actSet;

	intConstr tmpConstraint;
	longConstr conflConstraint; // functions as old confl_data
	intConstr logConstraint;

	std::vector<CRef> constraints;
	std::unordered_map<ID,CRef> external;
	std::vector<std::vector<Watch>> _adj={{}}; std::vector<std::vector<Watch>>::iterator adj;
	std::vector<int> _Level={-1}; IntVecIt Level;
	std::vector<Lit> trail;
	std::vector<int> trail_lim, Pos;
	std::vector<CRef> Reason;
	int qhead; // for unit propagation
	std::vector<Lit> phase;
	std::vector<double> activity;
	inline int decisionLevel() { return trail_lim.size(); }

	long long nbconstrsbeforereduce=2000;
	long long nconfl_to_restart=0;
	double v_vsids_inc=1.0;
	double c_vsids_inc=1.0;

	// ---------------------------------------------------------------------
	// ---------------------------------------------------------------------
	struct Constr { // internal constraint optimized for fast propagation
		static int sz_constr(int length){ return (sizeof(Constr)+sizeof(int)*length)/sizeof(uint32_t); }
		ID id;
		Val degree;
		// NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
		struct {
			unsigned unused       : 1;
			unsigned type         : 2;
			unsigned lbd          : 29;
			unsigned markedfordel : 1;
			unsigned counting     : 1;
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
		inline void setType(ConstraintType t){ header.type=(unsigned int) t; }
		inline ConstraintType getType() const { return (ConstraintType) header.type; }
		inline void setLBD(unsigned int lbd){ header.lbd=std::min(header.lbd,lbd); }
		inline unsigned int lbd() const { return header.lbd; }
		inline bool isMarkedForDelete() const { return header.markedfordel; }
		inline void markForDel(){ header.markedfordel=1; }
		inline bool isCounting() const { return header.counting; }
		inline void setCounting(bool c){ header.counting=(unsigned int) c; }
		inline Coef largestCoef() const { assert(!isSimple()); return std::abs(data[0]); }
		inline Coef coef(unsigned int i) const { return isSimple()?1:std::abs(data[i<<1]); }
		inline Lit lit(unsigned int i) const { return isSimple()?data[i]:data[(i<<1)+1]; }
		inline bool isWatched(unsigned int i) const { assert(!isSimple()); return data[i]<0; }
		inline void undoFalsified(int i) {
			assert(!isSimple());
			assert(isCounting() || isWatched(i));
			++stats.NWATCHLOOKUPSBJ;
			slack += abs(data[i]); // TODO: slack -= data[i] when only watched propagation
		}
		inline WatchStatus propagateWatch(CRef cr, int& idx, Lit p, Solver& S){
			assert(isFalse(S.Level,p));
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
				if(isTrue(S.Level,otherwatch)){
					idx=otherwatch-INF; // set new blocked literal
					return WatchStatus::FOUNDNONE; // constraint is satisfied
				}
				const unsigned int Csize=size();
				for(unsigned int i=2; i<Csize; ++i){
					Lit l = data[i];
					if(!isFalse(S.Level,l)){
						int mid = i/2+1;
						data[i]=data[mid];
						data[mid]=watch;
						data[widx]=l;
						S.adj[l].emplace_back(cr,otherwatch-INF);
						stats.NWATCHCHECKS+=i-1;
						return WatchStatus::FOUNDNEW;
					}
				}
				stats.NWATCHCHECKS+=Csize-2;
				assert(isFalse(S.Level,watch));
				for(unsigned int i=2; i<Csize; ++i) assert(isFalse(S.Level,data[i]));
				if(isFalse(S.Level,otherwatch)) return WatchStatus::CONFLICTING;
				else{ assert(!isTrue(S.Level,otherwatch)); ++stats.NPROPCLAUSE; S.propagate(otherwatch,cr); }
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
				if(!options.idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=degree+1; }
				assert(watchIdx>degree);
				stats.NWATCHCHECKS-=watchIdx;
				for(; watchIdx<Csize; ++watchIdx){
					Lit l = data[watchIdx];
					if(!isFalse(S.Level,l)){
						unsigned int mid = (watchIdx+degree+1)/2; assert(mid<=watchIdx); assert(mid>degree);
						data[watchIdx]=data[mid];
						data[mid]=data[widx];
						data[widx]=l;
						S.adj[l].emplace_back(cr,(widx<<1)+1);
						stats.NWATCHCHECKS+=watchIdx+1;
						return WatchStatus::FOUNDNEW;
					}
				}
				stats.NWATCHCHECKS+=watchIdx;
				assert(isFalse(S.Level,data[widx]));
				for(unsigned int i=degree+1; i<Csize; ++i) assert(isFalse(S.Level,data[i]));
				for(unsigned int i=0; i<=degree; ++i) if(i!=widx && isFalse(S.Level,data[i])) return WatchStatus::CONFLICTING;
				for(unsigned int i=0; i<=degree; ++i){
					Lit l = data[i];
					if(i!=widx && !isTrue(S.Level,l)){ ++stats.NPROPCARD; S.propagate(l,cr); }
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
					if(!options.idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=0; }
					stats.NPROPCHECKS-=watchIdx>>1;
					for(; watchIdx<Csize2 && data[watchIdx]>slack; watchIdx+=2){
						const Lit l = data[watchIdx+1];
						if(isUnknown(S.Pos,l)){
							stats.NPROPCLAUSE+=(degree==1); stats.NPROPCARD+=(degree!=1 && ClargestCoef==1); ++stats.NPROPCOUNTING;
							S.propagate(l,cr);
						}
					}
					stats.NPROPCHECKS+=watchIdx>>1;
				}
				return WatchStatus::FOUNDNONE;
			}

			// use watched propagation
			if(!options.idxProp || ntrailpops<stats.NTRAILPOPS){ ntrailpops=stats.NTRAILPOPS; watchIdx=0; }
			assert(c<0);
			slack+=c;
			if(!options.supProp || slack-c>=ClargestCoef){ // look for new watches if previously, slack was at least ClargestCoef
				stats.NWATCHCHECKS-=watchIdx>>1;
				for(; watchIdx<Csize2 && slack<ClargestCoef; watchIdx+=2){ // NOTE: first innermost loop of RoundingSat
					const Coef cf = data[watchIdx];
					const Lit l = data[watchIdx+1];
					if(cf>0 && !isFalse(S.Level,l)){
						slack+=cf;
						data[watchIdx]=-cf;
						S.adj[l].emplace_back(cr,watchIdx);
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
				if(isUnknown(S.Pos,l)){
					stats.NPROPCLAUSE+=(degree==1); stats.NPROPCARD+=(degree!=1 && ClargestCoef==1); ++stats.NPROPWATCH;
					S.propagate(l,cr);
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

		std::ostream & operator<<(std::ostream & o) {
			for(size_t i=0;i<size();++i){ o << coef(i) << "x" << lit(i) << " "; }
			o << ">= " << degree << "\n";
			return o;
		}
	};

	// ---------------------------------------------------------------------
	// Memory. Maximum supported size of learnt constraint database is 16GB

	class OutOfMemoryException{};
	static inline void* xrealloc(void *ptr, size_t size){
		void* mem = realloc(ptr, size);
		if(mem == NULL && errno == ENOMEM) throw OutOfMemoryException();
		else return mem;
	}
	struct {
		uint32_t* memory; // TODO: why not uint64_t?
		uint32_t at=0, cap=0;
		uint32_t wasted=0; // for GC
		ID crefID = 0;
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
		CRef alloc(intConstr& constraint, ConstraintType type){
			assert(constraint.getDegree()>0);
			assert(constraint.getDegree()<INF);
			assert(constraint.isSaturated());
			// as the constraint is saturated, the coefficients are between 1 and 1e9 as well.
			assert(!constraint.vars.empty());
			unsigned int length = constraint.vars.size();
			bool asClause = options.clauseProp && constraint.getDegree()==1;
			bool asCard = !asClause && options.cardProp && constraint.isCardinality();

			// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
			// during maintenance of watches the order will be shuffled.
			uint32_t old_at = at;
			at += Constr::sz_constr(length+((asClause||asCard)?0:length));
			capacity(at);
			Constr* constr = (Constr*)(memory+old_at);
			new (constr) Constr;
			constr->id = logger?logger->last_proofID:++crefID; assert(constr->id>0);
			constr->act = 0;
			constr->degree = constraint.getDegree();
			constr->header = {0,(unsigned int)type,0x1FFFFFFF,0,0,length};
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


		int heap_cap=0;
		// segment tree (fast implementation of priority queue).
		std::vector<Var> heap_tree = {-1,-1};
		void heap_resize(int newsize) {
			if (heap_cap >= newsize) return;
			// insert elements in such order that tie breaking remains intact
			std::vector<Var> variables;
			while (!heap_empty()) variables.push_back(heap_removeMax());
			heap_tree.clear();
			while(heap_cap<newsize) heap_cap=heap_cap*options.resize_factor+1;
			heap_tree.resize(2*(heap_cap+1), -1);
			for (Var x : variables) heap_insert(x);
		}
		void heap_percolateUp(Var x) {
			for(int at=x+heap_cap+1; at>1; at>>=1){
				if(heap_tree[at^1]==-1 || activity[x]>activity[heap_tree[at^1]])heap_tree[at>>1]=x;
				else break;
			}
		}
		bool heap_empty() { return heap_tree[1] == -1; }
		bool heap_inHeap(Var x) { return heap_tree[x+heap_cap+1] != -1; }
		void heap_insert(Var x) {
			assert(x<=heap_cap);
			if (heap_inHeap(x)) return;
			heap_tree[x+heap_cap+1] = x;
			heap_percolateUp(x);
		}
		Var heap_removeMax() {
			Var x = heap_tree[1];
			assert(x != -1);
			heap_tree[x+heap_cap+1] = -1;
			for(int at=x+heap_cap+1; at>1; at>>=1){
				if(heap_tree[at^1] != -1 && (heap_tree[at]==-1 || activity[heap_tree[at^1]]>activity[heap_tree[at]]))
					heap_tree[at>>1]=heap_tree[at^1];
				else heap_tree[at>>1]=heap_tree[at];
			}
			return x;
		}

	void vDecayActivity() { v_vsids_inc *= (1 / options.v_vsids_decay); }
	void vBumpActivity(Var v){
		assert(v>0);
		if ( (activity[v] += v_vsids_inc) > 1e100 ) { // Rescale
			for (Var x=1; x<=n; ++x) activity[x] *= 1e-100;
			v_vsids_inc *= 1e-100;
		}
		// Update heap with respect to new activity:
		if (heap_inHeap(v)) heap_percolateUp(v);
	}

	void cDecayActivity() { c_vsids_inc *= (1 / options.c_vsids_decay); }
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

	CRef attachConstraint(intConstr& constraint, ConstraintType type){
		assert(constraint.isSortedInDecreasingCoefOrder());
		assert(constraint.isSaturated());
		assert(constraint.hasNoZeroes());
		assert(constraint.hasNoUnits(Level));
		assert(constraint.getDegree()>0);
		assert(constraint.vars.size()>0);

		if(logger) constraint.logProofLine("a", stats);
		CRef cr = ca.alloc(constraint,type);
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
		C.setCounting(options.countingProp==1 || options.countingProp>(1-minWatches/(float)C.size()));

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
		heap_insert(v);
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

	bool analyze(CRef confl){
		Constr& C = ca[confl];
		if (C.getType()==ConstraintType::LEARNT) {
			cBumpActivity(C);
			recomputeLBD(C);
		}

		C.toConstraint(conflConstraint);
		stats.NADDEDLITERALS+=conflConstraint.vars.size();
		conflConstraint.removeUnitsAndZeroes(Level,Pos);
		assert(actSet.size()==0); // will hold the literals that need their activity bumped
		for(Var v: conflConstraint.vars) actSet.add(conflConstraint.getLit(v));
		while(decisionLevel()>0){
			if(asynch_interrupt) return false;
			Lit l = trail.back();
			assert(std::abs(conflConstraint.getCoef(-l))<INF);
			Coef confl_coef_l = conflConstraint.getCoef(-l);
			if(confl_coef_l>0) {
				if (conflConstraint.falsifiedAtLvlisOne(Level,decisionLevel())) break;
				assert(Reason[std::abs(l)] != CRef_Undef);
				if(options.originalRoundToOne){
					conflConstraint.roundToOne(Level,confl_coef_l,false);
					confl_coef_l=1;
				}
				Constr& reasonC = ca[Reason[std::abs(l)]];
				if (reasonC.getType()==ConstraintType::LEARNT) {
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
					if(options.originalRoundToOne){ tmpConstraint.weaken(-(tmpConstraint.getCoef(l)%div),l); tmpConstraint.saturate(); }
					tmpConstraint.roundToOne(Level,div,!options.originalRoundToOne);
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
		return true;
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
				if(C.isMarkedForDelete()){ aux::swapErase(ws,it_ws--); continue; }
				WatchStatus wstat = C.propagateWatch(cr,ws[it_ws].idx,-p,*this);
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
			if (heap_empty()) return 0;
			else next = heap_removeMax();
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
		assert(nvars>0);
		assert(nvars<INF);
		if (nvars <= n) return;
		aux::resizeIntMap(_adj,adj,nvars,options.resize_factor,{});
		aux::resizeIntMap(_Level,Level,nvars,options.resize_factor,-1);
		Pos.resize(nvars+1,-1);
		Reason.resize(nvars+1,CRef_Undef);
		activity.resize(nvars+1,0);
		phase.resize(nvars+1);
		tmpConstraint.resize(nvars+1);
		conflConstraint.resize(nvars+1);
		logConstraint.resize(nvars+1);
		heap_resize(nvars+1);
		for(Var v=n+1;v<=nvars;++v) phase[v] = -v, heap_insert(v);
		n = nvars;
	}

	// ---------------------------------------------------------------------
	// Constraint addition

	bool learnConstraint(longConstr& confl){
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
			assert(decisionLevel()==0);
			if(logger) tmpConstraint.logInconsistency(Level,Pos,stats);
			return false;
		}
		tmpConstraint.heuristicWeakening(Level,Pos,slk,stats);
		tmpConstraint.postProcess(Level,Pos,false,stats);
		assert(tmpConstraint.isSaturated());

		CRef cr = attachConstraint(tmpConstraint,ConstraintType::LEARNT);
		tmpConstraint.reset();
		Constr& C = ca[cr];
		recomputeLBD(C);
		return true;
	}

	ID addInputConstraint(ConstraintType type){
		assert(decisionLevel()==0);
		if(logger) tmpConstraint.logAsInput();
		tmpConstraint.postProcess(Level,Pos,true,stats);
		assert(tmpConstraint.getDegree()<INF);
		if(tmpConstraint.getDegree()<=0) return ID_Undef; // already satisfied.

		if(tmpConstraint.getSlack(Level)<0){
			puts("c Inconsistent input constraint");
			if(logger) tmpConstraint.logInconsistency(Level,Pos,stats);
			assert(decisionLevel()==0);
			return ID_Unsat;
		}

		CRef cr = attachConstraint(tmpConstraint,type);
		CRef confl = runPropagation();
		if (confl != CRef_Undef){
			puts("c Input conflict");
			if(logger){
				ca[confl].toConstraint(logConstraint);
				logConstraint.logInconsistency(Level,Pos,stats);
				logConstraint.reset();
			}
			assert(decisionLevel()==0);
			return ID_Unsat;
		}
		ID id = ca[cr].id;
		if(type==ConstraintType::EXTERNAL) external[id]=cr;
		return id;
	}

	ID addConstraint(const intConstr& c, ConstraintType type){
		c.copyTo(tmpConstraint);
		ID result = addInputConstraint(type);
		tmpConstraint.reset();
		return result;
	}

	ID addConstraint(const std::vector<Coef>& coefs, const std::vector<Lit>& lits, const Val rhs, ConstraintType type){
		// NOTE: copy to tmpConstraint guarantees original constraint is not changed and does not need logger
		tmpConstraint.construct(coefs,lits,rhs);
		ID result = addInputConstraint(type);
		tmpConstraint.reset();
		return result;
	}

	void removeConstraint(Constr& C){
		assert(decisionLevel()==0);
		assert(C.getType()!=ConstraintType::EXTERNAL);
		assert(!C.isMarkedForDelete());
		C.markForDel();
		ca.wasted += C.getMemSize();
	}

	void dropExternal(ID id, bool forceDelete) {
		if (id == ID_Undef) return;
		auto old_it = external.find(id);
		assert(old_it != external.end());
		Constr& constr = ca[old_it->second];
		constr.setType(ConstraintType::AUXILIARY);
		if (forceDelete) removeConstraint(constr);
		external.erase(old_it);
	}

	// ---------------------------------------------------------------------
	// Garbage collection

	// We assume in the garbage collection method that reduceDB() is the
	// only place where constraints are deleted.
	void garbage_collect(){
		assert(decisionLevel()==0); // so we don't need to update the pointer of Reason<CRef>
		if (options.verbosity > 0) puts("c GARBAGE COLLECT");
		for(Lit l=-n; l<=n; ++l) for(int i=0; i<(int)adj[l].size(); ++i){
				if(ca[adj[l][i].cref].isMarkedForDelete()) aux::swapErase(adj[l],i--);
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

	void reduceDB(){
		if (options.verbosity > 0) puts("c INPROCESSING");
		assert(decisionLevel()==0);

		std::vector<CRef> learnts;
		learnts.reserve(constraints.size()/2);

		size_t totalLearnts=0;
		size_t promisingLearnts=0;
		for(CRef& cr: constraints){
			Constr& C = ca[cr];
			if(C.isMarkedForDelete() || C.getType()==ConstraintType::EXTERNAL) continue;
			Val eval = -C.degree;
			for(int j=0; j<(int)C.size() && eval<0; ++j) if(isUnit(Level,C.lit(j))) eval+=C.coef(j);
			if(eval>=0) removeConstraint(C); // remove constraints satisfied at root
			else if(C.getType()==ConstraintType::LEARNT){
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
		for(; i<constraints.size(); ++i) if(!ca[constraints[i]].isMarkedForDelete()) constraints[j++]=constraints[i];
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

	template<class SMALL, class LARGE>
	LARGE assumpSlack(const IntSet& assumptions, const Constraint<SMALL, LARGE>& core){
		LARGE slack = -core.getRhs();
		for(Var v: core.vars) if(assumptions.has(v) || (!assumptions.has(-v) && core.coefs[v]>0)) slack+=core.coefs[v];
		return slack;
	}

	bool extractCore(const IntSet& assumptions, CRef confl, intConstr& outCore, Lit l_assump=0){
		assert(confl!=CRef_Undef);
		outCore.reset();

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
			if(asynch_interrupt) return false;
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
					if(options.originalRoundToOne){ tmpConstraint.weaken(-(tmpConstraint.getCoef(l)%div),l); tmpConstraint.saturate(); }
					tmpConstraint.roundToOne(Level,div,!options.originalRoundToOne);
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
		return true;
	}

	Val lhs(Constr& C, const std::vector<bool>& sol) {
		Val result = 0;
		for (size_t j = 0; j < C.size(); ++j) {
			Lit l = C.lit(j);
			result += ((l > 0) == sol[std::abs(l)]) * C.coef(j);
		}
		return result;
	}
	bool checksol(const std::vector<bool>& sol) {
		for (CRef cr: constraints) {
			Constr& C = ca[cr];
			if (C.getType() == ConstraintType::FORMULA && lhs(C, sol) < C.degree) return false;
		}
		puts("c SATISFIABLE (checked)");
		return true;
	}

	/**
	 * @return:
	 * 	UNSAT if root inconsistency detected
	 * 	SAT if satisfying assignment found
	 * 	INCONSISTENT if no solution extending assumptions exists
	 * 	INTERRUPTED if interrupted by external signal
	 * 	INPROCESSING if solver just finished a cleanup phase
	 * @param assumptions: set of assumptions
	 * @param core: if INCONSISTENT, implied constraint falsified by assumptions, otherwise untouched
	 * 	if core is the empty constraint, at least one assumption is falsified at root
	 * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
	 */
	SolveState solve(const IntSet& assumptions, intConstr& core, std::vector<bool>& solution) {
		backjumpTo(0); // ensures assumptions are reset
		std::vector<int> assumptions_lim={0};
		assumptions_lim.reserve((int)assumptions.size()+1);
		while (true) {
			if(asynch_interrupt) return SolveState::INTERRUPTED;
			CRef confl = runPropagation();
			if (confl != CRef_Undef) {
				if(decisionLevel() == 0){
					if(logger){
						ca[confl].toConstraint(logConstraint);
						logConstraint.logInconsistency(Level,Pos,stats);
						logConstraint.reset();
					}
					return SolveState::UNSAT;
				}
				vDecayActivity();
				cDecayActivity();
				stats.NCONFL++; nconfl_to_restart--;
				if(stats.NCONFL%1000==0){
					if (options.verbosity > 0) {
						printf("c #Conflicts: %10lld | #Constraints: %10lld\n",stats.NCONFL,(long long)constraints.size());
						if(options.verbosity>2){
							// memory usage
							std::cout<<"c total constraint space: "<<ca.cap*4/1024./1024.<<"MB"<<std::endl;
							std::cout<<"c total #watches: ";{long long cnt=0;for(Lit l=-n;l<=n;l++)cnt+=(long long)adj[l].size();std::cout<<cnt<<std::endl;}
						}
					}
				}

				if(decisionLevel()>=(int)assumptions_lim.size()){
					if(!analyze(confl)) return SolveState::INTERRUPTED;
					if(!learnConstraint(conflConstraint)) return SolveState::UNSAT;
					conflConstraint.reset();
				}else{
					if(!extractCore(assumptions,confl,core)) return SolveState::INTERRUPTED;
					return SolveState::INCONSISTENT;
				}
			} else {
				if(nconfl_to_restart <= 0){
					backjumpTo(0);
					double rest_base = luby(options.rinc, ++stats.NRESTARTS);
					nconfl_to_restart = (long long) rest_base * options.rfirst;
					if(stats.NCONFL >= (stats.NCLEANUP+1)*nbconstrsbeforereduce) {
						++stats.NCLEANUP;
						reduceDB();
						while(stats.NCONFL >= stats.NCLEANUP*nbconstrsbeforereduce) nbconstrsbeforereduce += options.incReduceDB;
						return SolveState::INPROCESSING;
					}
				}
				Lit next = 0;
				if((int)assumptions_lim.size()>decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
				if(assumptions_lim.back()<(int)assumptions.size()){
					for(int i=(decisionLevel()==0?0:trail_lim.back()); i<(int)trail.size(); ++i){
						Lit l = trail[i];
						if(assumptions.has(-l)){ // found conflicting assumption
							if(isUnit(Level,l)) backjumpTo(0), core.reset(); // negated assumption is unit
							else if(!extractCore(assumptions,Reason[std::abs(l)],core,-l)) return SolveState::INTERRUPTED;
							return SolveState::INCONSISTENT;
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
					assert(heap_empty());
					assert((int)trail.size()==n);
					solution.clear();
					solution.resize(n+1);
					solution[0]=false;
					for (Var v=1; v<=n; ++v) solution[v]=isTrue(Level,v);
					backjumpTo(0);
					assert(checksol(solution));
					return SolveState::SAT;
				}
				decide(next);
			}
		}
	}

};
