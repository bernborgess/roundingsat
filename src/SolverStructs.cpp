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

#include "SolverStructs.hpp"
#include "Solver.hpp"

void Constr::undoFalsified(int i) {
	assert(!isSimple());
	assert(isCounting() || isWatched(i));
	++stats.NWATCHLOOKUPSBJ;
	slack += abs(data[i]);
}

WatchStatus Constr::propagateWatch(CRef cr, int& idx, Lit p, Solver& S){
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

void ConstraintAllocator::capacity(uint32_t min_cap){
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
CRef ConstraintAllocator::alloc(intConstr& constraint, ConstraintType type){
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

// segment tree (fast implementation of priority queue).
void OrderHeap::resize(int newsize) {
	if (cap >= newsize) return;
	// insert elements in such order that tie breaking remains intact
	std::vector<Var> variables;
	while (!empty()) variables.push_back(removeMax());
	tree.clear();
	while(cap<newsize) cap=cap*options.resize_factor+1;
	tree.resize(2*(cap+1), -1);
	for (Var x : variables) insert(x);
}
void OrderHeap::percolateUp(Var x) {
	for(int at=x+cap+1; at>1; at>>=1){
		if(tree[at^1]==-1 || activity[x]>activity[tree[at^1]])tree[at>>1]=x;
		else break;
	}
}
bool OrderHeap::empty() const { return tree[1] == -1; }
bool OrderHeap::inHeap(Var x) const { return tree[x+cap+1] != -1; }
void OrderHeap::insert(Var x) {
	assert(x<=cap);
	if (inHeap(x)) return;
	tree[x+cap+1] = x;
	percolateUp(x);
}
Var OrderHeap::removeMax() {
	Var x = tree[1];
	assert(x != -1);
	tree[x+cap+1] = -1;
	for(int at=x+cap+1; at>1; at>>=1){
		if(tree[at^1] != -1 && (tree[at]==-1 || activity[tree[at^1]]>activity[tree[at]]))
			tree[at>>1]=tree[at^1];
		else tree[at>>1]=tree[at];
	}
	return x;
}