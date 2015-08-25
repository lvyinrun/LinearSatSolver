#ifndef SOLVER_H
#define SOLVER_H

#include <stdio.h>
#include "SolverTypes.h"
#include "../tl/Vec.h"
#include "../tl/Alloc.h"
#include "../tl/Sort.h"
#include "../tl/Alg.h"
#include "../tl/Heap.h"

#include "../utils/Options.h"
typedef int Var;

#define l_Undef (lbool((uint8_t)2))
typedef RegionAllocator<uint32_t>::Ref CRef;


class Solver
{
protected:
	// Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }
    struct Watcher
    {
        CRef cref;
        LitArith  blocker;
        Watcher(CRef cr, LitArith p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const
        {
            return cref == w.cref;
        }
        bool operator!=(const Watcher& w) const
        {
            return cref != w.cref;
        }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const
        {
            return ca[w.cref].mark() == 1;
        }
    };

    struct VarOrderLt {
        const IntMap<Var, double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const IntMap<Var, double>&  act) : activity(act) { }
    };

	struct ShrinkStackElem {
        uint32_t i;
        LitArith      l;
        ShrinkStackElem(uint32_t _i, LitArith _l) : i(_i), l(_l){}
    };

public:
// personal defined variables

	vec<int> litPosition;


	LitArith findLiteral(int x){
		int lower = 0, upper = litPosition.size();
		int middle = -1;
		while(lower < upper-1 ){
			middle = ( lower + upper )/2;
			if(litPosition[middle]>x) upper = middle;
			else if(litPosition[middle]<x) lower = middle;
			else if(litPosition[middle]==x) {lower = middle;break;}
		}
		if(litPosition[lower]<=x) lower++;
		Clause &c = ca[clauses[lower]];
		for(int i=0;i<c.size();i++){
			if(c[i].x==x) return c[i];
		}

		return lit_Undef;

	}
    Solver();
    virtual ~Solver();
    // Problem specification:
    //
    Var     newVar    (lbool upol = l_Undef, bool dvar = true); // Add a new variable with parameters specifying variable mode.
	Var     newVar    (LitArith &lit, lbool upol = l_Undef, bool dvar = true);
    bool    addClause (const vec<LitArith>& ps);                     // Add a clause to the solver.
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (LitArith p);                                  // Add a unit clause to the solver.
    bool    addClause (LitArith p, LitArith q);                           // Add a binary clause to the solver.
    bool    addClause (LitArith p, LitArith q, LitArith r);                    // Add a ternary clause to the solver.
    bool    addClause (LitArith p, LitArith q, LitArith r, LitArith s);             // Add a quaternary clause to the solver.

    //bool	addClauseArith ( vec<LitArith> & ps);
    bool    addClause_(      vec<LitArith>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
    bool	addClauseArith_( vec<LitArith> & ps);
    // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
	//bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<LitArith>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    // Solver state:
    //

    Var       next_var;         // Next variable to be created.
    ClauseAllocator     ca;

	vec<VarBound>		bounds;   //Lists of bounds of all variables
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<LitArith>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<LitArith>            assumptions;      // Current set of assumptions provided to solve by the user.

	VMap<double>        activity;         // A heuristic measurement of the activity of a variable.
    VMap<lbool>         assigns;          // The current assignments.
    VMap<char>          polarity;         // The preferred polarity of each variable.
	VMap<lbool>         user_pol;         // The users preferred polarity of each variable.
    VMap<VarData>       vardata;          // Stores reason and level for each variable.
	OccLists<Var, vec<Watcher>, WatcherDeleted, MkIndexLit> watches;
	//not to watch lit,but variables
    // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
	Heap<Var,VarOrderLt>order_heap;       // A priority queue of variables ordered with respect to the variable activity.

    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    double              cla_inc;          // Amount to bump next clause with.
    double              var_inc;          // Amount to bump next variable with.
	int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    VMap<char>          decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    double              progress_estimate;// Set by 'search()'.
//    Heap<Var,VarOrderLt>order_heap;       // A priority queue of variables ordered with respect to the variable activity.

	bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    vec<Var>            released_vars;
    vec<Var>            free_vars;

    // Variable mode:
    //
    void    setPolarity    (Var v, lbool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b);  // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (LitArith p) const;       // The current value of a literal.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;
    void    printStats ()      const;       // Print some current statistics to standard output.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

	// Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    LSet       conflict;          // If problem is unsatisfiable (possibly under assumptions),


    // Mode of operation:
    //
    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.
    int       min_learnts_lim;    // Minimum number to set the learnts limit to.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, num_clauses, num_learnts, clauses_literals, learnts_literals, max_literals, tot_literals;


    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    VMap<char>          seen;
    vec<ShrinkStackElem>analyze_stack;
    vec<LitArith>            analyze_toclear;
    vec<LitArith>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

	// Main internal methods
	void     insertVarOrder   (Var x);              // Insert a variable in the decision order priority queue.
    void     uncheckedEnqueue (LitArith p, CRef from = CRef_Undef); // Enqueue a literal. Assumes value of literal is undefined.
    CRef     propagate        ();                              // Perform unit propagation. Returns possibly conflicting clause.
    void     removeSatisfied  (vec<CRef>& cs);                  // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();
    lbool    solve_           ();                            // Main solve method (assumptions given in 'assumptions').
    void     cancelUntil      (int level);                   // Backtrack until a certain level.
    lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
    void     analyze          (CRef confl, vec<LitArith>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    bool     litRedundant     (LitArith p);                                                 // (helper method for 'analyze()')
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     analyzeFinal     (LitArith p, LSet& out_conflict);                             // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    LitArith      pickBranchLit    ();                                                      // Return the next decision variable.


    // Maintaining Variable/Clause activity:
    //
	void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
	void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.


    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     isRemoved        (CRef cr) const;         // Test if a clause has been removed.
    // Misc:
    //
	CRef     reason           (Var x) const;
    int decisionLevel()      const; // Gives the current decisionlevel.
    bool     withinBudget     ()      const;
    void     relocAll         (ClauseAllocator& to);
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...

	//new options
	lbool AssertBounds(LitArith la){
		if(la.o==OPTR_GRTEQ){
			if(la.v<=bounds[la.vn].lower) return lbool(true);
			else if(la.v<=bounds[la.vn].upper) {bounds[la.vn].lower = la.v;return lbool(true);}
		}else if(la.o == OPTR_LESSEQ){
			if(la.v >= bounds[la.vn].upper) return lbool(true);
			else if(la.v>=bounds[la.vn].lower){bounds[la.vn].upper = la.v;return lbool(true);}
		}
		return lbool(false);
	}


    //Arith helpers
    void displayClauses(){
		printf("\n\n\n****************   Display Clause  ***************\n");
		printf("%d\n\n",clauses.size());
		for(int i=0;i<clauses.size();i++){
			int k = clauses[i];
			printf("Clause %d:\n",k+1);
			displayOneClause(ca[k]);
		}
    }
    void displayOneClause(Clause &cla){
		int k = cla.header.size;
		printf(" size:%d\n",k);
		for(int i=0;i<k;i++){
			printf(" %d %s %d %f\t",cla.data[i].lit.x, VarName[cla.data[i].lit.vn].c_str(),cla.data[i].lit.o,cla.data[i].lit.v);
		}
		printf("\n");
    }

    void displayWatchList(){
		printf("\n\n\n****************   Display Watches  ***************\n");
		for(int i=0;i<VarName.size();i++){
			vec<Watcher> ws = watches.lookup(i);
			printf(" order:%d\n",i);
			Watcher        *j, *end;
			for(j = (Watcher*)ws, end = j + ws.size();  j != end;j++){
				printf("  %d %s %d %f\t",j->cref,VarName[j->blocker.vn].c_str(),j->blocker.o,j->blocker.v);
			}
			printf("\n");
		};
    }

    void displayOneWatch(vec<Watcher> & wc){
		printf("\n\n\n****************   Display One Watch  ***************\n");
		for(int j=0;j<wc.size();j++){
				printf("  %d %s %d %f\t",wc[j].cref,VarName[wc[j].blocker.vn].c_str(),wc[j].blocker.o,wc[j].blocker.v);
			}printf("\n");
    }

    void displayBounds(){
		printf("\n\n\n****************   Display Bounds ***************\n");
		for(int i=0;i<VarName.size();i++){
			printf("%ef\t%s\t%ef\n",bounds[i].lower,VarName[i].c_str(),bounds[i].upper);
		}
    }

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

private:
};




inline CRef Solver::reason(Var x) const { return vardata[x].reason; }

inline int  Solver::level (Var x) const { return vardata[x].level; }

inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }

inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline bool     Solver::addClause       (const vec<LitArith>& ps)
{
    ps.copyTo(add_tmp);
    return addClause_(add_tmp);
}
inline bool     Solver::addEmptyClause  ()
{
    add_tmp.clear();
    return addClause_(add_tmp);
}
inline bool     Solver::addClause       (LitArith p)
{
    add_tmp.clear();
    add_tmp.push(p);
    return addClause_(add_tmp);
}
inline bool     Solver::addClause       (LitArith p, LitArith q)
{
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    return addClause_(add_tmp);
}
inline bool     Solver::addClause       (LitArith p, LitArith q, LitArith r)
{
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    add_tmp.push(r);
    return addClause_(add_tmp);
}
inline bool     Solver::addClause       (LitArith p, LitArith q, LitArith r, LitArith s)
{
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    add_tmp.push(r);
    add_tmp.push(s);
    return addClause_(add_tmp);
}

inline bool     Solver::isRemoved       (CRef cr)         const { return ca[cr].mark() == 1; }

inline int      Solver::decisionLevel ()      const
{
    return trail_lim.size();
}

inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (LitArith p) const   {
	if(p==lit_Undef) return l_True;
	if(p.o == OPTR_GRTEQ ){
		if(p.v<=bounds[p.vn].lower) return lbool(true);
		else if(p.v >= bounds[p.vn].upper) return lbool(false);
		else return l_Undef;
	}else if(p.o == OPTR_LESSEQ){
		if(p.v <=bounds[p.vn].lower) return lbool(false);
		else if(p.v >=bounds[p.vn].upper) return lbool(true);
		else return l_Undef;
	}
	return l_Undef;
 //return assigns[var(p)];
 }



inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return num_clauses; }
inline int      Solver::nLearnts      ()      const   { return num_learnts; }
inline int      Solver::nVars         ()      const   { return next_var; }
// TODO: nFreeVars() is not quite correct, try to calculate right instead of adapting it like below:
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, lbool b){ user_pol[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b)
{
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }



// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline lbool    Solver::solveLimited  (const vec<LitArith>& assumps){
	assumps.copyTo(assumptions);
	return solve_();
}

#endif // SOLVER_H
