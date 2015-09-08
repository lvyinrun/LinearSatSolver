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
#include <stack>
#include <set>
#include <map>
using namespace std;
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
        LitArith self;
        LitArith  blocker;
        Watcher(CRef cr, LitArith s, LitArith p) : cref(cr), self(s), blocker(p) {}
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
	bool Switch_ALL = false;
    bool Switch_PMatrix = true;
	bool Switch_DisPlay = true;
// personal defined variables
	bool checkFlag = false;
	vec<int> litPosition;

	struct PickedLiteral{
		int clause;
		int var;
		int dl;
		set<int> found;
	};
	map<int,int> LitClauseMap;
	vector<bool> clauseAssigned;
	void buildPickHashMap(){
		for(int i=0;i<clauses.size();i++){
		clauseAssigned.push_back(false);
			int k = clauses[i];
			//printf("\n%d:",i);
			for(int m =0; m< ca[k].header.size;m++){
				//printf("%d\t",ca[k].data[m].lit.x);
				LitClauseMap.insert(pair<int,int>(ca[k].data[m].lit.x,i));
			}
		}
    }
	void print_Lit(LitArith lit){
		if(!Switch_ALL) printf("\nLit %d %s %s %f",lit.x,VarName[lit.vn].c_str(),lit.o==OPTR_GRTEQ?">=":"<=",lit.v);
	}
	int firstOrder = 0;
	stack<PickedLiteral> SearchStack;
	LitArith PickFirstLit(){
		LitArith la = lit_Undef;
        Clause& c = ca[0];
        if(firstOrder>=c.size()) return la;

        PickedLiteral newPl;
		newPl.clause = 0;
		newPl.found.insert(c[firstOrder].x);
		newPl.var = c[firstOrder].x;
		newPl.dl = decisionLevel();
		la = c[firstOrder];
		firstOrder++;
		SearchStack.push(newPl);
		if(!Switch_ALL)printf("\nPick First Literal");
		print_Lit(la);
		return la;
//        if(!satisfied(c)){
//            for (int m = 0; m < c.size(); m++)
//                if (value(c[m]) != l_False)
//                {
//                    PickedLiteral newPl;
//                    newPl.clause = 0;
//                    newPl.found.insert(c[m].x);
//                    newPl.var = c[m].x;
//                    newPl.dl = decisionLevel()+1;
//                    la = c[m];
//                    SearchStack.push(newPl);
//                    printf("\nPick First Literal");
//					print_Lit(la);
//					return la;
//                } }
//			return la;

	}
	LitArith pickBranchLiteral(){
		LitArith la=lit_Undef;
		if(SearchStack.size()==0){
			return PickFirstLit();
		}
		bool unsatisfiedFlag = false;
		while(SearchStack.size()>0){
			PickedLiteral &pl = SearchStack.top();
			int i, j;
//层次区分不够明确，keep on working
		bool loteral = (pl.dl <= decisionLevel());//横向的还是纵向的找（取决于上层是否回溯）
		for (i = loteral?pl.clause+1:pl.clause; i < clauses.size(); i++){
			//当前变量与decision相等说明前面未经回溯，在新的一层寻找。否则说明已经回溯过一层，在当前层寻找

				Clause& c = ca[clauses[i]];
				if(!satisfied(c)){
					unsatisfiedFlag = true;
					for (int m = 0; m < c.size(); m++)
						if (value(c[m]) == l_Undef&&pl.found.find(c[m].x)==pl.found.end()){
							if(i==pl.clause){
							//同一层，替换
								pl.dl = decisionLevel()+1;pl.found.insert(c[m].x);pl.var = c[m].x;
							}
							else{
								PickedLiteral newPl;
								newPl.clause = i;newPl.found.insert(c[m].x);newPl.var = c[m].x;newPl.dl = decisionLevel()+1;
								SearchStack.push(newPl);
							}
							la = c[m];
							goto LitFound;
						}
				}else if(clauseAssigned[i]==false) {
					unsatisfiedFlag = true;
					Clause& c = ca[clauses[i]];
					PickedLiteral newPl;
					newPl.clause = i;newPl.found.insert(c[0].x);newPl.var = c[0].x;newPl.dl = decisionLevel()+1;
					SearchStack.push(newPl);
					la = c[0];
					goto LitFound;
				}
				if(loteral==false) break;
			}
			if(unsatisfiedFlag==false) return lit_AllSatisfied;
			if(la==lit_Undef&&unsatisfiedFlag==true){
				//no branchliteral could be found backtrack
				if(decisionLevel()-1>=0)
					cancelUntil(decisionLevel()-1);
				SearchStack.pop();
			}else{

			}

		}
		LitFound:
		if(!Switch_ALL) printf("\nPick Literal");
		if(!Switch_ALL) print_Lit(la);
		return la;

	}
	bool FindUdefinedLit(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }

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
		if(lower>=clauses.size()) return lit_Undef;
		Clause &c = ca[clauses[lower]];
		for(int i=0;i<c.size();i++){
			if(c[i].x==x) return c[i];
		}

		return lit_Undef;

	}

	void rebuildLitPosition(){
		litPosition.clear();
		for(int i=0;i<clauses.size();i++){
			Clause &c = ca[clauses[i]];
			int max = 0;
			for(int k = 0; k<c.size();k++){
				if(c[k].x>max) max = c[k].x;
			}
			litPosition.push(max);
		}

//		for(int i=0;i<litPosition.size();i++){
//			printf("%d\t",litPosition[i]);
//		}
	}

	void initMatrix(){
	//wrong place
		matrixOut=fopen("a.txt","w");
		matrix=(double *) malloc(sizeof(double)*(LimitsRowNum)*(LimitsVarNum));
		fclose(matrixOut);
	}

	void matrixAddRow(stack<ArithItem> & items,int basic){
	rowNumber++;
	if(rowNumber>MAX_ROW) MAX_ROW = rowNumber;
	//printf("adding matrix %d\n",rowNumber);
		while(items.size()>0){
			ArithItem item = items.top();
			items.pop();
			int colNum = item.item_value.term.variable;
			if(colNum>MAX_COLUMN) MAX_COLUMN = colNum;
			matrix[rowNumber*LimitsVarNum+colNum] = item.item_value.term.coefficient;
			//if(item.type==TERM) printf("%f%s\t",item.item_value.term.coefficient,VarName[item.item_value.term.variable].c_str());
		}
		if(basic>MAX_COLUMN) MAX_COLUMN = basic;
		matrix[(rowNumber)*LimitsVarNum+basic]=-1;
        matrix[basic]=rowNumber;
		//printf("\t%d \n",basic);
	}
    void printBoundAndValue(){
		if(Switch_PMatrix && Switch_ALL) return;
		matrixOut=fopen("a.txt","a");
		fprintf(matrixOut,"\n\n\n****************   Display Bounds ***************\n");
		for(int i=0;i<VarName.size();i++){
			fprintf(matrixOut,"%s\t%ef\t%ef\t%ef\n",VarName[i].c_str(),bounds[i].lower,bounds[i].val,bounds[i].upper);
		}
		fprintf(matrixOut,"\n");
		fclose(matrixOut);
    }
	void printMatrix(){
		if(Switch_PMatrix && Switch_ALL) return;
		matrixOut=fopen("a.txt","a");
		for(int i=0;i<=MAX_ROW;i++){
			for(int j=0;j<=MAX_COLUMN;j++){
				fprintf(matrixOut,"%3.4f\t",matrix[i*LimitsVarNum+j]);
			}fprintf(matrixOut,"\n");
		}fprintf(matrixOut,"\n\n");
		fclose(matrixOut);
		printBoundAndValue();
	}
	void update(int varNumber,double val){
		int rowNum = 0;
		double dval = val - bounds[varNumber].val;
		for(int i=0;i<=MAX_COLUMN;i++){
			rowNum = matrix[i];
			if(rowNum!=0){
				bounds[i].val += matrix[rowNum*LimitsVarNum+varNumber]*dval;
			}
		}
		bounds[varNumber].val = val;
	}

	void InitialSlashVariable(){
		int i=0;
		while(matrix[i]==0&&i<=MAX_COLUMN) i++;
		int nonbasic = i;
		while(i<=MAX_COLUMN){
			double res = 0;
			int rowNum = matrix[i];
			for(int j=0;j<nonbasic;j++){
				res += matrix[rowNum*LimitsVarNum+j] * bounds[j].val;
			}
			bounds[i].val = res;
			i++;
		}

	}
void pivotAndUpdate(int xi,int xj,double v){

};
	bool check(){
		printMatrix();
		CRef    confl     = CRef_Undef;
		while(true){
			int col=0, row=0;
			VarBound bound;
			for(col=0; col <= MAX_COLUMN; col++){
				if(matrix[col]!=0) {
				bound = bounds[col];
					if(bound.val>bound.upper||bound.val<bound.lower) break;
				}
			}
			if(MAX_COLUMN < col) return true;
			//col是基变量，要换入到非基中
			row = matrix[col];
			if(bound.val<bound.lower){
				int i=0;
				for(i=0;i<=MAX_COLUMN;i++){
					if(matrix[i]!=0) continue;
					if((matrix[row*LimitsVarNum + i]>0 && bounds[i].val<bounds[i].upper)||
					   (matrix[row*LimitsVarNum + i]<0 && bounds[i].val>bounds[i].lower)) break;
				}
				if(i>MAX_COLUMN) return false;
				//i is basic variable and need to pivot in
				double oldIvalue = bounds[i].val;

				pivotAndUpdate(row,col,bound.lower);

				double t = -matrix[row*LimitsVarNum+i];


				bounds[i].val = (bounds[col].lower-bounds[col].val)/matrix[row*LimitsVarNum+i]+bounds[i].val;
				//对每个基变量中含xi的值的val进行修改
				for(int k=0;k<=MAX_COLUMN;k++){
					if(matrix[k]!=0){
						int row = matrix[k];
						if(matrix[row*LimitsVarNum+i]!=0){
							bounds[k].val +=  matrix[row*LimitsVarNum+i]*(bounds[i].val- oldIvalue);
						}
					}
				}
				for(int k=0;k<=MAX_COLUMN;k++){
					matrix[row*LimitsVarNum+k] = matrix[row*LimitsVarNum+k]/t;
				}

				for(int m=1;m<=MAX_ROW;m++){
					if(m==row) continue;
					double coeff = matrix[m*LimitsVarNum+i];
					for(int n=0; n<=MAX_COLUMN;n++){
						matrix[m*LimitsVarNum+n] += matrix[row*LimitsVarNum+n]*coeff;
					}
				}
				bounds[col].val = bounds[col].lower;
				matrix[i] = matrix[col];
				matrix[col] = 0;
			}else if(bound.val>bound.upper){
				int i=0;
				for(i=0;i<=MAX_COLUMN;i++){
					if(matrix[i]!=0) continue;
					if((matrix[row*LimitsVarNum + i]<0 && bounds[i].val<bounds[i].upper)||
					   (matrix[row*LimitsVarNum + i]>0 && bounds[i].val>bounds[i].lower)) break;
				}
				if(i>MAX_COLUMN) return false;
				double oldIvalue = bounds[i].val;

				pivotAndUpdate(row,col,bound.upper);
				double t = -matrix[row*LimitsVarNum+i];

				bounds[i].val = (bounds[col].upper-bounds[col].val)/matrix[row*LimitsVarNum+i]+bounds[i].val;
				//对每个基变量中含xi的值的val进行修改
				for(int k=0;k<=MAX_COLUMN;k++){
					if(matrix[k]!=0){
						int row = matrix[k];
						if(matrix[row*LimitsVarNum+i]!=0){
							bounds[k].val +=  matrix[row*LimitsVarNum+i]*(bounds[i].val- oldIvalue);
						}
					}
				}

				for(int k=0;k<=MAX_COLUMN;k++){
					matrix[row*LimitsVarNum+k] = matrix[row*LimitsVarNum+k]/t;
				}

				for(int m=1;m<=MAX_ROW;m++){
					if(m==row) continue;
					double coeff = matrix[m*LimitsVarNum+i];
					for(int n=0; n<=MAX_COLUMN;n++){
						matrix[m*LimitsVarNum+n] += matrix[row*LimitsVarNum+n]*coeff;
					}
				}
				bounds[col].val = bounds[col].upper;
				matrix[i] = matrix[col];
				matrix[col] = 0;
			}
		}
	}
	int LimitsVarNum=8000;
	int LimitsRowNum=2000;
	int MAX_COLUMN=0;
    int MAX_ROW=0;
    int rowNumber = 0;
	double * matrix;

	FILE *matrixOut;
    Solver();
    virtual ~Solver();
    // Problem specification:
    //
    Var     newVar    (lbool upol = l_Undef, bool dvar = true); // Add a new variable with parameters specifying variable mode.
	Var     newLit    (LitArith &lit, lbool upol = l_Undef, bool dvar = true);
	Var		newVar(string x);
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
	vec<oldBound> trail_bound;

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
		//assert lower
			if(la.v<=bounds[la.vn].lower) return lbool(true);
			else if(la.v<=bounds[la.vn].upper) {
				trail_bound.push(mkOldBound(decisionLevel(),la.vn,0,bounds[la.vn].lower));
				bounds[la.vn].lower = la.v;
				if(matrix[la.vn]==0&&bounds[la.vn].val<la.v) update(la.vn,la.v);
				return lbool(true);
			}
		}else if(la.o == OPTR_LESSEQ){
		//assert upper
			if(la.v >= bounds[la.vn].upper) return lbool(true);
			else if(la.v>=bounds[la.vn].lower){
				trail_bound.push(mkOldBound(decisionLevel(),la.vn,1,bounds[la.vn].upper));
				bounds[la.vn].upper = la.v;
				if(matrix[la.vn]==0&&bounds[la.vn].val>la.v) update(la.vn,la.v);
				return lbool(true);
			}
		}
		return lbool(false);
	}

    //Arith helpers
    void displayClauses(){
		if(Switch_DisPlay&&Switch_ALL) return;
		printf("\n\n\n****************   Display Clause  ***************\n");
		printf("%d\n\n",clauses.size());
		for(int i=0;i<clauses.size();i++){
			int k = clauses[i];
			printf("Clause %d:\n",k+1);
			displayOneClause(ca[k]);
		}
    }
    void displayOneClause(Clause &cla){
		if(Switch_DisPlay&&Switch_ALL) return;
		int k = cla.header.size;
		printf(" size:%d\n",k);
		for(int i=0;i<k;i++){
			printf(" %d %s %s %f\t",cla.data[i].lit.x, VarName[cla.data[i].lit.vn].c_str(),cla.data[i].lit.o==13?"<=":">=",cla.data[i].lit.v);
		}
		printf("\n");
    }

    void displayWatchList(){
		if(Switch_DisPlay&&Switch_ALL) return;
		printf("\n\n\n****************   Display Watches  ***************\n");
		for(int i=0;i<VarName.size();i++){
			vec<Watcher> ws = watches.lookup(i);
			printf(" order:%d\n",i);
			Watcher        *j, *end;
			for(j = (Watcher*)ws, end = j + ws.size();  j != end;j++){
				printf("  %d\t Watch\t %d %s %s %f\t",j->cref,j->blocker.x, VarName[j->blocker.vn].c_str(),j->blocker.o==13?"<=":">=",j->blocker.v);
				printf("Self\t %d %s %s %f\n",j->self.x, VarName[j->self.vn].c_str(),j->self.o==13?"<=":">=",j->self.v);
			}
			printf("\n");
		};
    }

    void displayOneWatch(vec<Watcher> & wc){
		if(Switch_DisPlay&&Switch_ALL) return;
		printf("\n\n\n****************   Display One Watch  ***************\n");
		for(int j=0;j<wc.size();j++){
				printf("  %d %s %s %f\t",wc[j].cref,VarName[wc[j].blocker.vn].c_str(),wc[j].blocker.o==13?"<=":">=",wc[j].blocker.v);
			}printf("\n");
    }

    void displayBounds(){
		if(Switch_DisPlay&&Switch_ALL) return;
		printf("\n\n\n****************   Display Bounds ***************\n");
		for(int i=0;i<VarName.size();i++){
			printf("%s\t%ef\t%ef\t%ef\n",VarName[i].c_str(),bounds[i].lower,bounds[i].val,bounds[i].upper);
		}
		printf("\n");
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
	int si = order_heap.size();
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
inline void     Solver::newDecisionLevel()                      {
	trail_lim.push(trail.size());
	//printf("New Decision Level:%d",decisionLevel());
	}



// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline lbool    Solver::solveLimited  (const vec<LitArith>& assumps){
	assumps.copyTo(assumptions);
	return solve_();
}

#endif // SOLVER_H
