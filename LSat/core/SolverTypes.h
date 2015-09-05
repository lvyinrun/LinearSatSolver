#ifndef SOLVERTYPES_H_INCLUDED
#define SOLVERTYPES_H_INCLUDED

#include "inttypes.h"
#include "../tl/IntMap.h"
#include "../tl/Alloc.h"
#include <float.h>
typedef int Var;
const Var var_Undef = -1;
/*
struct Lit {
    int     x;

    // Use this as a constructor:
    friend Lit mkLit(Var var, bool sign = false);

    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
};

inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }

inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
inline  bool sign      (Lit p)              { return p.x & 1; }
inline  int  var       (Lit p)              { return p.x >> 1; }

const Lit lit_Undef = { -2 };  // }- Useful special constants.
const Lit lit_Error = { -1 };  // }
*/

const char * const ARITH_OPTR_LPAR = "(";
const char * const ARITH_OPTR_RPAR = ")";
const char * const ARITH_OPTR_AND = "and";
const char * const ARITH_OPTR_OR = "or";
const char * const ARITH_OPTR_PLUS = "+";
const char * const ARITH_OPTR_MINUX = "-";
const char * const ARITH_OPTR_MUL = "*";
const char * const ARITH_OPTR_DIV = "/";
const char * const ARITH_OPTR_NEG = "-";
const char * const ARITH_OPTR_EQ = "=";
const char * const ARITH_OPTR_GRT = ">";
const char * const ARITH_OPTR_GRTEQ = ">=";
const char * const ARITH_OPTR_LESS = "<";
const char * const ARITH_OPTR_LESSEQ = "<=";

enum ArithContentType {OPERATOR,VALUE,TERM,ARITH};
enum ArithOperator{
	OPTR_LPAR,OPTR_RPAR,OPTR_AND,OPTR_OR,OPTR_PLUS,OPTR_MINUX,OPTR_MUL,OPTR_DIV,OPTR_NEG,OPTR_EQ,OPTR_GRT,OPTR_GRTEQ,OPTR_LESS,OPTR_LESSEQ
};

struct VarBound{
	double val;
	double lower;
	double upper;
	VarBound(int v, double l, double r):val(v),lower(l),upper(r){};
	VarBound():val(0),lower(0),upper(0){};
};
    struct oldBound{
		int dl;//decision level;
		int x;//variable
		int dir;// 0: lower;1 upper;
		double bound;
		friend oldBound mkOldBound(int dl,int x, int dir, double bound);
    };

inline oldBound mkOldBound(int dl,int x, int dir, double bound){
	oldBound ob;
	ob.dl = dl;
	ob.x = x;
	ob.dir = dir;
	ob.bound = bound;
	return ob;
}
//Arith
struct LitArith{
	int x;//lit order

	int vn; //varname
	ArithOperator o; //operator
	double v;//value

	friend LitArith mkLit(Var lit,int varname, ArithOperator optr,double value, bool sign = false);
	bool operator == (LitArith p) const {return (p.x == x);}
	bool operator != (LitArith p) const {return (p.x != x);}
    bool operator <  (LitArith p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
};

inline LitArith mkLit(Var lit,int varname,ArithOperator optr,double value, bool sign){
	LitArith q;
	q.x = lit;

	q.v = value;
	q.o = optr;
	q.vn = varname;

	return q;
}
//need to be changed
inline  LitArith  operator ~(LitArith p)              { LitArith q; q.x = p.x ^ 1; q.o = p.o; q.v = p.v; q.vn = p.vn; return q; }
inline  LitArith  operator ^(LitArith p, bool b)      { LitArith q; q.x = p.x ^ (unsigned int)b; q.o = p.o; q.v = p.v; q.vn = p.vn; return q; }


//什么情况下会返回-1？？？？？
inline  bool sign      (LitArith p)              { return p.x & 1; }
inline  int  var       (LitArith p)              { return p.x; }

const LitArith lit_Undef = { -2 };  // }- Useful special constants.
const LitArith lit_Error = { -1 };  // }

struct ArithTerm{
	double coefficient;
	int variable;
	friend ArithTerm mkArithTerm(double c,int v);
};

inline ArithTerm mkArithTerm(double c,int v){
	ArithTerm  term;
	term.coefficient = c;
	term.variable = v;
	return term;
}

struct ArithItem{
	ArithContentType type;
	union {
		ArithOperator optr;
		double dvalue;
		ArithTerm term;
		LitArith la;
	} item_value;

	friend ArithItem mkArithItemOptr(ArithContentType t,ArithOperator optr);
	friend ArithItem mkArithItemValue(ArithContentType t,double val);
	friend ArithItem mkArithItemTerm(ArithTerm term);
	friend ArithItem mkArithItemTerm(int var);
	friend ArithItem mkArithItemLitArith(LitArith arith);
};
inline ArithItem mkArithItemOptr(ArithContentType t,ArithOperator optr){
	ArithItem ai;ai.type = t;ai.item_value.optr = optr;	return ai;}

inline ArithItem mkArithItemValue(ArithContentType t,double val){
	ArithItem ai;ai.type = t;ai.item_value.dvalue = val;return ai;
}
inline ArithItem mkArithItemTerm(ArithTerm term){
	ArithItem ai;ai.type = TERM;ai.item_value.term = term;return ai;
}

inline ArithItem mkArithItemLitArith(LitArith arith){
	ArithItem ai;ai.type = ARITH;ai.item_value.la = arith;return ai;
}

inline ArithItem mkArithItemTerm(int var){
	ArithItem ai;ai.type = TERM;ai.item_value.term.coefficient=1;ai.item_value.term.variable = var;return ai;
}

class lbool {
    uint8_t value;

public:
    explicit lbool(uint8_t v) : value(v) { }

    lbool()       : value(0) { }
    explicit lbool(bool x) : value(!x) { }

    bool  operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
    bool  operator != (lbool b) const { return !(*this == b); }
    lbool operator ^  (bool  b) const { return lbool((uint8_t)(value^(uint8_t)b)); }

    lbool operator && (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v); }

    lbool operator || (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.value; }
inline lbool toLbool(int   v) { return lbool((uint8_t)v);  }


struct MkIndexLit {
	vec<LitArith>::Size operator()(int x) const {
	return vec<LitArith>::Size(x); }
};

struct MkIndexLitArith {
	vec<LitArith>::Size operator () (LitArith lit) const{
		return vec<LitArith>::Size(lit.x);}
};

template<class T> class VMap : public IntMap<Var, T>{};
template<class T> class LMap : public IntMap<LitArith, T, MkIndexLit>{};
class LSet : public IntSet<LitArith, MkIndexLitArith>{};
//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

template<class K, class Vec, class Deleted, class MkIndex = MkIndexDefault<K> >
class OccLists
{
public:
    IntMap<K, Vec,  MkIndex> occs;
    IntMap<K, char, MkIndex> dirty;
    vec<K>                   dirties;
    Deleted                  deleted;

 public:
    OccLists(const Deleted& d, MkIndex _index = MkIndex()) :
	occs(_index),
	dirty(_index),
	deleted(d){}

    void  init      (const K& idx){
     occs.reserve(idx);
     occs[idx].clear();
     dirty.reserve(idx, 0);
     }
    Vec&  operator[](const K& idx){
		return occs[idx];
	}
    Vec&  lookup    (const K& idx){
     if (dirty[idx])
		clean(idx);
     return occs[idx]; }

    void  cleanAll  ();
    void  clean     (const K& idx);
    void  smudge    (const K& idx){
        if (dirty[idx] == 0){
            dirty[idx] = 1;
            dirties.push(idx);
        }
    }

    void  clear(bool free = true){
        occs   .clear(free);
        dirty  .clear(free);
        dirties.clear(free);
    }
};

template<class K, class Vec, class Deleted, class MkIndex>
void OccLists<K,Vec,Deleted,MkIndex>::cleanAll()
{
    for (int i = 0; i < dirties.size(); i++)
        // Dirties may contain duplicates so check here if a variable is already cleaned:
        if (dirty[dirties[i]])
            clean(dirties[i]);
    dirties.clear();
}


template<class K, class Vec, class Deleted, class MkIndex>
void OccLists<K,Vec,Deleted,MkIndex>::clean(const K& idx)
{
    Vec& vec = occs[idx];
    int  i, j;
    for (i = j = 0; i < vec.size(); i++)
        if (!deleted(vec[i]))
            vec[j++] = vec[i];
    vec.shrink(i - j);
    dirty[idx] = 0;
}

#if defined(MINISAT_CONSTANTS_AS_MACROS)
  #define l_True  (lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
  #define l_False (lbool((uint8_t)1))
  #define l_Undef (lbool((uint8_t)2))
#else
  const lbool l_True ((uint8_t)0);
  const lbool l_False((uint8_t)1);
  const lbool l_Undef((uint8_t)2);
#endif
//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref CRef;

class Clause {
public://this should be removed
    struct {
        unsigned mark      : 2;
        unsigned learnt    : 1;
        unsigned has_extra : 1;
        unsigned reloced   : 1;
        unsigned size      : 27; }                        header;
    union { LitArith lit; float act; uint32_t abs; CRef rel; } data[0];

    friend class ClauseAllocator;
    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(const vec<LitArith>& ps, bool use_extra, bool learnt) {
        header.mark      = 0;
        header.learnt    = learnt;
        header.has_extra = use_extra;
        header.reloced   = 0;
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++)
            data[i].lit = ps[i];

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = 0;
            else
                calcAbstraction();
    }
    }

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(const Clause& from, bool use_extra){
        header           = from.header;
        header.has_extra = use_extra;   // NOTE: the copied clause may lose the extra field.

        for (int i = 0; i < from.size(); i++)
            data[i].lit = from[i];

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = from.data[header.size].act;
            else
                data[header.size].abs = from.data[header.size].abs;
		}
    }

public:
	void calcAbstraction() {
        assert(header.has_extra);
        uint32_t abstraction = 0;
        for (int i = 0; i < size(); i++)
            abstraction |= 1 << (var(data[i].lit) & 31);
        data[header.size].abs = abstraction;  }

    int          size        ()      const   { return header.size; }
    void         shrink      (int i)         { assert(i <= size()); if (header.has_extra) data[header.size-i] = data[header.size]; header.size -= i; }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return header.learnt; }
    uint32_t     mark        ()      const   { return header.mark; }
    void         mark        (uint32_t m)    { header.mark = m; }
    bool         has_extra   ()      const   { return header.has_extra; }
    bool         reloced     ()      const   { return header.reloced; }
    CRef         relocation  ()      const   { return data[0].rel; }
    void         relocate    (CRef c)        { header.reloced = 1; data[0].rel = c; }
	// NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    LitArith&         operator [] (int i)         { return data[i].lit; }
	LitArith          operator [] (int i) const   { return data[i].lit; }
    operator const LitArith* (void) const         { return (LitArith*)data; }

        float&       activity    ()              { assert(header.has_extra); return data[header.size].act; }
};

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:

const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
const CRef CRef_Check_Error = RegionAllocator<uint32_t>::Ref_Check_Error;

class ClauseAllocator
{
    RegionAllocator<uint32_t> ra;//4 bytes
	bool extra_clause_field;
	static uint32_t clauseWord32Size(int size, bool has_extra){
	//printf("size:   Clause%d  LitArith:%d size:%d has_extra:%d,uint32:%d\n",sizeof(Clause),sizeof(LitArith),size , (int)has_extra, sizeof(uint32_t));
        return (sizeof(Clause) + (sizeof(LitArith) * (size + (int)has_extra)))/sizeof(uint32_t); }
public:
	enum { Unit_Size = RegionAllocator<uint32_t>::Unit_Size };
	ClauseAllocator(uint32_t start_cap) : ra(start_cap), extra_clause_field(false){}
    ClauseAllocator() : extra_clause_field(false){}

	void moveTo(ClauseAllocator& to){
        to.extra_clause_field = extra_clause_field;
        ra.moveTo(to.ra); }
	// Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](CRef r)         { return (Clause&)ra[r]; }
    const Clause& operator[](CRef r) const   { return (Clause&)ra[r]; }
    Clause*       lea       (CRef r)         { return (Clause*)ra.lea(r); }
    const Clause* lea       (CRef r) const   {
		return (Clause*)ra.lea(r);
	}
    CRef          ael       (const Clause* t){ return ra.ael((uint32_t*)t); }

	CRef alloc(const vec<LitArith>& ps, bool learnt = false)
    {
      //  assert(sizeof(LitArith)      == sizeof(uint32_t));
      //  assert(sizeof(float)    == sizeof(uint32_t));
        bool use_extra = learnt | extra_clause_field;
        CRef cid       = ra.alloc(clauseWord32Size(ps.size(), use_extra));
        new (lea(cid)) Clause(ps, use_extra, learnt);

        return cid;
    }

	void free(CRef cid)
    {
        Clause& c = operator[](cid);
        ra.free(clauseWord32Size(c.size(), c.has_extra()));
    }


    CRef alloc(const Clause& from)
    {
        bool use_extra = from.learnt() | extra_clause_field;
        CRef cid       = ra.alloc(clauseWord32Size(from.size(), use_extra));
        new (lea(cid)) Clause(from, use_extra);
        return cid; }
	void reloc(CRef& cr, ClauseAllocator& to)
    {
        Clause& c = operator[](cr);

        if (c.reloced()) { cr = c.relocation(); return; }

        cr = to.alloc(c);
        c.relocate(cr);
    }

	uint32_t size      () const      { return ra.size(); }
    uint32_t wasted    () const      { return ra.wasted(); }
};
#endif // SOLVERTYPES_H_INCLUDED
