#ifndef PARSEUTILS_H_INCLUDED
#define PARSEUTILS_H_INCLUDED

#include "../tl/Vec.h"
#include "../core/SolverTypes.h"
#include <zlib.h>
#include <map>
#include <vector>
#include <string>
//-------------------------------------------------------------------------------------------------
// A simple buffered character stream class:
using namespace std;
class StreamBuffer {
    gzFile         in;
    unsigned char* buf;
    int            pos;
    int            size;

    enum { buffer_size = 64*1024 };

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, buffer_size); } }

public:
    explicit StreamBuffer(gzFile i) : in(i), pos(0), size(0){
        buf = (unsigned char*)xrealloc(NULL, buffer_size);
        assureLookahead();
    }
    ~StreamBuffer() { free(buf); }

    int  operator *  () const { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ ()       { pos++; assureLookahead(); }
    void operator + (const int length)       { pos+=length; assureLookahead(); }

    void operator -= (const int length)       { pos-=length; assureLookahead(); }
    int  position    () const { return pos; }
};

//-------------------------------------------------------------------------------------------------
// End-of-file detection functions for StreamBuffer and char*:


static inline bool isEof(StreamBuffer& in) { return *in == EOF;  }
static inline bool isEof(const char*   in) { return *in == '\0'; }

//-------------------------------------------------------------------------------------------------
// Generic parse functions parametrized over the input-stream type.


template<class B>
static void skipWhitespace(B& in) {
// add * in != 10 to temporarly ignore '\n'
    while ((*in >= 9 && *in <= 13&& *in!=10) || *in == 32)
        ++in; }


template<class B>
static void skipLine(B& in) {
    for (;;){
        if (isEof(in)) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }


template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }


template<class B>
static double parseDouble(B& in) {
    double     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }

// String matching: in case of a match the input iterator will be advanced the corresponding
// number of characters.
template<class B>
static bool match(B& in, const char* str) {
    int i;
    for (i = 0; str[i] != '\0'; i++)
        if (in[i] != str[i])
            return false;

    in += i;

    return true;
}

// String matching: consumes characters eagerly, but does not require random access iterator.
template<class B>
static bool eagerMatch(B& in, const char* str) {
    for (; *str != '\0'; ++str, ++in)
        if (*str != *in)
            return false;
    return true; }

// String matching: consumes characters eagerly, but does not require random access iterator.
template<class B>
static bool lazyMatch(B& in, const char* str) {
	int i=0;
    for (i=0; *str != '\0'; ++str, ++in,i++)
        if (*str != *in)
            {in -= i;return false;}
    return true; }

extern map<string,int > VarMap;
extern vector<string> VarName;
// String matching: consumes characters eagerly, but does not require random access iterator.
template<class B>
static short lazyMatch(B& in) {
	if(*in >= '0' && *in <= '9') return -1;
	else {
		string res="";
		while(*in !=' '&& *in!=')') {
			res += *in;++in;
		}
		map<string,int>::iterator it = VarMap.find(res);
		if(it!=VarMap.end()){
			return it->second;
		}
	}
	return -1;
}

template<class B, class Solver>
static void parseVariable(B& in, Solver &S){
	if(*in >= '0' && *in <= '9') return;
	else {
		string res="";
		while(*in !=' '&& *in!=')') {
			res += *in;++in;
		}

		S.newVar(res);
		}
}
//=================================================================================================
//=================================================================================================
// DIMACS Parser:

template<class B, class Solver>
static void readClause(B& in, Solver& S ,vec<LitArith>& lits){
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        printf("\n%d",parsed_lit);
//        var = abs(parsed_lit)-1;
//
//        while (var >= S.nVars())
//        {
//        S.newVar();}
//
//        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}
template<class B, class Solver>
static void parse_DIMACS_main(B& in, Solver& S, bool strictp = false) {
    vec<LitArith> lits;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
                vars    = parseInt(in);
                clauses = parseInt(in);
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            cnt++;
            readClause(in, S, lits);
       //     S.addClause_(lits);
		}
    }
    if (strictp && cnt != clauses)
        printf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses\n");
}



// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, Solver& S, bool strictp = false) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S, strictp);
}

#endif // PARSEUTILS_H_INCLUDED
