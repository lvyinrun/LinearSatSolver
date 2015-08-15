#ifndef PARSESMT_H_INCLUDED
#define PARSESMT_H_INCLUDED

#include <zlib.h>
#include <stack>
#include <map>
#include <vector>
#include "../tl/Vec.h"
#include "../core/SolverTypes.h"

#include <../parse/ParseUtils.h>
using namespace std;

map<string,int > VarMap;
vector<string> VarName;
// Inserts problem into solver.
//
template<class Solver>
static void parse_SMT(gzFile input_stream, Solver& S, bool strictp = false) {
    StreamBuffer in(input_stream);
    parse_SMT_main(in, S, strictp);
}
bool debug_flag=false;
const char * ARITH_OPTR_LPAR = "(";
const char * ARITH_OPTR_RPAR = ")";
const char * ARITH_OPTR_AND = "and";
const char * ARITH_OPTR_OR = "or";
const char * ARITH_OPTR_PLUS = "+";
const char * ARITH_OPTR_MINUX = "-";
const char * ARITH_OPTR_MUL = "*";
const char * ARITH_OPTR_DIV = "/";
const char * ARITH_OPTR_NEG = "-";
const char * ARITH_OPTR_EQ = "=";
const char * ARITH_OPTR_GRT = ">";
const char * ARITH_OPTR_GRTEQ = ">=";
const char * ARITH_OPTR_LESS = "<";
const char * ARITH_OPTR_LESSEQ = "<=";

enum ArithContentType {OPERATOR,VAR,VALUE,TERM};
enum ArithOperator{
	OPTR_LPAR,OPTR_RPAR,OPTR_AND,OPTR_OR,OPTR_PLUS,OPTR_MINUX,OPTR_MUL,OPTR_DIV,OPTR_NEG,OPTR_EQ,OPTR_GRT,OPTR_GRTEQ,OPTR_LESS,OPTR_LESSEQ
};

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
		int varOrder;
		ArithTerm term;
	} item_value;

	friend ArithItem mkArithItemOptr(ArithContentType t,ArithOperator optr);
	friend ArithItem mkArithItemVar(ArithContentType t,int var);
	friend ArithItem mkArithItemValue(ArithContentType t,double val);
	friend ArithItem mkArithItemTerm(ArithContentType t,ArithTerm term);
};

void print_item(ArithItem item,int stack_size){
	if(debug_flag!=true) return;
	if(item.type==OPERATOR) printf("operator\t %d\n",stack_size);
	else if(item.type==VALUE) printf("%f\t %d\n",item.item_value.dvalue,stack_size);
	else if(item.type==VAR) printf("%s\t %d\n",VarName[item.item_value.varOrder].c_str(),stack_size);
	else if(item.type==TERM) printf("cof:%f\t var:%s\t %d\n",item.item_value.term.coefficient,VarName[item.item_value.term.variable].c_str(),stack_size);
}

void print_item_format(ArithItem item){
	if(item.type==OPERATOR) {
		if(item.item_value.optr==OPTR_LPAR) printf("(\t");
		else if(item.item_value.optr==OPTR_RPAR) printf(")\t");
	}
	else if(item.type==VALUE) printf("%f\t",item.item_value.dvalue);
	else if(item.type==VAR) printf("%s\t",VarName[item.item_value.varOrder].c_str());
	else if(item.type==TERM) printf("%f%s\t",item.item_value.term.coefficient,VarName[item.item_value.term.variable].c_str());
}
inline ArithItem mkArithItemOptr(ArithContentType t,ArithOperator optr){
	ArithItem ai;ai.type = t;ai.item_value.optr = optr;	return ai;}

inline ArithItem mkArithItemVar(ArithContentType t,int var){
	ArithItem ai;ai.type = t;ai.item_value.varOrder = var;return ai;
}
inline ArithItem mkArithItemValue(ArithContentType t,double val){
	ArithItem ai;ai.type = t;ai.item_value.dvalue = val;return ai;
}
inline ArithItem mkArithItemTerm(ArithTerm term){
	ArithItem ai;ai.type = TERM;ai.item_value.term = term;return ai;
}
struct ArithLine{
	ArithOperator optr;
	vec<ArithTerm> left;
	vec<ArithTerm> right;
};
template<class B, class Solver>
static void parse_SMT_main(B& in, Solver& S, bool strictp = false) {
    vec<LitArith> lits;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;
    for (;;){
        skipWhitespace(in);

        if (*in == EOF) break;
        else if (*in == '('){
			++in;
            if (eagerMatch(in, "set-")){
				skipLine(in);
				//printf("\n set");
                //vars    = parseInt(in);
                //clauses = parseInt(in);
                // SATRACE'06 hack
               // if (clauses > 4000000)
                //     S.eliminate(true);
            }else if(eagerMatch(in, "declare-fun")){
				skipWhitespace(in);
				if(*in=='x') ++in;

			//	printf("\n declare %d",parseInt(in));
				skipLine(in);

            }else if(eagerMatch(in, "assert")){
            //destruct
				int var_order;
				stack<ArithItem> s;
				while(true){
					skipWhitespace(in);
					if(*in=='\n') {
						skipLine(in);break;
					}
					else if(lazyMatch(in,ARITH_OPTR_RPAR)) {
					//弹栈开始运算
						stack<ArithItem> localTemp;
						int numOfRPAR=0;
						while(s.size()>0){
							ArithItem ai = s.top();
							s.pop();
							if(ai.type==OPERATOR && ai.item_value.optr==OPTR_RPAR){
								numOfRPAR++;
							}
							if(ai.type==OPERATOR &&ai.item_value.optr==OPTR_LPAR){
								if(numOfRPAR>0) numOfRPAR--;
								else break;
							}
							localTemp.push(ai);
						}

						ArithItem ai = localTemp.top();
						localTemp.pop();
						//+ - * / 四则运算
						//相除的情况一定是几个数进行除法运算，线性不等式
						if(ai.item_value.optr == OPTR_DIV){

							stack<ArithItem> stack_minus;
							ArithItem ditem = localTemp.top();
							localTemp.pop();
							vector<ArithItem> firstPart;
							//read the first element
							if(ditem.type==OPERATOR&&ditem.item_value.optr==OPTR_LPAR){
								stack<ArithItem> parStack;
								parStack.push(ditem);
								while(parStack.size()>0){
									ditem = localTemp.top();
									localTemp.pop();
									if(ditem.type!=OPERATOR){
										firstPart.push_back(ditem);
									}else{
										if(ditem.item_value.optr==OPTR_LPAR) parStack.push(ditem);
										else if(ditem.item_value.optr==OPTR_RPAR) parStack.pop();
									}
								}
							}else{
								firstPart.push_back(ditem);
							}

							double divided = 1;
							while(localTemp.size()>0){
								ditem = localTemp.top();
								localTemp.pop();
								if(ditem.type = VALUE){
									divided *= ditem.item_value.dvalue;
								}
							}
						s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
						print_item(s.top(),s.size());
							for(int i=0;i<firstPart.size();i++){
								if(firstPart[i].type==VALUE){
									firstPart[i].item_value.dvalue /= divided;
									s.push(firstPart[i]);
									print_item(s.top(),s.size());
								}
								else if(firstPart[i].type==VAR){
									s.push(mkArithItemTerm(mkArithTerm(-1/divided,firstPart[i].item_value.varOrder)));
									print_item(s.top(),s.size());
								}else if(firstPart[i].type==TERM){
									firstPart[i].item_value.term.coefficient /= divided;
									s.push(firstPart[i]);
									print_item(s.top(),s.size());
								}
							}
							s.push(mkArithItemOptr(OPERATOR,OPTR_RPAR));
							print_item(s.top(),s.size());

						}

						//MULTIPLY
						else if(ai.item_value.optr == OPTR_MUL){
							double coef=1;
							bool polyFound=false;
							vector<ArithItem> poly;

							while(localTemp.size()>0){
								ArithItem curItem = localTemp.top();
								localTemp.pop();

								stack<ArithItem> mul_cla;
								vector<ArithItem> mul_vec;
								mul_vec.clear();

								if(curItem.type==OPERATOR) {
									mul_cla.push(curItem);
								}else if(curItem.type==VALUE){
									coef *= curItem.item_value.dvalue;
									continue;
								}else{
									polyFound = true;
									poly.push_back(curItem);
									continue;
								};
								while(mul_cla.size()>0){
									curItem = localTemp.top();
									localTemp.pop();
									if(curItem.type!=OPERATOR){
										mul_vec.push_back(curItem);
									}
									else if(curItem.type==OPERATOR&&curItem.item_value.optr==OPTR_RPAR) mul_cla.pop();
									else if(curItem.type==OPERATOR&&curItem.item_value.optr==OPTR_LPAR) mul_cla.push(curItem);
								}
								if(polyFound||(!polyFound&&mul_vec.size()==1&&mul_vec[0].type==VALUE)){
									coef *= mul_vec[0].item_value.dvalue;
								}else{
									polyFound = true;
									for(int k=0;k<mul_vec.size();k++){
										poly.push_back(mul_vec[k]);
									}
								}
							}
							if(polyFound){
								if(poly.size()==1) {
									s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
									print_item(s.top(),s.size());
								}
								for(int i=0;i<poly.size();i++){
									if(poly[i].type==TERM){
										poly[i].item_value.term.coefficient*=coef;
										s.push(poly[i]);
										print_item(s.top(),s.size());
									}else if(poly[i].type==VAR){
										s.push(mkArithItemTerm(mkArithTerm(coef,poly[i].item_value.varOrder)));
										print_item(s.top(),s.size());
									}
								}
								if(poly.size()==1) {
									s.push(mkArithItemOptr(OPERATOR,OPTR_RPAR));
									print_item(s.top(),s.size());
								}

							}else{
								s.push(mkArithItemValue(VALUE,coef));
								print_item(s.top(),s.size());
							}
						}
						//PLUS
						else if(ai.item_value.optr == OPTR_PLUS){
							s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
									print_item(s.top(),s.size());
							ArithItem plus_value=mkArithItemValue(VALUE,0);
							while(localTemp.size()>0){
								ArithItem it = localTemp.top();
								localTemp.pop();
								if(it.type==OPERATOR) continue;
								else if(it.type==VALUE){
									plus_value.item_value.dvalue+=it.item_value.dvalue;
								}else{
									s.push(it);
									print_item(s.top(),s.size());
								}
							}
							if(plus_value.item_value.dvalue!=0) {
								s.push(plus_value);
								print_item(s.top(),s.size());
							}
							s.push(mkArithItemOptr(OPERATOR,OPTR_RPAR));
							print_item(s.top(),s.size());
						}
						//"-"
						else if(ai.item_value.optr == OPTR_MINUX){
							stack<ArithItem> stack_minus;
							ArithItem mitem = localTemp.top();
							localTemp.pop();
							vector<ArithItem> firstPart;
							//read the first element
							if(mitem.type==OPERATOR&&mitem.item_value.optr==OPTR_LPAR){
								stack<ArithItem> parStack;
								parStack.push(mitem);
								while(parStack.size()>0){
									mitem = localTemp.top();
									localTemp.pop();
									if(mitem.type!=OPERATOR){
										firstPart.push_back(mitem);
									}else{
										if(mitem.item_value.optr==OPTR_LPAR) parStack.push(mitem);
										else if(mitem.item_value.optr==OPTR_RPAR) parStack.pop();
									}
								}
							}else{
								firstPart.push_back(mitem);
							}

							while(localTemp.size()>0){
								mitem = localTemp.top();
								localTemp.pop();
								if(mitem.type!=OPERATOR) stack_minus.push(mitem);
							}


							//start calc
							s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
									print_item(s.top(),s.size());
							if(stack_minus.size()==0){
							//this mean negative sign
								double res=0;
								for(int i=0;i<firstPart.size();i++){
									if(firstPart[i].type==VALUE) res-=firstPart[i].item_value.dvalue;
									else if(firstPart[i].type==VAR){
										s.push(mkArithItemTerm(mkArithTerm(-1,firstPart[i].item_value.varOrder)));
										print_item(s.top(),s.size());
									}else if(firstPart[i].type==TERM){
										firstPart[i].item_value.term.coefficient = -firstPart[i].item_value.term.coefficient;
										s.push(firstPart[i]);
										print_item(s.top(),s.size());
									}
								}
								if(res!=0){
									s.push(mkArithItemValue(VALUE,res));
									print_item(s.top(),s.size());
								}
							}else{
							//this means minus
								double res=0;
								//被减数入栈
								for(int i=0;i<firstPart.size();i++){
									if(firstPart[i].type==VALUE) res+=firstPart[i].item_value.dvalue;
									else {
										s.push(firstPart[i]);
										print_item(s.top(),s.size());
									}
								}

								while(stack_minus.size()>0){
									mitem = stack_minus.top();
									stack_minus.pop();
									if(mitem.type==VALUE) {
										res -= mitem.item_value.dvalue;
									}
									else if(mitem.type==VAR) {
										s.push(mkArithItemTerm(mkArithTerm(-1,mitem.item_value.varOrder)));
										print_item(s.top(),s.size());
									}
									else if(mitem.type==TERM) {
										mitem.item_value.term.coefficient = - mitem.item_value.term.coefficient;
										s.push(mitem);
										print_item(s.top(),s.size());
									}
								}
								if(res!=0){
									s.push(mkArithItemValue(VALUE,res));
									print_item(s.top(),s.size());
								}

							}

							s.push(mkArithItemOptr(OPERATOR,OPTR_RPAR));
							print_item(s.top(),s.size());
						}
						else if(ai.item_value.optr == OPTR_EQ|| ai.item_value.optr == OPTR_GRT|| ai.item_value.optr == OPTR_GRTEQ || ai.item_value.optr == OPTR_LESS || ai.item_value.optr == OPTR_LESSEQ){

							if(localTemp.size()>0){
								ArithItem cur = localTemp.top();
								localTemp.pop();
								stack<ArithItem> cur_stack;
								if(cur.type == OPTR_LPAR){
									cur_stack.push(cur);
								}else{
									print_item_format(cur);
								}
								while(cur_stack.size()>0){
									cur = localTemp.top();
									localTemp.pop();
									if(cur.type==OPERATOR&&cur.item_value.optr == OPTR_LPAR) cur_stack.push(cur);
									else if(cur.type==OPERATOR&& cur.item_value.optr == OPTR_RPAR) cur_stack.pop();
									else{
										print_item_format(cur);
									}
								}
							}

							if(ai.item_value.optr == OPTR_EQ){printf(" = ");
							}else if(ai.item_value.optr == OPTR_GRT){printf(" > ");
							}else if(ai.item_value.optr == OPTR_GRTEQ){printf(" >= ");
							}else if(ai.item_value.optr == OPTR_LESS){printf(" < ");
							}else if(ai.item_value.optr == OPTR_LESSEQ){printf(" <= ");}

							if(localTemp.size()>0){
								ArithItem cur = localTemp.top();
								localTemp.pop();
								stack<ArithItem> cur_stack;
								if(cur.type == OPTR_LPAR){
									cur_stack.push(cur);
								}else{
									print_item_format(cur);
								}
								while(cur_stack.size()>0){
									cur = localTemp.top();
									localTemp.pop();
									if(cur.type==OPERATOR&&cur.item_value.optr == OPTR_LPAR) cur_stack.push(cur);
									else if(cur.type==OPERATOR&& cur.item_value.optr == OPTR_RPAR) cur_stack.pop();
									else{
										print_item_format(cur);
									}
								}
							}
							printf("\n");
						}
						else if(ai.item_value.optr == OPTR_OR){
							printf("\n");

						}else if(ai.item_value.optr == OPTR_AND){
							printf("\n\n AND \n");

						}

					}else if(lazyMatch(in,ARITH_OPTR_LPAR)) {
						//s.push()
						s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_LPAR,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_AND)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_AND));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_AND,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_OR)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_OR));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_OR,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_PLUS)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_PLUS));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_PLUS,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_MINUX)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_MINUX));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_MINUX,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_MUL)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_MUL));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_MUL,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_DIV)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_DIV));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_DIV,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_NEG)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_NEG));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_NEG,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_EQ)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_EQ));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_EQ,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_GRT)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_GRT));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_GRT,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_GRTEQ)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_GRTEQ));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_GRTEQ,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_LESS)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_LESS));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_LESS,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_LESSEQ)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_LESSEQ));
						if(debug_flag==true) printf("%s %d\n",ARITH_OPTR_LESSEQ,s.size());
					}
					else if(( var_order = lazyMatch(in) ) > -1) {
						s.push(mkArithItemVar(VAR,var_order));
						if(debug_flag==true) printf("%s %d var_order:%d\n",VarName[var_order].c_str(),s.size(),var_order);
					}
					//printf("%s\n",ARITH_OPTR_NEG);
					else {//pare double and push stack
						s.push(mkArithItemValue(VALUE,parseDouble(in)));
						if(debug_flag==true) printf("%f %d\n",s.top().item_value.dvalue,s.size());
					}
				}

			//	printf("\n assert");
            }else if(eagerMatch(in, "check-sat")){
				skipLine(in);
				printf("\n check-sat");
            }else if(eagerMatch(in, "exit")){
				skipLine(in);
				printf("\n exit");
            }
            else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        }
//        else if (*in == 'c' || *in == 'p')
//            skipLine(in);
//        else{
//            cnt++;
//            readClause(in, S, lits);
//       //     S.addClause_(lits);
//		}
    }
    if (strictp && cnt != clauses)
        printf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses\n");
}
#endif // PARSESMT_H_INCLUDED
