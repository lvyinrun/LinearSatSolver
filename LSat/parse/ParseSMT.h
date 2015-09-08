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
bool smt_debug_flag=false;
bool orInStack = false;
// Inserts problem into solver.
//
template<class Solver>
static void parse_SMT(gzFile input_stream, Solver& S, bool strictp = false) {
    StreamBuffer in(input_stream);
    parse_SMT_main(in, S, strictp);
}
void print_item(ArithItem item,int stack_size){
	if(smt_debug_flag !=true) return;
	if(item.type==OPERATOR) printf("operator\t %d\n",stack_size);
	else if(item.type==VALUE) printf("%f\t %d\n",item.item_value.dvalue,stack_size);
	else if(item.type==TERM) printf("%f %s\t %d\n",item.item_value.term.coefficient,VarName[item.item_value.term.variable].c_str(),stack_size);
	else if(item.type==ARITH) printf("%s %s %f %d\n",VarName[item.item_value.la.vn].c_str(),item.item_value.la.o==OPTR_LESSEQ?"<=":">=", item.item_value.la.v,stack_size);
}

void print_item_format(ArithItem item){
	if(item.type==OPERATOR) {
		if(item.item_value.optr==OPTR_LPAR) printf("(\t");
		else if(item.item_value.optr==OPTR_RPAR) printf(")\t");
	}
	else if(item.type==VALUE) printf("%f\t",item.item_value.dvalue);
//	else if(item.type==VAR) printf("%s\t",VarName[item.item_value.varOrder].c_str());
	else if(item.type==TERM) printf("%f%s\t",item.item_value.term.coefficient,VarName[item.item_value.term.variable].c_str());
}


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
				//if(*in=='x') ++in;
				parseVariable(in,S);

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
						if(s.size()==0) continue;
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
//								}
//								else if(firstPart[i].type==VAR){
//									s.push(mkArithItemTerm(mkArithTerm(-1/divided,firstPart[i].item_value.varOrder)));
//									print_item(s.top(),s.size());
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
//									}else if(poly[i].type==VAR){
//										s.push(mkArithItemTerm(mkArithTerm(coef,poly[i].item_value.varOrder)));
//										print_item(s.top(),s.size());
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
//									else if(firstPart[i].type==VAR){
//										s.push(mkArithItemTerm(mkArithTerm(-1,firstPart[i].item_value.varOrder)));
//										print_item(s.top(),s.size());
	//								}
									else if(firstPart[i].type==TERM){
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
//									else if(mitem.type==VAR) {
//										s.push(mkArithItemTerm(mkArithTerm(-1,mitem.item_value.varOrder)));
//										print_item(s.top(),s.size());
//									}
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
							//readClause;此处相当于read clause
							LitArith la;
							stack<ArithItem> items;
							if(localTemp.size()>0){
								ArithItem cur = localTemp.top();
								localTemp.pop();
								stack<ArithItem> cur_stack;
								if(cur.type == OPTR_LPAR){
									cur_stack.push(cur);
								}else if(cur.type == TERM) {
										la.vn = cur.item_value.term.variable;
									}

								while(cur_stack.size()>0){
									cur = localTemp.top();
									localTemp.pop();
									if(cur.type==OPERATOR&&cur.item_value.optr == OPTR_LPAR) cur_stack.push(cur);
									else if(cur.type==OPERATOR&& cur.item_value.optr == OPTR_RPAR) cur_stack.pop();
									else{
										//print_item_format(cur);
										if(cur.type == TERM) items.push(cur);
										//la.x = cur.item_value.term.variable;
									}
								}
							}
							if(items.size()>1){
							//需要进行代换，引入新的变量
								//	printf("wocao,yao daihuan\n");
									string res= "x";
									char sss[10];
									sprintf(sss,"%d",VarMap.size()+1);
									res.append(sss);
									S.newVar(res);

									la.vn = VarMap.size()-1;

									S.matrixAddRow(items,la.vn);
							}else if(items.size()==1){
									la.vn = items.top().item_value.term.variable;
							}

							if(ai.item_value.optr == OPTR_EQ){
								//printf(" = ");
								la.o = OPTR_EQ;
							}else if(ai.item_value.optr == OPTR_GRT){
							//printf(" > ");
							la.o=OPTR_GRT;
							}else if(ai.item_value.optr == OPTR_GRTEQ){
							//printf(" >= ");
							la.o=OPTR_GRTEQ;
							}else if(ai.item_value.optr == OPTR_LESS){
							//printf(" < ");
							la.o=OPTR_LESS;
							}else if(ai.item_value.optr == OPTR_LESSEQ){
							//printf(" <= ");
							la.o = OPTR_LESSEQ;
							}else{ printf("what happends");}

							if(localTemp.size()>0){
								ArithItem cur = localTemp.top();
								localTemp.pop();
								stack<ArithItem> cur_stack;
								if(cur.type == OPTR_LPAR){
									cur_stack.push(cur);
								}else{
									//print_item_format(cur);
									if(cur.type == VALUE) la.v = cur.item_value.dvalue;
								}
								while(cur_stack.size()>0){
									cur = localTemp.top();
									localTemp.pop();
									if(cur.type==OPERATOR&&cur.item_value.optr == OPTR_LPAR) cur_stack.push(cur);
									else if(cur.type==OPERATOR&& cur.item_value.optr == OPTR_RPAR) cur_stack.pop();
									else{
										//print_item_format(cur);
										if(cur.type == VALUE) la.v = cur.item_value.dvalue;
									}
								}
							}
							/* very importatn
								and the new clause to Solver state
								*/
							if(orInStack==false){
							//	printf("\n************************FALSE  %d*****************************\n",localTemp.size());
								LitArith lit;
								localTemp.push(mkArithItemLitArith(la));
								while(localTemp.size()>0){
									ArithItem it = localTemp.top();
									localTemp.pop();

									S.newLit(it.item_value.la);
									lits.push(it.item_value.la);
								}

								//printf("vec size %d\n",lits.size());
								S.addClauseArith_(lits);
								lits.clear();
								continue;
							}else{
								s.push(mkArithItemLitArith(la));
								print_item(s.top(),s.size());
							}
						}
						else if(ai.item_value.optr == OPTR_OR){
							orInStack = false;
							LitArith lit;
							while(localTemp.size()>0){
								ArithItem it = localTemp.top();
								localTemp.pop();

								S.newLit(it.item_value.la);
								lits.push(it.item_value.la);
							}

							//printf("vec size %d\n",lits.size());
							S.addClauseArith_(lits);
							lits.clear();
						}else if(ai.item_value.optr == OPTR_AND){
							//printf("\n\n AND \n");

						}

					}else if(lazyMatch(in,ARITH_OPTR_LPAR)) {
						//s.push()
						s.push(mkArithItemOptr(OPERATOR,OPTR_LPAR));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_LPAR,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_AND)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_AND));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_AND,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_OR)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_OR));
						orInStack = true;
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_OR,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_PLUS)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_PLUS));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_PLUS,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_MINUX)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_MINUX));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_MINUX,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_MUL)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_MUL));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_MUL,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_DIV)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_DIV));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_DIV,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_NEG)) {
						s.push(mkArithItemOptr(OPERATOR,OPTR_NEG));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_NEG,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_EQ)) {
					// =
						s.push(mkArithItemOptr(OPERATOR,OPTR_EQ));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_EQ,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_GRTEQ)) {
					// >=
						s.push(mkArithItemOptr(OPERATOR,OPTR_GRTEQ));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_GRTEQ,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_GRT)) {
					// >
						s.push(mkArithItemOptr(OPERATOR,OPTR_GRT));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_GRT,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_LESSEQ)) {
					// <=
						s.push(mkArithItemOptr(OPERATOR,OPTR_LESSEQ));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_LESSEQ,s.size());
					}else if(lazyMatch(in,ARITH_OPTR_LESS)) {
					// <
						s.push(mkArithItemOptr(OPERATOR,OPTR_LESS));
						if(smt_debug_flag==true) printf("%s %d\n",ARITH_OPTR_LESS,s.size());
					}
					else if(( var_order = lazyMatch(in) ) > -1) {
						s.push(mkArithItemTerm(var_order));
						if(smt_debug_flag==true) printf("%s %d var_order:%d\n",VarName[var_order].c_str(),s.size(),var_order);
					}
					//printf("%s\n",ARITH_OPTR_NEG);
					else {//pare double and push stack
						s.push(mkArithItemValue(VALUE,parseDouble(in)));
						if(smt_debug_flag==true) printf("%f %d\n",s.top().item_value.dvalue,s.size());
					}
				}

			//	printf("\n assert");
            }else if(eagerMatch(in, "check-sat")){
				skipLine(in);
				//printf("\n check-sat");
            }else if(eagerMatch(in, "exit")){
				skipLine(in);
				//printf("\n exit");
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
