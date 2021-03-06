#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <zlib.h>

#include "parse/ParseSMT.h"
#include "core/Solver.h"

using namespace std;

int main(int argc, char **argv)
{
    if(argc==1)
        printf("Reading from standard input...\n");
    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

	Solver S;
	S.initMatrix();
    parse_SMT(in, S, (bool)0);

    gzclose(in);
    FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;


	S.displayBounds();
	S.displayClauses();
	S.displayWatchList();
	S.checkFlag = true;
	S.InitialSlashVariable();
	S.buildPickHashMap();
	if(!S.simplify())     cout << "\n\Failed" << endl;
	else cout<<"\n\nstart solving\n\n"<<endl;
	vec<LitArith> dummy;
	S.newDecisionLevel();
	S.uncheckedEnqueue(S.PickFirstLit());

	lbool ret = S.solveLimited(dummy);


	if(S.ok==true) printf("TRUE\n");else printf("FALSE\n");
	printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
	if (ret == l_True)
        {
            printf("SAT\n");
            for (int i = 0; i < S.nVars(); i++)
                if (S.model[i] != l_Undef)
                    printf("%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
            printf(" 0\n");
        }
    return 0;
}
