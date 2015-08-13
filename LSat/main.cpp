#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <zlib.h>

#include "parse/ParseUtils.h"
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
    parse_DIMACS(in, S, (bool)0);
    cout << "Hello world!" << endl;
    return 0;
}
