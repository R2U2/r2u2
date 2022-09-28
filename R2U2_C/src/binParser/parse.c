#include "R2U2.h"
#include "parse.h"

#include <stdint.h>

#define MAX_LINE 256

int parse_bz(FILE *fp)
{
	

	return 0;
}

int parse_ft(FILE *fp)
{
	return 0;
}

int parse_pt(FILE *fp)
{
	return 0;
}

int parse(const char *filename)
{
	FILE *file = fopen (filename, "r");

    if (file != NULL) {
		parse_bz(file);
		parse_ft(file);
		parse_pt(file);
		fclose(file);
	} else {
		perror(filename);
	}

    return 0;
}