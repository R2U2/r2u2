#include <stdint.h>
#include <stdbool.h>

#include "R2U2.h"
#include "../bz/bz_booleanizer.h"
#include "parse.h"

#define BUFFER_SIZE 256

int parse_bz(FILE *fp)
{
	bool ok;
	uint32_t i;
	uint8_t buffer[BUFFER_SIZE];

	ok = fread(&bz.num_instr, sizeof(uint32_t), 1, fp) == sizeof(uint32_t);

	printf("Number BZ instruction: %08X, %d\n", bz.num_instr, bz.num_instr);

	ok = fread(buffer, 1, BUFFER_SIZE, fp) == BUFFER_SIZE || feof(fp);

	printf("First BZ byte: %02X\n", buffer[0]);

	// for(i = 0; i < bz.num_instr; ++i) {
	// 	// if(bz_opcode_has_param()) {

	// 	// }
	// }

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