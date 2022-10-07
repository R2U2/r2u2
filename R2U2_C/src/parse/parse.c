#include <stdint.h>
#include <stdbool.h>

#include "R2U2.h"
#include "../bz/bz_booleanizer.h"
#include "parse.h"

#define BUFFER_SIZE 8

bool has_param(bz_opcode_t opcode) 
{
	return opcode == BZ_STORE  || opcode == BZ_ILOAD  || opcode == BZ_FLOAD ||
		   opcode == BZ_ICONST || opcode == BZ_FCONST || opcode == BZ_FEQ ||
		   opcode == BZ_FNEQ   || opcode >= BZ_AUX1 ;
}

int parse_bz(FILE *fp)
{
	bool ok;
	uint32_t i, j;
	uint8_t buffer[BUFFER_SIZE], opcode;
	uint64_t s; // number of bytes to read

	ok = fread(&s, sizeof(uint64_t), 1, fp) == sizeof(uint64_t);

	printf("bytes to read: %lu\n", s);

	ok = fread(buffer, 1, BUFFER_SIZE, fp) == BUFFER_SIZE || feof(fp);

	// printf("ok? %hhu\n", ok);

	i = 0, j = 0;
	while(buffer[i] != BZ_NONE && ok) {
		bz.instructions[j].opcode = buffer[i];

		switch (buffer[i]) {
		case BZ_STORE:
			printf("store %u\n", buffer[i+1]);
			break;
		case BZ_ILOAD:
			printf("iload %u\n", buffer[i+1]);
			break;
		case BZ_ICONST:
			printf("iconst %d\n", buffer[i+1]);
			break;
		case BZ_IGT:
			printf("igt\n");
			break;
		case BZ_ILT:
			printf("ilt\n");
			break;
		case BZ_IADD:
			printf("iadd\n");
			break;
		default:
			printf("%02X\n",buffer[i]);
			break;
		}

		i++, j++;

		if(has_param(buffer[i])) {
			bz.instructions[j].param.i = buffer[i];
			i += sizeof(uint32_t);
		}


		if(i >= BUFFER_SIZE) {
			ok = fread(buffer, 1, BUFFER_SIZE, fp) == BUFFER_SIZE || feof(fp);
			i = 0;
		}
	}

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