#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../../src/AT/filter_abs_diff_angle.h"
#include "../../src/AT/filter_movavg.h"
#include "../../src/AT/filter_rate.h"

#include "compare.h"

#define BUFFER_SIZE 256
#define MAX_TIME 256
#define MAX_INSTR 256
#define MAX_SIGS 256

#define COMP(X,OP,Y) \
	((X) OP (Y)) ? 1 : 0

typedef enum {
	eq = 0,
	lt = 1,
	leq = 2,
	gt = 3,
	geq = 4
} comp_t;

typedef enum {
	boolean,
	integer,
	floating_point,
	movavg,
	diff_angle,
	rate
} sigtype_t;

typedef union {
	int integer;
	double floating_point;
} constant_type_t;

/* data structure for AT instructions */
typedef struct __attribute__((__packed__)) {
	comp_t comp;
	sigtype_t sig_type;
	uint8_t sig_addr;
	uint8_t atom_addr;
	constant_type_t constant;
} instruction_t;

typedef char *signals_vector_t[MAX_SIGS];
typedef uint8_t atomics_vector_t[BUFFER_SIZE];
typedef instruction_t instructions_t[MAX_INSTR];

/* similar to TL_observers? */
static signals_vector_t signals_vector;
static atomics_vector_t atomics_vector;
static instructions_t instructions;

/* filter lookup table */
void (*filters[])() = {};

/* integer comparison function lookup table */
int (*compare_int[])(int, int) = {compare_int_eq,
							      compare_int_lt,
								  compare_int_leq,
								  compare_int_gt,
								  compare_int_geq};
/* double comparison function lookup table */
int (*compare_double[])(double, double) = {compare_double_eq,
										   compare_double_lt,
										   compare_double_leq,
										   compare_double_gt,
										   compare_double_geq};

void
decode(instruction_t instruction)
{
	void *data;
	switch(instruction.sig_type) {
		case boolean:
			data = malloc(sizeof(uint8_t));
			sscanf(signals_vector[instruction.sig_addr], "%hhd", (uint8_t *)data);
			atomics_vector[instruction.atom_addr] = *(uint8_t *)data;
			break;

		case integer:
			data = malloc(sizeof(int));
			sscanf(signals_vector[instruction.sig_addr], "%d", (int *)data);
			atomics_vector[instruction.atom_addr] = 
				compare_int[instruction.comp](*(int *)data, instruction.constant.integer); 
			break;

		case floating_point:
			data = malloc(sizeof(double));
			sscanf(signals_vector[instruction.sig_addr], "%lf", (double *)data);
			atomics_vector[instruction.atom_addr] = 
				compare_double[instruction.comp](*(double *)data, instruction.constant.floating_point);
			break;

		case diff_angle:
			data = malloc(sizeof(double));
			sscanf(signals_vector[instruction.sig_addr], "%lf", (double *)data);
			break;
		
		case movavg:
			data = malloc(sizeof(double));
			sscanf(signals_vector[instruction.sig_addr], "%lf", (double *)data);
			break;

		case rate:
			data = malloc(sizeof(double));
			sscanf(signals_vector[instruction.sig_addr], "%lf", (double *)data);
			break;
	}

	free(data);
}

int 
main(int argc, char *argv[])
{
	FILE *input_file;
	if((input_file = fopen("test.csv", "r")) == NULL)
		perror("Error opening input file");

	char inbuf[BUFFER_SIZE];

	/* 
	 * initialize AT checker 
	 * could be put in initialization function
	 */
	uint8_t num_instr = 4;

	instructions[0].comp = eq;
	instructions[0].sig_type = boolean;
	instructions[0].sig_addr = 0;
	instructions[0].atom_addr = 0;

	instructions[1].comp = lt;
	instructions[1].sig_type = integer;
	instructions[1].sig_addr = 1;
	instructions[1].constant.integer = 8;
	instructions[1].atom_addr = 1;
	
	instructions[2].comp = gt;
	instructions[2].sig_type = floating_point;
	instructions[2].sig_addr = 2;
	instructions[2].constant.floating_point = 175;
	instructions[2].atom_addr = 2;

	instructions[3].comp = gt;
	instructions[3].sig_type = floating_point;
	instructions[3].sig_addr = 3;
	instructions[3].constant.floating_point = 4;
	instructions[3].atom_addr = 3;
	
	uint8_t cur_time;
	for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {
		
		if(fgets(inbuf, sizeof(inbuf), input_file) == NULL) 
			break;

		uint8_t i, num_sigs = 1;
	
		/* tokenize each input to a string */
		signals_vector[0] = strtok(inbuf, ",\n");
		for(i = 1; (signals_vector[i] = strtok(NULL, ",\n")) != NULL; i++, num_sigs++);

		/* decode each instruction */
		for(i = 0; i < num_instr; i++) {
			decode(instructions[i]);
		}
	
		for(i = 0; i < num_instr; i++ ) {
			printf("%d", atomics_vector[i]);
			if(i != num_sigs-1)
				printf(",");
		}
		
		printf("\n");

	}
}
