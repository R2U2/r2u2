#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define BUFFER_SIZE 256
#define MAX_TIME 256
#define MAX_INSTR 256

typedef enum {
	eq = 0b00,
	lt = 0b01,
	gt = 0b10
} opcode_t;

/* data structure for AT instructions */
typedef struct __attribute__((__packed__)) {
	opcode_t opcode;
	uint8_t sig_addr;
	uint8_t constant;
	uint8_t atom_addr;
} instruction_t;

typedef int signals_vector_t[BUFFER_SIZE];
typedef int atomics_vector_t[BUFFER_SIZE];
typedef instruction_t instructions_t[MAX_INSTR];

/* forward declaration of test filters */
void filter_eq_init(int *, int *);
void filter_lt_init(int *, int *);
void filter_gt_init(int *, int *);

void filter_eq(int *, int *, const uint8_t);
void filter_lt(int *, int *, const uint8_t);
void filter_gt(int *, int *, const uint8_t);

void filter_eq_free(int *, int *);
void filter_lt_free(int *, int *);
void filter_gt_free(int *, int *);

/* function lookup table */
void (*filters[])(int *, int *, const uint8_t) = {filter_eq, 
											  filter_lt, 
											  filter_gt};

void 
filter_eq(int *a, int *s, const uint8_t c)
{
	*a = (*s == c);
}

void 
filter_lt(int *a, int *s, const uint8_t c)
{
	*a = (*s < c);
}

void 
filter_gt(int *a, int *s, const uint8_t c)
{
	*a = (*s > c);
}

int 
main(int argc, char *argv[])
{
	FILE *input_file;
	if((input_file = fopen("test.csv", "r")) == NULL)
		perror("Error opening input file");

	char inbuf[BUFFER_SIZE];
	int num_sigs;
	signals_vector_t signals_vector;
	atomics_vector_t atomics_vector;
	instructions_t instructions;

	/* initialize AT checker */
	uint8_t num_instr = 3;

	instructions[0].opcode = eq;
	instructions[0].sig_addr = 0;
	instructions[0].constant = 1;
	instructions[0].atom_addr = 0;

	instructions[1].opcode = lt;
	instructions[1].sig_addr = 1;
	instructions[1].constant = 6;
	instructions[1].atom_addr = 1;
	
	instructions[2].opcode = gt;
	instructions[2].sig_addr = 2;
	instructions[2].constant = 4;
	instructions[2].atom_addr = 2;

	int cur_time;
	for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {
		
		if(fgets(inbuf, sizeof(inbuf), input_file) == NULL) 
			break;

		num_sigs = 0;

		/* NOTE: input signals have a fixed width of 1 */
		size_t atom;
		for(atom = 0; atom < strlen(inbuf)/2; ++atom) {
			if(!(sscanf(&inbuf[2*atom], "%d", (int *)&signals_vector[atom])))
				perror("Error reading input");
			num_sigs++;
			atomics_vector[atom] = 0;
		}

		int i;
		for(i = 0; i < num_instr; i++) {
			filters[instructions[i].opcode](&atomics_vector[instructions[i].atom_addr], 
				   						    &signals_vector[instructions[i].sig_addr], 
										    instructions[i].constant);
		}

		for(atom = 0; atom < num_sigs; atom++ ) {
			printf("%d", atomics_vector[atom]);
			if(atom != num_sigs-1)
				printf(",");
		}
		
		printf("\n");
		//at_checkers_update(&atomics_vector);	

	}
}
