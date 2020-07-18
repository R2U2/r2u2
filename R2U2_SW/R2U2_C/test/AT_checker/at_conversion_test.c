#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define BUFFER_SIZE 256
#define MAX_TIME 256

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

	/* initialize AT checker */
	instruction_t instr0;
	instr0.opcode = lt;
	instr0.sig_addr = 0;
	instr0.constant = 5;
	instr0.atom_addr = 0;

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

		filters[instr0.opcode](&atomics_vector[instr0.atom_addr], 
							   &signals_vector[instr0.sig_addr], 
							   instr0.constant);

		for(atom = 0; atom < num_sigs; atom++ ) {
			printf("%d\n", atomics_vector[atom]);
		}
		
		//at_checkers_update(&atomics_vector);	

	}
}
