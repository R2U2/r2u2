#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "at_checkers.h"
#include "at_globals.h"

#define MAX_TIME 256

int
main(int argc, char *argv[])
{
	FILE *input_file;
	if((input_file = fopen("test.csv", "r")) == NULL)
		perror("Error opening input file");

	char inbuf[BUFFER_SIZE];

	/*
	 * initialize AT checker
	 * need some way to take user input to get these instructions
	 */
	num_instr = 4;

	instructions[0].comp = EQ;
	instructions[0].opcode = OP_BOOL;
	instructions[0].sig_addr = 0;
	instructions[0].atom_addr = 0;

	instructions[1].comp = LT;
	instructions[1].opcode = OP_INT;
	instructions[1].sig_addr = 1;
	instructions[1].comp_const.i = 8;
	instructions[1].atom_addr = 1;

	instructions[2].comp = GT;
	instructions[2].opcode = OP_ABS_DIFF_ANGLE;
	instructions[2].sig_addr = 2;
	instructions[2].filt_data_struct.diff_angle = 90;
	instructions[2].comp_const.d = 30;
	instructions[2].atom_addr = 2;

	instructions[3].comp = GT;
	instructions[3].opcode = OP_MOVAVG;
	instructions[3].sig_addr = 3;
	instructions[3].comp_const.d = 3;
	instructions[3].atom_addr = 3;

	at_checkers_init();

	uint8_t cur_time;
	for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {

		if(!fgets(inbuf, sizeof(inbuf), input_file))
			break;

		uint8_t i, num_sigs;
		char *signal;

		/* fetch each signal and read as correct format */
		for(i = 0, signal = strtok(inbuf, ",\n"); signal; i++, signal = strtok(NULL, ",\n")) {
			switch(instructions[i].opcode) {
				case OP_BOOL:			sscanf(signal, "%hhu", &signals_vector[i].b);
										break;
				case OP_INT:			sscanf(signal, "%d", &signals_vector[i].i);
										break;
				case OP_DOUBLE: 		sscanf(signal, "%lf", &signals_vector[i].d);
										break;
				case OP_ABS_DIFF_ANGLE: sscanf(signal, "%lf", &signals_vector[i].d);
										break;
				case OP_MOVAVG:			sscanf(signal, "%d", &signals_vector[i].i);
										break;
				case OP_RATE:			sscanf(signal, "%lf", &signals_vector[i].d);
										break;
			}
		}

		num_sigs = i;

		/* execute each instruction */
		at_checkers_update();

		for(i = 0; i < num_instr; i++ ) {
			printf("%d", atomics_vector[i]);
			if(i != num_sigs-1)
				printf(",");
		}

		printf("\n");

	}
}
