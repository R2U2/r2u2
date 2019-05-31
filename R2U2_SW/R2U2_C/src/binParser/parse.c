#include <stdio.h>
#include <stdlib.h>
#include "TL_observers.h"


instruction_mem_t parse_inst(char* filename) {
	instruction_mem_t instruction_mem_ft;
	char c[1000];
	FILE *fptr;

	if ((fptr = fopen(filename, "r")) == NULL) {
		printf("Error! Cannot find instruction file.");
		// Program exits if file pointer returns NULL.
		exit(1);         
	}
	fscanf(fptr,"%[^\n]", c);

	printf("Data from the file:\n%s", c);
	fclose(fptr);
    
	return 0;

}

interval_t parse_int(char* filename) {

}

addr_SCQ_map_t parse_scq_size(char* filename) {

}