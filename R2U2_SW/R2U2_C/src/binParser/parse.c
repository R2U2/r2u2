#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "TL_observers.h"


bool* string2bin(char* s) {
	int len = strlen(s);
	bool* res = (bool*) malloc(len);
	for(int i=0; i<len; i++) {
		char tmp = *(s+i);
		*(res+i) = (bool)(tmp-'0');
		printf("%d ",*(res+i));
	}
	return res;
}




// instruction_mem_t decode_inst(char* line) {

// }




// instruction_mem_t parse_inst(char* filename) {
int parse_inst(char* filename) {
	instruction_mem_t instruction_mem_ft;
	FILE *file = fopen ( filename, "r" );
	if ( file != NULL ) {
		char line [128]; /* or other suitable maximum line size */
		while ( fgets (line, sizeof(line), file ) != NULL ) {/* read a line */
	    	// fputs ( line, stdout ); /* write the line */
			// printf("%s",line);
			// instruction_mem_t inst = decode_inst(line);
			line[strcspn(line,"\n\r")] = 0; //remove ending special symbol
			string2bin(line);
			printf("\n");
		}
		fclose ( file );
	} else {
		perror ( filename ); /* why didn't the file open? */
	}
	return 0;

}
/*
interval_t parse_int(char* filename) {

}

addr_SCQ_map_t parse_scq_size(char* filename) {

}
*/