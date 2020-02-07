/* From vendored libs */
#include "csvparser.h"
#include "R2U2Config.h"
#include<stdlib.h>

void count_signals(const char* data_file, int* NUM_SIG, int* MAX_TIME) {
	int i =  0;
	*MAX_TIME = 0;
	*NUM_SIG = 0;
	// file, delimiter, first_line_is_header?
	CsvParser *csvparser = CsvParser_new(data_file, ",", 1);
	CsvRow *row;

	while ((row = CsvParser_getRow(csvparser)) ) {
		/* Ignore header rows */
		if (CsvParser_getFields(row)[0][0] == '#') { continue; }

		if (*NUM_SIG == 0) *NUM_SIG = CsvParser_getNumFields(row);
		if (CsvParser_getNumFields(row) != *NUM_SIG) {
			/* Inconsistant number of signals */
			/* TODO: Handle errors properly */
			printf("WARNING: Improper signal file - row ignored!\n\tFound: %d\tExpected: %d\n", CsvParser_getNumFields(row), *NUM_SIG);
		} else {
			*MAX_TIME += 1;
		}
		CsvParser_destroy_row(row);
	}
	CsvParser_destroy(csvparser);
	printf("Found %d signals across %d timesteps\n", *NUM_SIG, *MAX_TIME);
}

void load_signals(const char* data_file, int NUM_SIG, int MAX_TIME, r2u2_in_type** in_dat) {
	// file, delimiter, first_line_is_header?
	CsvParser *csvparser = CsvParser_new(data_file, ",", 1);
	CsvRow *row;
	
	for (int i=0; i<MAX_TIME; i++) {
		in_dat[i] = (r2u2_in_type*)malloc(NUM_SIG * sizeof(r2u2_in_type)); 
		row = CsvParser_getRow(csvparser);
		const char **rowFields = CsvParser_getFields(row);
		if (rowFields[0][0] == '#') { continue; }
		for (int j=0; j<NUM_SIG; j++) {
			sscanf(rowFields[j], "%lf",&in_dat[i][j]); // issue here
		}
		CsvParser_destroy_row(row);
	}
	CsvParser_destroy(csvparser);
}


void decodeCSV(const char* csv_file, r2u2_in_type** in_dat, int* MAX_TIME, int* NUM_SIG) {
	/* Get Config */
	// count_signals(csv_file, NUM_SIG, MAX_TIME);
	// printf("Found %d signals across %d timesteps\n", *NUM_SIG, *MAX_TIME);
	// load_signals(csv_file, *NUM_SIG, *MAX_TIME, in_dat);
	/* Allocate Memory */
}
