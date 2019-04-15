#include <stdio.h>
#include <stdlib.h>

/* From vendored libs */
#include "csvparser.h"

#include "R2U2Config.h"
#include "TL/TL_observers.h"
#include "AT/at_checkers.h"

void count_signals(char*, int*, int*);
r2u2_in_type** load_signals(char*, int, int);

int main(int argc, char const *argv[]) {

if (argc != 2) {
    fprintf(stdout,"%s Version %d.%d\n",
            argv[0],
            R2U2_C_VERSION_MAJOR,
            R2U2_C_VERSION_MINOR);
    fprintf(stdout, "Usage: input data file name\n");
}



    /* Get Config */
    int MAX_TIME;    /* TODO: Replace with sensor data */
    int NUM_SIG;     /* TODO: Replace with sensor data */
    count_signals(argv[1], &NUM_SIG, &MAX_TIME);
    printf("Found %d signals across %d timesteps\n", NUM_SIG, MAX_TIME);
    r2u2_in_type **in_dat = load_signals(argv[1], NUM_SIG, MAX_TIME);

    static int NUM_ATM = 2;     /* TODO: Replace with config data */

    /* TODO: Dynamically load from *_ft.c */
    /* Currently provied by test0006_ft.c */
    //instruction_mem_t instruction_mem_ft;

    /* TODO: Dynamically load from *_pt.c */
    //instruction_mem_t instruction_mem_pt;

    /* Dynamicly load from _pti.c */
    //interval_t interval_mem_pt[];
    //int l_interval_mem_pt;

    /* TODO: Dynamicly load from *_fti.c */
    //interval_t interval_mem_ft[];

    /* Allocate Memory */
    r2u2_in_type *cur_sigs;
    cur_sigs = malloc(sizeof(r2u2_in_type) * NUM_SIG);
    if (cur_sigs == NULL) return 1;

    bool **atom_out;
    atom_out = malloc(sizeof(bool *) * MAX_TIME);
    for (int i=0; i<MAX_TIME; i++) {
        atom_out[i] = malloc(sizeof(bool) * NUM_ATM);
    }

    /* TODO: Alloc full results buffers - memory map to file? */

    /* Engine Initialization */
    TL_init();
    at_checkers_init();

    /* Open File Output  */
    FILE *out_file, *dbg_file;
    out_file = fopen("./R2U2.out", "w+");
    dbg_file = fopen("./R2U2.log", "w+");
    if ((out_file == NULL) || (dbg_file == NULL)) return 1;
    fprintf(dbg_file, "**********RESULTS**********\n\n");
    /* TODO: Async file I/O */

    /* Main processing loop */
    for (int cur_time=0; cur_time < MAX_TIME; cur_time++) {
        printf("\n");
        printf("***************************************");
        printf("**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****",cur_time+1);
        printf("***************************************");
        printf("\n");

        fprintf(out_file, "**********CURRENT TIME STEP: %d**********\n\n", cur_time+1);

        fprintf(dbg_file, "----------TIME STEP: %d----------\n", cur_time);


        /* Sensor values for current time step */
        /* TODO: Replace with memory map */
        for (int i=0; i<NUM_SIG; i++) {cur_sigs[i] = in_dat[cur_time][i];}

        /* Atomics Update */
        at_checkers_update(cur_sigs);
        for (int i=0; i<NUM_ATM; i++) {atom_out[cur_time][i] = atomics_vector[i];}
        /* TODO: Memcopy? Memory-maped file */
        //printf("\n[DBG] t=%d; ATOMICS VECTOR:\n",cur_time);
        //for (int i=0; i<NUM_ATM; i++){
        //    printf("%1.1d",atomics_vector[i]);
        //    /* TODO: Getride of theese hardcodes */
        //    if (i%8 == 7)  printf(" ");
        //    if (i%32 == 31)  printf("\n");
        //}
        //printf("\n");

        /* Temporal Logic Update */
        /* TODO: Why does this require file pointers? */
        TL_update(out_file, dbg_file);

        fprintf(out_file,"\n\n");
        fprintf(dbg_file, "\n");

        /* Copy outputs from vectors */

    }

    /* TODO: GNU Plot printing? */

    /* Old Outputs:
        1. Atomics:     atom_out
        2. PT Results:  xxx
        3. FT Results:  xxx
        4. Async Results: xxx
        5. Progonstics Results: xxx
        6. Async Timing: xxx
    */

    fclose(out_file);
    fclose(dbg_file);
    return 0;
}

void count_signals(char* data_file, int* NUM_SIG, int* MAX_TIME) {
    int i =  0;
    *MAX_TIME = 0;
    *NUM_SIG = 0;
    //                                   file, delimiter, first_line_is_header?
    CsvParser *csvparser = CsvParser_new(data_file, " ", 0);
    CsvRow *row;

    while ((row = CsvParser_getRow(csvparser)) ) {
        /* Ignore header rows */
        if (CsvParser_getFields(row)[0][0] == '#') { continue; }

        if (*NUM_SIG == 0) {
            *NUM_SIG = CsvParser_getNumFields(row);
        } else {
            if (CsvParser_getNumFields(row) != *NUM_SIG) {
                /* Inconsistant number of signals */
                /* TODO: Handle errors properl */
                printf("WARNING: Improper signal file - row ignored!\n\tFound: %d\tExpected: %d\n", CsvParser_getNumFields(row), *NUM_SIG);
            } else {
                *MAX_TIME += 1;
            }
        }
        CsvParser_destroy_row(row);
    }
    CsvParser_destroy(csvparser);
}

r2u2_in_type** load_signals(char* data_file, int NUM_SIG, int MAX_TIME) {
    int i =  0;
    //                                   file, delimiter, first_line_is_header?
    CsvParser *csvparser = CsvParser_new(data_file, " ", 0);
    CsvRow *row;
    /* Malloc Input data array */
    r2u2_in_type **in_dat;
    in_dat = malloc(sizeof(r2u2_in_type *) * MAX_TIME);
    for (int i=0; i<MAX_TIME; i++) {
        row = CsvParser_getRow(csvparser);
        const char **rowFields = CsvParser_getFields(row);
        if (rowFields[0][0] == '#') { continue; }
        /* TODO: Replace NUM_SIG with NUM_ATM */
        in_dat[i] = malloc(sizeof(r2u2_in_type) * NUM_SIG);
        for (int j=0; j<NUM_SIG; j++) {
            sscanf(rowFields[j], "%lf", &in_dat[i][j]);
        }
        CsvParser_destroy_row(row);
    }
    CsvParser_destroy(csvparser);

    return in_dat;
}