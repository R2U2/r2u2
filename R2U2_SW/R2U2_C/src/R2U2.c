#include <stdio.h>
#include <stdlib.h>

#include "R2U2Config.h"
#include "TL/TL_observers.h"
#include "AT/at_checkers.h"

int main(int argc, char const *argv[]) {
    fprintf(stdout,"%s Version %d.%d\n",
            argv[0],
            R2U2_C_VERSION_MAJOR,
            R2U2_C_VERSION_MINOR);


    /* Get Config */
    static int MAX_TIME = 5; /* TODO: Replace with sensor data */
    static int NUM_SIG = 2;    /* TODO: Replace with sensor data */
    r2u2_in_type in_dat[5][2] = {{0, 1},
                                 {2, 3},
                                 {4, 5},
                                 {6, 7},
                                 {8, 9}};

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
    //int l_interval_mem_ft; // (not found, not used?)

    /* Allocate Memory */
    r2u2_in_type *cur_sigs;
    cur_sigs = malloc(sizeof(r2u2_in_type) * NUM_SIG);
    if (cur_sigs == NULL) return 1;
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

        /* Temporal Logic Update */
        /* TODO: Why does this require file pointers? */
        TL_update(out_file, dbg_file);

        fprintf(out_file,"\n\n");
        fprintf(dbg_file, "\n");

        /* Copy outputs from vectors */

    }

    /* TODO: GNU Plot printing */

    fclose(out_file);
    fclose(dbg_file);
    return 0;
}