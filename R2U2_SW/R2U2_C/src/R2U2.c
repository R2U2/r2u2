#include <stdio.h>
#include <unistd.h>
#include <limits.h>
#include <string.h>

#include "R2U2.h"
#include "R2U2Config.h"
#include "binParser/parse.h"
#include "TL/TL_observers.h"
// #include "AT/at_checkers.h"

int main(int argc, char *argv[]) {
    // TODO: Better CLI parsing
    if (argc < 2) {
        fprintf(stdout,"%s Version %d.%d\n",
        argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stdout, "Usage: 1) .ftm, 2) .fti, 3) .ftscq, 4) trace data file (or none for stdin)\n");
    }
    int MAX_TIME = INT_MAX;
    FILE *input_file;
    char inbuf[BUFSIZ];

    /* Find configuration files */
    TL_asm_files tl_asm_files;
    // for (int i = 0; i < 3; ++i) {
    //     tl_asm_files[i] = fopen("ftm.bin", "r");
    // }
    tl_asm_files[0] = fopen("ftm.bin", "r");
    tl_asm_files[1] = fopen("fti.bin", "r");
    tl_asm_files[2] = fopen("ftscq.bin", "r");
    TL_config(tl_asm_files);
    for (int i = 0; i < 3; ++i) {
        fclose(tl_asm_files[i]);
    }

    /* Engine Initialization */
    TL_init();
    // at_checkers_init();

    /* Select file vs stream */
    // TODO: Really need some better handeling
    if (access(argv[1], F_OK) == 0) {
        input_file = fopen(argv[1], "r");
        if (input_file == NULL) return 1;
    } else {
        input_file = stdin;
    }

    // R2U2 Output File
    FILE *log_file;
    log_file = fopen("./R2U2.log", "w+");
    // TODO: Name after input and output
    if(log_file == NULL) return 1;

    /* Main processing loop */
    int cur_time = 0;
    for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {

        if(fgets(inbuf, sizeof inbuf, input_file) == NULL) break;
        for (size_t atom = 0; atom < strlen(inbuf)/2; ++atom) {
            if (sscanf(&inbuf[2*atom], "%d", &atomics_vector[atom]) == 0) return 1;
        }

        DEBUG_PRINT("\n----------TIME STEP: %d----------\n",cur_time);

        /* Atomics Update */
        // at_checkers_update(cur_sigs);

        /* Temporal Logic Update */
        TL_update(log_file);

    }
    fclose(log_file);

    return 0;
}

