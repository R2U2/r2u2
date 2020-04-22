#include <stdio.h>
#include <unistd.h>
#include <limits.h>
#include <string.h>

#include "R2U2Config.h"
#include "binParser/parse.h"
#include "TL/TL_observers.h"
// #include "AT/at_checkers.h"

int main(int argc, char *argv[]) {
    // TODO: Better CLI parsing
    if (argc < 4 || argc > 5) {
        fprintf(stdout,"%s Version %d.%d\n",
        argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stdout, "Usage: 1) .ftm, 2) .fti, 3) .ftscq, 4) trace data file (or none for stdin)\n");
    }
    int MAX_TIME = INT_MAX;
    FILE *input_file;
    char inbuf[BUFSIZ];

    /* Engine Initialization */
    TL_init();
    // at_checkers_init();
    // TODO: Does this crash on bad bins?
    // TODO: Weird memory stuff to be checked
    TL_init_files(argv[1],argv[2],argv[3]);

    /* Select file vs stream */
    if (argc == 5 && (access( argv[4], F_OK ) == 0))
    {
        input_file = fopen(argv[4], "r");
        if (input_file == NULL) return 1;
    } else {
        input_file = stdin;
    }

    // R2U2 Output File
    FILE *log_file;
    log_file = fopen("./R2U2.log", "w+");
    // TODO: Name after input and output
    if(log_file == NULL) return 1;
    printf("**********RESULTS**********\n");
    fprintf(log_file, "**********RESULTS**********\n");

    /* Main processing loop */
    int cur_time = 0;
    for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {

        if(fgets(inbuf, sizeof inbuf, input_file) == NULL) break;
        for (int atom = 0; atom < strlen(inbuf)/2; ++atom) {
            if (sscanf(&inbuf[2*atom], "%d", &atomics_vector[atom]) == 0) return 1;
        }

        // Terminal and log file headings, when in debug mode
        #ifdef DEBUG
        // Print to the terminal
        printf("\n**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****\n",cur_time);
        // Print to the '.log' file
        fprintf(log_file, "----------TIME STEP: %d----------\n", cur_time);
        #endif

        /* Atomics Update */
        // at_checkers_update(cur_sigs);

        /* Temporal Logic Update */
        TL_update(log_file);

    }
    fclose(log_file);

    return 0;
}

