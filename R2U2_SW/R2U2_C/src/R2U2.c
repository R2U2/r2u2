#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>

#include "R2U2Config.h"
#include "binParser/parse.h"
#include "TL/TL_observers.h"
#include "AT/at_checkers.h"

void sys_init(char *argv[]) {
    /* Engine Initialization */
    TL_init();
    at_checkers_init();
    //TL_init_files("src/inputs/tmp.ftm","src/inputs/tmp.fti","src/inputs/tmp.ftscq");
    TL_init_files(argv[2],argv[3],argv[4]);
}

int main(int argc, char *argv[]) {
    // TODO: Better CLI parsing
    if (argc != 4) {
        fprintf(stdout,"%s Version %d.%d\n",
        argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stdout, "Usage: 1) trace data file, 2) .ftm, 3) .fti, 4) .ftscq\n");
    }
    r2u2_in_type *cur_sigs = {1, 0};
    int MAX_TIME = INT_MAX, NUM_SIG = 0;
    char inbuf[BUFSIZ];

    while(access( argv[1], F_OK ) == -1) sleep(1);
    sys_init(argv); // TODO: Weird memory stuff to be checked

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

        fgets(inbuf, sizeof inbuf, stdin);
        if (inbuf[strlen(inbuf)-1] == '\n') {
            // read full line
        } else {
            // line was truncated
            return -7;
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

