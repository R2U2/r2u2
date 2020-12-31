#include <stdio.h>
#include <unistd.h>
#include <getopt.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>

#include "R2U2.h"
#include "R2U2Config.h"
#include "binParser/parse.h"
#include "TL/TL_observers.h"
#include "AT/at_checkers.h"
#include "AT/at_globals.h"

#ifndef CONFIG
const char *usage = "Usage: <configuration directory> [-t trace-file] [-h]\n"
                    "-t trace-file \t csv file with recorded signal values\n"
                    "-h \t\t print this help statement\n";
#else
const char *usage = "Usage: [-t trace-file] [-h]\n"
                    "-t trace-file \t csv file with recorded signal values\n"
                    "-h \t\t print this help statement\n";
#endif

int main(int argc, char *argv[]) {

    if (argc < 2) {
        fprintf(stderr,"%s Version %d.%d\n",
            argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stderr, usage);
        return 1;
    }

    uint8_t no_files = 0, c;
    int MAX_TIME = INT_MAX;
    FILE *input_file;
    char inbuf[BUFSIZ]; // LINE_MAX instead? PATH_MAX??

    while((c = getopt(argc, argv, "t:h")) != -1) {
      switch(c) {
        case 't':
          if (access(optarg, F_OK) == 0) {
            input_file = fopen(optarg, "r");
            if (input_file == NULL) {
              fprintf(stderr, "Invalid trace filename");
              return 1;
            }
          } else {
            input_file = stdin;
          }
          break;
        case 'h':
          fprintf(stdout, usage);
          return 1;
        case '?':
          if(optopt == 't')
            fprintf(stderr, "Option -%c requires an argument\n", optopt);
          else
            fprintf(stderr, "Unknown option %x", optopt);
          return 1;
        default:
          return 1; // something went wrong with getopt
      }
    }

    /* Engine Initialization */
    if (getcwd(inbuf, sizeof(inbuf)) == NULL) {
      fprintf(stderr, "Error retrieving cwd");
      return 1;
    }
    // TODO check that config directory is a valid path
    chdir(argv[optind]);

    TL_config("ftm.bin", "fti.bin", "ftscq.bin", "ptm.bin", "pti.bin");
    TL_init();
    AT_config("at.bin");
    AT_init();

    chdir(inbuf);

    // R2U2 Output File
    FILE *log_file;
    log_file = fopen("./R2U2.log", "w+");
    // TODO: Name after input and output
    if(log_file == NULL) return 1;


    /* Main processing loop */
    uint32_t cur_time = 0, i;
    char *signal;
    for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {

        if(fgets(inbuf, sizeof inbuf, input_file) == NULL) break;

        for(i = 0, signal = strtok(inbuf, ",\n"); signal; i++,
            signal = strtok(NULL, ",\n")) {
              signals_vector[i] = signal;
          }

        DEBUG_PRINT("\n----------TIME STEP: %d----------\n",cur_time);

        /* Atomics Update */
        AT_update(cur_time);

        /* Temporal Logic Update */
        TL_update(log_file);

    }

    fclose(log_file);

    AT_free();

    return 0;
}
