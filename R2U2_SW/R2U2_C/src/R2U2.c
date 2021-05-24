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
const char *usage = "Usage: r2u2 <configuration directory> [trace-file] [-h]\n"
                    "trace-file \t csv file with recorded signal values\n"
                    "-h \t\t print this help statement\n";
#else
const char *usage = "Usage: r2u2 [trace-file] [-h]\n"
                    "trace-file \t csv file with recorded signal values\n"
                    "-h \t\t print this help statement\n";
#endif

int main(int argc, char *argv[]) {

    #ifndef CONFIG
    uint8_t n_args_req = 2;
    #else
    uint8_t n_args_req = 1;
    #endif

    if (argc < n_args_req) {
        fprintf(stderr,"R2U2 Version %d.%d\n",
            R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stderr, usage);
        return 1;
    }

    else if (argc == 2) {
	     fprintf(stdout,"%s Version %d.%d\n",
	             argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
	     fprintf(stdout, "Configuration directory path: %s. Command line input will be used for trace file path.\n", argv[1]);
    }

    else if (argc == 3) {
	     fprintf(stdout,"%s Version %d.%d\n",
	             argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
	     fprintf(stdout, "Configuration directory path: %s. Trace file path: %s.\n", argv[1], argv[2]);
    }

    else {
	     fprintf(stdout,"%s Version %d.%d\n",
	             argv[0], R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
	     fprintf(stdout, "Too many arguments supplied. Configuration directory path: %s. Trace file path: %s. Other arguments will be ignored.\n", argv[1], argv[2]);
    }

    int MAX_TIME = INT_MAX, c;
    FILE *input_file = NULL;
    char inbuf[BUFSIZ]; // LINE_MAX instead? PATH_MAX??

    // Extensible way to loop over CLI options
    while((c = getopt(argc, argv, "h")) != -1) {
      switch(c) {
        case 'h': {
          fprintf(stdout, usage);
          return 1;
        }
        case '?': {
          fprintf(stderr, "Unknown option %x", optopt);
          return 1;
        }
        default: {
          return 1; // something went wrong with getopt
        }
      }
    }

    /* Engine Initialization */
    if (getcwd(inbuf, sizeof(inbuf)) == NULL) {
      fprintf(stderr, "Error retrieving cwd");
      return 1;
    }

    uint8_t argind = optind;

    #ifndef CONFIG // Compilation is using binaries
    // TODO check that config directory is a valid path
    chdir(argv[argind]);
    argind++;
    #endif

    TL_config("ftm.bin", "fti.bin", "ftscq.bin", "ptm.bin", "pti.bin");
    TL_init();
    AT_config("at.bin");
    AT_init();

    #ifndef CONFIG
    chdir(inbuf);
    #endif

    /* Input configuration */
    if(argind < argc) { // The trace file was specified
      char *trace_filename = argv[argind];
      if (access(trace_filename, F_OK) == 0) {
        input_file = fopen(trace_filename, "r");
        if (input_file == NULL) {
          fprintf(stderr, "Invalid trace filename");
          return 1;
        }
      }
    } else { // Trace file not specified, use stdin
      input_file = stdin;
    }

    /* R2U2 Output File */
    FILE *log_file;
    log_file = fopen("./R2U2.log", "w+");
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
