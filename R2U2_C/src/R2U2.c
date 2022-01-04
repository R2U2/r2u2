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

#if R2U2_DEBUG
/* Provides the global debug file pointer used via extern in r2u2.h */
FILE* r2u2_debug_fptr = NULL;
#endif

/* Forward definition of CSV header ordering from aux files */
int signal_aux_config(char*, FILE*, uintptr_t*);

int main(int argc, char *argv[]) {

    #ifndef CONFIG
    uint8_t n_args_req = 2;
    #else
    uint8_t n_args_req = 1;
    #endif

    if (argc < n_args_req) {
        fprintf(stderr,"R2U2 Version %d.%d\n",
            R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR);
        fprintf(stderr, "%s", usage);
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

    const uint32_t MAX_TIME = UINT32_MAX;
    int c;
    FILE *input_file = NULL;
    char *signal, inbuf[BUFSIZ]; // LINE_MAX instead? PATH_MAX??

    // Extensible way to loop over CLI options
    while((c = getopt(argc, argv, "h")) != -1) {
      switch(c) {
        case 'h': {
          fprintf(stdout, "%s", usage);
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

    uint8_t argind = (unsigned char) optind;

    #ifndef CONFIG // Compilation is using binaries
    // TODO check that config directory is a valid path
    char *bin_dir = argv[argind];
    argind++;
    chdir(bin_dir);
    #endif

    TL_config("ftm.bin", "fti.bin", "ftscq.bin", "ptm.bin", "pti.bin");
    #if R2U2_TL_Formula_Names || R2U2_TL_Contract_Status || R2U2_AT_Signal_Sets
    TL_aux_config("alias.txt");
    #endif
    TL_init();
    AT_config("at.bin");
    AT_init();

    #ifndef CONFIG
    chdir(inbuf);
    #endif

    /* Input configuration */
    if(argind < argc) { // The trace file was specified
      if (access(argv[argind], F_OK) == 0) {
        input_file = fopen(argv[argind], "r");
        if (input_file == NULL) {
          fprintf(stderr, "Invalid trace filename");
          return 1;
        }
      }
    } else { // Trace file not specified, use stdin
      input_file = stdin;
    }

    #if R2U2_CSV_Header_Mapping
    chdir(bin_dir);
    int header_status = 0;
    uintptr_t alias_table[N_SIGS];
    header_status = signal_aux_config("alias.txt", input_file, alias_table);
    if (header_status > 1) { return header_status; }
    chdir(inbuf);
    #endif

    /* R2U2 Output File */
    FILE *log_file;
    log_file = fopen("./R2U2.log", "w+");
    if(log_file == NULL) return 1;

    /* R2U2 Debug File */
    #if R2U2_DEBUG
    r2u2_debug_fptr = stderr;
    // Set to stderr by default, uncoimment below for file output
    // r2u2_debug_fptr = fopen("./R2U2_dbg.log", "w+");
    // if(r2u2_debug_fptr == NULL) return 10;
    #endif

    /* Main processing loop */
    uint32_t cur_time = 0, i;
    for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {

        if(fgets(inbuf, sizeof inbuf, input_file) == NULL) break;

        #if R2U2_CSV_Header_Mapping
        if (cur_time == 0 && inbuf[0] == '#') {
          /* Skip Header row, if it exists */
          if(fgets(inbuf, sizeof inbuf, input_file) == NULL) break;
        }

        if (header_status == 1) {
          /* Use CSV header reordering */
          for(i = 0, signal = strtok(inbuf, ",\n"); signal; i++,
              signal = strtok(NULL, ",\n")) {
                signals_vector[alias_table[i]] = signal;
            }
        } else {
          /* Use CSV columns in order given */
          for(i = 0, signal = strtok(inbuf, ",\n"); signal; i++,
              signal = strtok(NULL, ",\n")) {
                signals_vector[i] = signal;
            }
        }
        #else
        for(i = 0, signal = strtok(inbuf, ",\n"); signal; i++,
            signal = strtok(NULL, ",\n")) {
              signals_vector[i] = signal;
        }
        #endif


        R2U2_DEBUG_PRINT("\n----------TIME STEP: %d----------\n",cur_time);

        /* Atomics Update */
        AT_update();

        /* Temporal Logic Update */
        TL_update(log_file);
    }

    fclose(log_file);

    AT_free();

    return 0;
}

int signal_aux_config(char* aux, FILE* input_file, uintptr_t* alias_table){
  /*
  Load signal mapping from aux file and map CSV

  Return values:
    Success values
    0: No column defs found - do not use header mapping
    1: Column defs loaded successfully, use header mapping
    -----------------------------------------------------
    Error values:
    3: Invalid signal definition
    4: Aux file exists but can't be opened
    5: Error reading CSV header
    6: Missing a column for a listed signal
  */
  // TODO: unify this with aux file load or keep separate?
      // If using CSV input and alias exists, set alias flag
  // Read aux file for
  FILE *alias_file = NULL;
  uintptr_t idx, col_num;
  char type, *signal, *scan_ptr;
  char aliasname[BUFSIZ], inbuf[BUFSIZ], line[MAX_LINE]; // LINE_MAX instead? PATH_MAX??

  int alias_order = 0;
  if (access(aux, F_OK) == 0) {
    alias_file = fopen(aux, "r");
    if (alias_file != NULL) {

      /* Put CSV header (from input_file pointer) into inbuf buffer */
      if((fgets(inbuf, sizeof(inbuf), input_file) == NULL) || (inbuf[0] != '#') ){
        fprintf(stderr, "Can't read input header\n");
        return 5;
      }

      /* Initialize lookup table - default to natural number order */
      for(idx = 0; idx < N_SIGS; idx++){ alias_table[idx] = idx;}

      while(fgets(line, sizeof(line), alias_file) != NULL) {
        if(sscanf(line, "%c", &type) == 1 && type == 'S') {
          /* Found a signal definition, look for matching header */
          if(sscanf(line, "%*c %s %ld", aliasname, &idx) == 2){
            if((signal = strstr(inbuf, aliasname)) != NULL){
              col_num = 0;
              for(scan_ptr=inbuf;scan_ptr != signal;scan_ptr++){
                /* Walk through header, counting columns
                 * Slower but lower memory than finding all columns first
                 */
                if(*scan_ptr == ',') {col_num += 1;}
              }
              alias_table[col_num] = idx;
            } else {
              fprintf(stderr, "No matching Column for: %s\n", aliasname);
              return 6;
            }
          } else {
            /* Invalid signal line */
            fprintf(stderr, "The signal mapping '%s' is invalid\n", line);
            return 3;
          }
          alias_order = 1; /* Flag that reordering should be used */
        }
      }
      fclose(alias_file);

    } else { /* Cannot open aux file which appears available */
      perror(aux);
      return 4;
    }
  }
  return alias_order;
}
