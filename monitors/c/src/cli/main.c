#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>

#include "internals/config.h"
#include "internals/errors.h"
#include "cli/csv_trace.h"
#include "r2u2.h"
#if R2U2_TL_Contract_Status
#include "memory/contract_status.h"
#endif


// R2U2 Reference Implementation
// Provides example of library usage and "offline" monitoring
//
//
#define PRINT_VERSION() fprintf(stderr, "R2U2 v%d.%d.%d\n", \
        R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR, R2U2_C_VERSION_PATCH)
#define PRINT_USAGE() fprintf(stderr, "Usage: %s %s", argv[0], help)
const char *help = "<configuration> [trace]\n"
                   "\tconfiguration: path to monitor configuration binary\n"
                   "\ttrace: optional path to input CSV\n";

// Create CSV reader and monitor with default extents using macro
r2u2_csv_reader_t r2u2_csv_reader = {0};

// Contract status reporting, if enabled
#if R2U2_TL_Contract_Status
r2u2_contract_status_reporter_t r2u2_contact_status = {0};
r2u2_status_t contract_status_callback(r2u2_mltl_instruction_t inst, r2u2_verdict *res);
#endif

int main(int argc, char const *argv[]) {

  r2u2_status_t err_cond;
  int spec_file = -1;
  struct stat fd_stat;
  // TODO(bckempa): fstat size is off_t, but we need size_t for mmap
  //                convert and check for overflow on downcast

  // TODO(bckempa): Move this somewhere more visible
  #if R2U2_DEBUG
    r2u2_debug_fptr = stderr;
  #endif

  // Arg Parsing - for now just check for the correct number and look for flags
  //               short-circuiting helps avoid unnecessary checks here
  if ((argc < 2) || (argc > 3) ||
      (argv[1][0] == '-') || ((argc == 3) && (argv[2][0] == '-'))) {
      PRINT_VERSION();
      PRINT_USAGE();
      return 1;
  }

  uint8_t* spec;
  if (access(argv[1], F_OK) == 0) {
      // Use a raw open to get an unbuffered FD for mapping
      spec_file = open(argv[1], O_RDONLY, 0);
      if (spec_file == -1) {
        PRINT_USAGE();
        perror("Error opening specification file");
        return 1;
      }
      // Get file size for the mmap (using generic buffer size didn't work)
      if( fstat( spec_file, &fd_stat ) != 0 ) {
        PRINT_USAGE();
        perror("Error reading specification file");
        return 1;
      }
      // map read-only mirror of the file to memory - great for execution perf
      spec = mmap(NULL, (size_t)fd_stat.st_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, spec_file, 0);
      if (spec == MAP_FAILED) {
        PRINT_USAGE();
        perror("Error memory mapping specification file");
        return 1;
      }
      // File descriptor is not needed after mmap completes
      if (close(spec_file) != 0) {
        // This isn't a fatal error, just warn
        perror("Spec file did not close cleanly");
      }
  } else {
      PRINT_USAGE();
      perror("Cannot access specification file");
      return 1;
  }

  // Configure R2U2 monitor
  r2u2_monitor_t r2u2_monitor = R2U2_DEFAULT_MONITOR;
  r2u2_update_binary_file(spec, &r2u2_monitor);

  // Open output File
  r2u2_monitor.out_file = stdout;
  if(r2u2_monitor.out_file == NULL) {
    perror("Cannot open output log");
    return 1;
  if (munmap(spec, (size_t)fd_stat.st_size) != 0) {
    perror("Spec memory mapping did not close cleanly");
  }

  // Configure contract status reporting, if enabled
  #if R2U2_TL_Contract_Status
    r2u2_contact_status.out_file = r2u2_monitor.out_file;
    r2u2_contract_status_load_mapping(&r2u2_contact_status, &r2u2_monitor);
    r2u2_monitor.out_func = contract_status_callback;
  #endif

  // Select CSV reader input file
  if (argc > 2) {
    // The trace file was specified
    if (access(argv[2], F_OK) == 0) {
      r2u2_csv_reader.input_file = fopen(argv[2], "r");
      if (r2u2_csv_reader.input_file == NULL) {
        PRINT_USAGE();
        perror("Error opening trace file");
        return 1;
      }
    } else {
        PRINT_USAGE();
        perror("Cannot access trace file");
        return 1;
    }
  } else {
    // Trace file not specified, use stdin
    r2u2_csv_reader.input_file = stdin;
  }
  // Debug assert - input_file != Null

  // CSV Load Destination
  // To support operations without a front-end, check if the first instruction
  // is to the TL engine and if so, load signals direct to the atomic buffer.
  // This is a stronger assumption than the underlying engines make but is only
  // present in this reference monitor implementation.
  //
  // NOTE: This check will not behave properly if configuration is prepended
  // rather than appended to the instruction memory
  r2u2_status_t (*csv_load_func)(r2u2_csv_reader_t*, r2u2_monitor_t*);
  if (r2u2_monitor.bz_program_count.max_program_count == 0) {
    csv_load_func = &r2u2_csv_load_next_atomics;
  } else {
    csv_load_func = &r2u2_csv_load_next_signals;
  }

  // Main processing loop
  do {
    err_cond = (*csv_load_func)(&r2u2_csv_reader, &r2u2_monitor);

    if ((err_cond != R2U2_OK)) break;

  } while (err_cond == R2U2_OK);
      err_cond = r2u2_monitor_step(&r2u2_monitor);

  if (err_cond == R2U2_END_OF_TRACE) {
    // Traces are allowed to end, exit cleanly
    err_cond = R2U2_OK;
  }

  // Cleanup
  if (fclose(r2u2_monitor.out_file) != 0) {
    // We didn't close the output file sucessfully
    // handling this is out of scope but we should notify the user
    perror("Output file did not close cleanly");
    // We don't want to clober what is probably a more interesting error cond
    // so don't modify err_cond or return non-zero here, just fall though
    // TODO(bckempa): We could overcomplicate this by setting err_cond
    //                if and only if it is zero
  }

  if (munmap(r2u2_monitor.instruction_mem, (size_t)fd_stat.st_size) != 0) {
    perror("Spec memory mapping did not close cleanly");
  }

  // if (err_cond != R2U2_OK) {
  //   /* Prints R2U2 Status string if built with debugging enabled */
  //   r2u2_debug_fptr = stderr;
  //   R2U2_DEBUG_PRINT("%s\n", r2u2_status_string(err_cond));
  // }

  return (int) err_cond;
}

#if R2U2_TL_Contract_Status
r2u2_status_t contract_status_callback(r2u2_instruction_t inst, r2u2_verdict *res) {
  // Curry `r2u2_contract_status_report` with a reference to the r2u2_contact_status
  // struct for use by the montior output callback interface
  return r2u2_contract_status_report(&r2u2_contact_status, &inst, res);
}
#endif
