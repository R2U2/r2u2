#include "r2u2.h"

#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>

#include "internals/errors.h"
#include "memory/instruction.h"
#include "memory/csv_trace.h"
#if R2U2_TL_Contract_Status
#include "memory/contract_status.h"
#endif


// R2U2 Reference Implementation
// Provides example of library usage and "offline" monitoring
//
//
#define PRINT_VERSION() fprintf(stderr, "R2U2 Version %d.%d.%d\n", \
        R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR, R2U2_C_VERSION_PATCH)
#define PRINT_USAGE() fprintf(stderr, "Usage: %s %s", argv[0], help)
const char *help = "<configuration> [trace] [-a --as_atomics]\n"
                   "\tconfiguration: path to monitor configuration binary\n"
                   "\ttrace: optional path to input CSV\n"
                   "\t-a --as_atomics: enable loading CSV values directly as atomics\n";

// Create CSV reader and monitor with default extents using macro
r2u2_csv_reader_t r2u2_csv_reader = {0};
r2u2_monitor_t r2u2_monitor = R2U2_DEFAULT_MONITOR;

// Create Queue memory arena
uint8_t *arena = &(uint8_t [R2U2_DUOQ_BYTES]){0};

// Contract status reporting, if enabled
#if R2U2_TL_Contract_Status
r2u2_contract_status_reporter_t r2u2_contact_status = {0};
r2u2_status_t contract_status_callback(r2u2_instruction_t inst, r2u2_verdict *res);
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
  if ((argc < 2) || (argc > 4) ||
      (argv[1][0] == '-') || ((argc > 2) && (argv[2][0] == '-'))) {
      PRINT_VERSION();
      PRINT_USAGE();
      return 1;
  }

  // Load monitor
  // R2U2's binary loader takes a pointer to the raw bytes and expects the
  // caller to handle anything more advanced like file I/O which might
  // allocate depending on the stdlib impl (e.g., grabs a buffer) so we mmap
  // the file before passing the ptr
  //
  // Note: We're being lazy and using the R2U2_DEFAULT_MONITOR macro which
  // allocates a buffer for the instuction mem, but we replace it with the file
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
      r2u2_monitor.instruction_mem = mmap(NULL, (size_t)fd_stat.st_size, PROT_READ, MAP_PRIVATE, spec_file, 0);
      if (r2u2_monitor.instruction_mem == MAP_FAILED) {
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

  // Connect monitor to queue memory arena
  r2u2_monitor.duo_queue_mem.blocks = (r2u2_duoq_control_block_t*) arena;
  r2u2_monitor.duo_queue_mem.queues = (r2u2_tnt_t*) (arena + R2U2_DUOQ_BYTES - 4);

  // Reset monitor and build instuction table from spec binary
  r2u2_init(&r2u2_monitor);

  // Open output File
  r2u2_monitor.out_file = stdout;
  if(r2u2_monitor.out_file == NULL) {
    perror("Cannot open output log");
    return 1;
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

  // Directly load CSV values as atomics
  if (argc > 3) {
    // -a/--as_atomics was specified
    if (strcmp(argv[2], "-a") || strcmp(argv[2], "--as_atomics")) {
      r2u2_csv_reader.as_atomics = true;
    } else {
        PRINT_USAGE();
        perror("Cannot access trace file");
        return 1;
    }
  } else {
    r2u2_csv_reader.as_atomics = false;
  }

  // Main processing loop
  do {
    err_cond = r2u2_csv_load_next_signals(&r2u2_csv_reader, &r2u2_monitor);
    if ((err_cond != R2U2_OK)) break;

    err_cond = r2u2_tic(&r2u2_monitor);
  } while (err_cond == R2U2_OK);

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
