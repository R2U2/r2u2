#include "r2u2.h"

#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>

#include "internals/errors.h"
#include "memory/instruction.h"
#include "memory/csv_trace.h"

// TODO(bckempa): REMOVE when C2PO is ready
#include "tmp_spec.h"

// R2U2 Reference Implmentation
// Provides example of library usage and "offline" monitoring
//
//
#define PRINT_VERSION() fprintf(stderr, "R2U2 Version %d.%d.%d\n", \
        R2U2_C_VERSION_MAJOR, R2U2_C_VERSION_MINOR, R2U2_C_VERSION_PATCH)
#define PRINT_USAGE() fprintf(stderr, "Usage: %s %s", argv[0], help)
const char *help = "<configuration> [trace]\n"
                   "\tconfiguration: path to monitor configuration binary\n"
                   "\ttrace: optional path to input CSV\n";

// Create CSV reader and monitor with default extents using macro
r2u2_csv_reader_t r2u2_csv_reader = {0};
r2u2_monitor_t r2u2_monitor = R2U2_DEFAULT_MONITOR;

int main(int argc, char const *argv[]) {

  r2u2_status_t err_cond;
  #if 0 // TODO(bckempa): ENABLE when C2PO is ready
  int spec_file = -1;
  struct stat fd_stat;
  #endif
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

  // Load monitor
  // R2U2's binary loader takes a pointer to the raw bytes and expects the
  // caller to handle anything more advanced like file I/O which might
  // allocate depending on the stdlib impl (e.g., grabs a buffer) so we mmap
  // the file before passing the ptr
  //
  // Note: We're being lazy and using the R2U2_DEFAULT_MONITOR macro which
  // allocates a buffer for the instuction mem, but we replace it with the file
  #if 0 // TODO(bckempa): ENABLE when C2PO is ready - Disable memory-mapped outside spec file while using embedded Spec
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
      r2u2_monitor.instruction_mem = mmap(NULL, fd_stat.st_size, PROT_READ, MAP_PRIVATE, spec_file, 0);
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


  // Reset monitor and build instuction table from spec binary
  r2u2_init(&r2u2_monitor);
  #endif

  #if 1 // TODO(bckempa): REMOVE when C2PO is ready - load embedded spec
    r2u2_monitor_clock_reset(&r2u2_monitor);
    load_temp_spec(&r2u2_monitor);
    config_temp_spec(&r2u2_monitor);
  #endif

  // Open output File
  // TODO(bckempa): Formula set name or time? Take an optional path?
  r2u2_monitor.out_file = fopen("./R2U2.log", "w+");
  if(r2u2_monitor.out_file == NULL) {
    perror("Cannot open output log");
    return 1;
  }

  // Select CSV reader input file
  if(argc > 2) {
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

  #if 0 // TODO(bckempa): ENABLE when C2PO is ready
  if (munmap(r2u2_monitor.instruction_mem, fd_stat.st_size) != 0) {
    perror("Spec memory mapping did not close cleanly");
  }
  #endif

  // if (err_cond != R2U2_OK) {
  //   /* Prints R2U2 Status string if built with debugging enabled */
  //   r2u2_debug_fptr = stderr;
  //   R2U2_DEBUG_PRINT("%s\n", r2u2_status_string(err_cond));
  // }

  return (int) err_cond;
}
