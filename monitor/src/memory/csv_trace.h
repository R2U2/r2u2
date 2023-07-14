#ifndef R2U2_MEMORY_CSV_TRACE_H
#define R2U2_MEMORY_CSV_TRACE_H

#include <stdio.h>
#include <string.h>

#include "internals/errors.h"
#include "memory/monitor.h"

// This could arguably have the functions split out as an engine, however they
// are never called by instruction dispatch and may allocate memory so we'll
// contain them here

typedef struct {
  FILE *input_file;

  char in_buf[BUFSIZ]; // TODO(bckempa): LINE_MAX instead? PATH_MAX?

} r2u2_csv_reader_t;

r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor);

#endif /* R2U2_MEMORY_CSV_TRACE_H */
