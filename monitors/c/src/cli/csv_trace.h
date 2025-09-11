#ifndef R2U2_MEMORY_CSV_TRACE_H
#define R2U2_MEMORY_CSV_TRACE_H

#include "internals/errors.h"
#include "memory/monitor.h"

typedef struct {
  FILE *input_file;
  char in_buf[BUFSIZ];
} r2u2_csv_reader_t;

r2u2_status_t r2u2_csv_load_next_atomics(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor);
r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor);

#endif /* R2U2_MEMORY_CSV_TRACE_H */
