#ifndef R2U2_CLI_CSV_TRACE_H
#define R2U2_CLI_CSV_TRACE_H

#include "internals/errors.h"
#include "memory/monitor.h"

typedef struct {
  FILE* input_file;
  char in_buf[BUFSIZ];
} r2u2_csv_reader_t;

/// @brief      Sets the R2U2 monitor's signal_vector (or atomic_vector if booleanizer is not enabled)
///             based on next line in CSV
/// @param[in]  csv_reader  Pointer to r2u2_csv_reader_t
/// @param[in]  monitor  Pointer to (configured) R2U2 monitor
/// @return     r2u2_status_t
r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t* csv_reader, r2u2_monitor_t* monitor);

#endif /* R2U2_CLI_CSV_TRACE_H */
