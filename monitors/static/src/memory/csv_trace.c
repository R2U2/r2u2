#include "r2u2.h"
// We use a config flag and therefore must include the toplevel header first

#include "csv_trace.h"

r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor) {

  char *signal;
  // Since this can store a pointer, it must be able to store an index
  uintptr_t i;

  // Read in next line of trace to internal buffer for processing
  if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;

    // Skip header row, if it exists - note we only check for this on the first line
    if (monitor->time_stamp == 0 && csv_reader->in_buf[0] == '#') {
      if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;
    }

    #if R2U2_CSV_Header_Mapping

    // TODO(bckempa): Port header mapping code
    for(i = 0, signal = strtok(csv_reader->in_buf, ",\n"); signal; i++, signal = strtok(NULL, ",\n")) {
      // Follow the pointer to the signal vector, then assign the ith element
      // Note this is a pointer into the r2u2_csv_reader_t in_buf which must
      // stay in place while the signal vector is live
      (*(monitor->signal_vector))[i] = signal;
    }

    #else

    for(i = 0, signal = strtok(csv_reader->in_buf, ",\n"); signal; i++, signal = strtok(NULL, ",\n")) {
      // Follow the pointer to the signal vector, then assign the ith element
      // Note this is a pointer into the r2u2_csv_reader_t in_buf which must
      // stay in place while the signal vector is live
      (*(monitor->signal_vector))[i] = signal;
    }

    #endif

  return R2U2_OK;
}
