#include "r2u2.h"
// We use a config flag and therefore must include the toplevel header first

#include "csv_trace.h"

r2u2_status_t r2u2_csv_load_next_atomics(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor) {

  char *signal;
  // Since this can store a pointer, it must be able to store an index
  uintptr_t i;

  // Read in next line of trace to internal buffer for processing
  if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;

  // Skip header row, if it exists - note we only check for this on the first line
  if (monitor->time_stamp == 0 && csv_reader->in_buf[0] == '#') {
    if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;
  }

  for(i = 0, signal = strtok(csv_reader->in_buf, ",\n"); signal; i++, signal = strtok(NULL, ",\n")) {
    // TODO(bckempa): What should the behavior be if the value isn't 1 or 0?

    //if the term starts with an '@' then store it in the monitor's time_stamp
    if (signal[0] == '@'){
      if( sscanf(signal+1,"%u", &monitor->time_stamp) != 1 ) return R2U2_END_OF_TRACE;
      R2U2_DEBUG_PRINT("Event: @%u\n",monitor->time_stamp);
      i--;
      continue; 
    }

    r2u2_int i1;
    if(sscanf(signal, "%d", &i1) != 1) return R2U2_END_OF_TRACE;
    else ((*(monitor->atomic_buffer))[i]) = (r2u2_bool)i1;
  }

  return R2U2_OK;
}

r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t *csv_reader, r2u2_monitor_t *monitor) {
  printf("Load next signals\n");
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

      //if the term starts with an '@' then store it in the monitor's time_stamp
      if (signal[0] == '@'){
        char *timechar = signal+1;
        uint32_t time_signature;
        if(sscanf(timechar,"%u",&time_signature) != 1 ) return R2U2_END_OF_TRACE;
        (monitor->time_stamp) = time_signature;
        R2U2_DEBUG_PRINT("Event: %u\n",monitor->time_stamp);
        continue; 
      }
      (*(monitor->signal_vector))[i] = signal;
    }

    #endif

  return R2U2_OK;
}
