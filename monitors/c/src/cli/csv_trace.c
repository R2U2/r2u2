#include "internals/config.h"
#include "csv_trace.h"
#include "r2u2.h"
#include "internals/debug.h"
#include <stdio.h>
#include <string.h>

r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t* csv_reader, r2u2_monitor_t* monitor) {
  char* signal;
  uintptr_t i;

  // Read in next line of trace to internal buffer for processing
  if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;

  // Skip header row, if it exists - note we only check for this on the first line
  if (monitor->time_stamp == 0 && csv_reader->in_buf[0] == '#') {
    if(fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) return R2U2_END_OF_TRACE;
  }
  
  for(i = 0, signal = strtok(csv_reader->in_buf, ",\n"); signal; i++, signal = strtok(NULL, ",\n")) {
    // Follow the pointer to the signal vector, then assign the ith element
    // Note this is a pointer into the r2u2_csv_reader_t in_buf which must
    // stay in place while the signal vector is live

    //if the term starts with an '@' then store it in the monitor's time_stamp
    if (i == 0 && signal[0] == '@'){
      char* temp_var;
      char* timechar = strtok_r(signal+1, " ", &temp_var);
      uint32_t time_signature;
      if(sscanf(timechar,"%u",&time_signature) != 1 ) return R2U2_END_OF_TRACE;
      (monitor->time_stamp) = time_signature;
      R2U2_DEBUG_PRINT("Event: %u\n",monitor->time_stamp);
      signal = strtok_r(NULL, " ", &temp_var);
    }
    r2u2_load_string_signal(monitor, i, signal);
  }

  return R2U2_OK;
}
