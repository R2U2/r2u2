#include "internals/config.h"
#include "csv_trace.h"
#include "r2u2.h"
#include "internals/debug.h"
#include <ctype.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static r2u2_status_t r2u2_csv_read_line(r2u2_csv_reader_t* csv_reader) {
  if (fgets(csv_reader->in_buf, sizeof(csv_reader->in_buf), csv_reader->input_file) == NULL) {
    if (ferror(csv_reader->input_file)) {
      fprintf(stderr, "Invalid CSV: trace read failed\n");
      return R2U2_ERR_OTHER;
    }
    return R2U2_END_OF_TRACE;
  }
  if (strchr(csv_reader->in_buf, '\n') == NULL && !feof(csv_reader->input_file)) {
    // A record that exactly fills the buffer can end immediately at EOF,
    // or have only the terminating newline remaining in the input stream.
    int next_char = fgetc(csv_reader->input_file);
    if (next_char != '\n' && !(next_char == EOF && !ferror(csv_reader->input_file))) {
      if (ferror(csv_reader->input_file)) {
        fprintf(stderr, "Invalid CSV: trace read failed\n");
        return R2U2_ERR_OTHER;
      }
      fprintf(stderr, "Invalid CSV: record exceeds input buffer\n");
      return R2U2_ERR_OTHER;
    }
  }
  // CR is only a line terminator, never a signal-field separator.
  char* carriage_return = strchr(csv_reader->in_buf, '\r');
  if (carriage_return != NULL && carriage_return[1] != '\n' && carriage_return[1] != '\0') {
    fprintf(stderr, "Invalid CSV: carriage return inside a signal\n");
    return R2U2_ERR_OTHER;
  }
  return R2U2_OK;
}

// Count comma-separated fields before strtok collapses empty fields. This
// also checks that the first and last field, and every field between them,
// are present. Do not modify the buffer: the monitor keeps pointers into it.
static r2u2_status_t r2u2_csv_count_fields(const char* row, uintptr_t* count) {
  uintptr_t fields = 0;
  bool has_value = false;

  for (const char* cursor = row; *cursor != '\0' && *cursor != '\r' && *cursor != '\n'; cursor++) {
    if (*cursor == ',') {
      if (!has_value) {
        fprintf(stderr, "Invalid CSV: empty column\n");
        return R2U2_ERR_OTHER;
      }
      fields++;
      has_value = false;
    } else if (!isspace((unsigned char)*cursor)) {
      has_value = true;
    }
  }
  if (!has_value) {
    fprintf(stderr, "Invalid CSV: empty column\n");
    return R2U2_ERR_OTHER;
  }
  *count = fields + 1;
  return R2U2_OK;
}

r2u2_status_t r2u2_csv_load_next_signals(r2u2_csv_reader_t* csv_reader, r2u2_monitor_t* monitor) {
  char* signal;
  uintptr_t i;
  uintptr_t columns;
  r2u2_status_t read_status;
  const uintptr_t capacity = monitor->bz_program_count.max_program_count == 0
      ? R2U2_MAX_ATOMICS : R2U2_MAX_SIGNALS;

  // Read in next line of trace to internal buffer for processing
  read_status = r2u2_csv_read_line(csv_reader);
  if (read_status != R2U2_OK) return read_status;

  // Skip header row, if it exists - note we only check for this on the first line
  if (monitor->time_stamp == 0 && csv_reader->in_buf[0] == '#') {
    const char* header = csv_reader->in_buf + 1;
    while (*header == ' ' || *header == '\t') header++;
    if (r2u2_csv_count_fields(header, &columns) != R2U2_OK) return R2U2_ERR_OTHER;
    if (columns > capacity) {
      fprintf(stderr, "Invalid CSV: header exceeds configured capacity\n");
      return R2U2_ERR_OTHER;
    }
    csv_reader->expected_columns = columns;
    read_status = r2u2_csv_read_line(csv_reader);
    if (read_status != R2U2_OK) return read_status;
  }

  if (csv_reader->expected_columns != 0) {
    if (r2u2_csv_count_fields(csv_reader->in_buf, &columns) != R2U2_OK)
      return R2U2_ERR_OTHER;
    if (columns != csv_reader->expected_columns) {
      fprintf(stderr, "Invalid CSV: row width does not match header\n");
      return R2U2_ERR_OTHER;
    }
  }
  
  for(i = 0, signal = strtok(csv_reader->in_buf, ",\r\n"); signal; i++, signal = strtok(NULL, ",\r\n")) {
    if (i >= capacity) {
      fprintf(stderr, "Invalid CSV: input signals exceed configured capacity\n");
      return R2U2_ERR_OTHER;
    }
    // Follow the pointer to the signal vector, then assign the ith element
    // Note this is a pointer into the r2u2_csv_reader_t in_buf which must
    // stay in place while the signal vector is live

    // If the first term starts with '@', read its timestamp and first signal.
    if (i == 0 && signal[0] == '@') {
      char* temp_var;
      char* timechar = strtok_r(signal+1, " ", &temp_var);
      char* time_end;
      unsigned long time_value;
      if (timechar == NULL || timechar[0] == '-') {
        fprintf(stderr, "Invalid CSV: malformed timestamp\n");
        return R2U2_ERR_OTHER;
      }
      errno = 0;
      time_value = strtoul(timechar, &time_end, 10);
      if (errno == ERANGE || time_end == timechar || *time_end != '\0' ||
          time_value > R2U2_TNT_TIME) {
        fprintf(stderr, "Invalid CSV: malformed or out-of-range timestamp\n");
        return R2U2_ERR_OTHER;
      }
      signal = strtok_r(NULL, " ", &temp_var);
      if (signal == NULL) {
        fprintf(stderr, "Invalid CSV: missing signal after timestamp\n");
        return R2U2_ERR_OTHER;
      }
      monitor->time_stamp = (r2u2_time) time_value;
      R2U2_DEBUG_PRINT("Event: %u\n", monitor->time_stamp);
    }
    r2u2_load_string_signal(monitor, i, signal);
  }

  return R2U2_OK;
}
