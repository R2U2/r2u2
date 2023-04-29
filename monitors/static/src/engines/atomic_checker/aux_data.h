#ifndef AUX_DATA_H
#define AUX_DATA_H

#include "internals/types.h"

#include "extra_filters/filter_movavg.h"

typedef union {
    r2u2_float prev;        /* rate filter */
    // TODO(bckempa): the movAvg type is waaaaaay bigger than anything else....
    movavg_t movavg;       /* movavg filter */
} r2u2_at_filter_aux_data_t;

typedef r2u2_at_filter_aux_data_t (r2u2_at_filter_aux_data_buffer_t)[];

#endif
