#include "internals/errors.h"
#include "r2u2.h"
#include "operations.h"
#include "compare.h"


// #include <stdio.h>
// #include <stdint.h>
// #include <stdbool.h>
// #include <float.h>

#if R2U2_AT_EXTRA_FILTERS
#include "extra_filters/filter_abs_diff_angle.h"
#include "extra_filters/filter_rate.h"
#include "extra_filters/filter_movavg.h"
#endif

#if R2U2_AT_Signal_Sets
#include "signal_set_filters/filter_exactly_one_of.h"
#include "signal_set_filters/filter_none_of.h"
#include "signal_set_filters/filter_all_of.h"
#endif

// #if R2U2_AT_EXTRA_FILTERS
r2u2_status_t op_abs_diff_angle(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    double signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%lf", &signal);
    r2u2_float diff_angle = (r2u2_float) abs_diff_angle(signal, instr->filter_arg.d);

    R2U2_DEBUG_PRINT("\tabs_diff_angle(s%d, %lf) = %lf\n", instr->sig_addr, instr->filter_arg.d, diff_angle);

    if (instr->comp_is_sig) {
        r2u2_float comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%lf", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](diff_angle, comp_sig, R2U2_FLOAT_EPSILON);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](diff_angle, instr->comparison.d, R2U2_FLOAT_EPSILON);
    }


    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}

r2u2_status_t op_movavg(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    int32_t signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%d", &signal);
    r2u2_float avg = filter_movavg_update_data(&((monitor->at_aux_buffer)[instr->aux_addr].movavg), instr->filter_arg.i, signal);

    R2U2_DEBUG_PRINT("\tmovavg(s%d, %d) = %lf\n", instr->sig_addr, instr->filter_arg.i, avg);

    if (instr->comp_is_sig) {
        r2u2_float comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%lf", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](avg, comp_sig, R2U2_FLOAT_EPSILON);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](avg, instr->comparison.d, R2U2_FLOAT_EPSILON);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}

r2u2_status_t op_rate(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    r2u2_float signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%lf", &signal);
    r2u2_float rate = filter_rate_update_data(signal, &(monitor->at_aux_buffer)[instr->aux_addr].prev);

    R2U2_DEBUG_PRINT("\trate(s%d) = %lf\n", instr->sig_addr, rate);

    if (instr->comp_is_sig) {
        r2u2_float comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%lf", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](rate, comp_sig, R2U2_FLOAT_EPSILON);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](rate, instr->comparison.d, R2U2_FLOAT_EPSILON);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}
// #endif

#if R2U2_AT_Signal_Sets
r2u2_status_t op_exactly_one_of(r2u2_at_instruction_t *instr) {
    uint8_t i, set_addr = instr->sig_addr;
    bool set[N_ATOMICS];

    for (i = 1; i <= *aux_signal_set_map[set_addr]; i++) {
        set[i-1] = (*(monitor->atomic_buffer)[0])[*(aux_signal_set_map[set_addr]+i)];
    }
    bool res = filter_exactly_one_of(set, *(aux_signal_set_map[set_addr]));

    if (instr->comp_is_sig) {
        bool comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%hhu", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, comp_sig);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, instr->comparison.b);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}


r2u2_status_t op_none_of(r2u2_at_instruction_t *instr) {
    uint8_t i, set_addr = instr->sig_addr;
    bool set[N_ATOMICS];

    for (i = 1; i <= *aux_signal_set_map[set_addr]; i++) {
        set[i-1] = (*(monitor->atomic_buffer)[0])[*(aux_signal_set_map[set_addr]+i)];
    }
    bool res = filter_none_of(set, *(aux_signal_set_map[set_addr]));

    if (instr->comp_is_sig) {
        bool comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%hhu", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, comp_sig);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, instr->comparison.b);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}


r2u2_status_t op_all_of(r2u2_at_instruction_t *instr) {
    uint8_t i, set_addr = instr->sig_addr;
    bool set[N_ATOMICS];

    for (i = 1; i <= *aux_signal_set_map[set_addr]; i++) {
        set[i-1] = (*(monitor->atomic_buffer)[0])[*(aux_signal_set_map[set_addr]+i)];
    }
    bool res = filter_all_of(set, *(aux_signal_set_map[set_addr]));

    if (instr->comp_is_sig) {
        bool comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%hhu", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, comp_sig);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](res, instr->comparison.b);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}
#endif


r2u2_status_t op_bool(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    r2u2_bool signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%hhu", &signal);

    R2U2_DEBUG_PRINT("\tbool(s%d) = %hhu\n", instr->sig_addr, signal);

    if (instr->comp_is_sig) {
        bool comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%hhu", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](signal, comp_sig);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](signal, instr->comparison.b);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}

r2u2_status_t op_int(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    int32_t signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%d", &signal);

    R2U2_DEBUG_PRINT("\tint(s%d) = %d\n", instr->sig_addr, signal);

    if (instr->comp_is_sig) {
        int32_t comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%d", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](signal, comp_sig);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_int[instr->conditional](signal, instr->comparison.i);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}

r2u2_status_t op_float(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    double signal;
    sscanf((*(monitor->signal_vector))[instr->sig_addr], "%lf", &signal);

    R2U2_DEBUG_PRINT("\tfloat(s%d) = %lf\n", instr->sig_addr, signal);

    if (instr->comp_is_sig) {
        double comp_sig;
        sscanf((*(monitor->signal_vector))[instr->comparison.s], "%lf", &comp_sig);
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](signal, comp_sig, R2U2_FLOAT_EPSILON);
    } else {
        (*(monitor->atomic_buffer)[0])[instr->atom_addr] =
            r2u2_at_compare_float[instr->conditional](signal, instr->comparison.d, R2U2_FLOAT_EPSILON);
    }

    R2U2_DEBUG_PRINT("\tResult: %hhu\n", (*(monitor->atomic_buffer)[0])[instr->atom_addr]);

    return R2U2_OK;
}

r2u2_status_t op_error(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {
    UNUSED(monitor);
    UNUSED(instr);
    // printf("Error: invalid opcode %d at addr %p\n", instr->filter, (void *) instr);
    return R2U2_INVALID_INST;
}

r2u2_status_t (*r2u2_at_decode[])(r2u2_monitor_t *, r2u2_at_instruction_t*) = { op_error,
    op_bool,
    op_int,
    op_float,
#if R2U2_AT_EXTRA_FILTERS
    op_rate,
    op_abs_diff_angle,
    op_movavg,
#else
    op_error,
    op_error,
    op_error,
#endif
#if R2U2_AT_Signal_Sets
    op_exactly_one_of,
    op_none_of,
    op_all_of,
#else
    op_error,
    op_error,
    op_error
#endif
};
