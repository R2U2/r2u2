#ifndef AT_INSTRUCTION_H
#define AT_INSTRUCTION_H

#include "filters/filter_movavg.h"

typedef enum {
	GT  = 0b001,
	LT  = 0b010,
	EQ  = 0b011,
	GEQ = 0b100,
	LEQ = 0b101
} comparison_t;

typedef enum {
	OP_BOOL           = 0b0001,
	OP_INT            = 0b0010,
	OP_DOUBLE         = 0b0011,
	OP_RATE           = 0b0100,
	OP_ABS_DIFF_ANGLE = 0b0101,
	OP_MOVAVG         = 0b0110
} at_filter_t;

typedef union {
	uint32_t b;
	int32_t i;
	double d;
} type_t;

typedef union {
	double diff_angle;	/* abs_diff_angle filter */
	double prev;		/* rate filter */
	movAvg_t movavg;	/* movavg filter */
} filt_data_struct_t;

typedef struct {
	comparison_t comp;
	at_filter_t filter;
	uint8_t sig_addr;
	double arg;
	uint8_t atom_addr;
	type_t comp_const;
	filt_data_struct_t filt_data_struct;
} at_instruction_t;

#endif
