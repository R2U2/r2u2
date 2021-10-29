#ifndef AT_INSTRUCTION_H
#define AT_INSTRUCTION_H

#include <stdbool.h>

#ifdef R2U2_AT_ExtraFilters
#include "extra_filters/filter_movavg.h"
#endif

typedef enum {
	EQ  = 0b000,
	NEQ = 0b001,
	LT  = 0b010,
	LEQ = 0b011,
	GT  = 0b100,
	GEQ = 0b101
} conditional_t;

typedef enum {
	OP_BOOL           = 0b0001,
	OP_INT            = 0b0010,
	OP_DOUBLE         = 0b0011,
	#ifdef R2U2_AT_ExtraFilters
	OP_RATE           = 0b0100,
	OP_ABS_DIFF_ANGLE = 0b0101,
	OP_MOVAVG         = 0b0110,
	OP_EXACTLY_ONE_OF = 0b0111 // NOTE: sig_addr stores set_addr
	#endif
} at_filter_t;

typedef union {
	int8_t s;
	bool b;
	int32_t i;
	double d;
} type_t;


#ifdef R2U2_AT_ExtraFilters
typedef union {
	double diff_angle;	/* abs_diff_angle filter */
	double prev;				/* rate filter */
	movAvg_t *movavg;		/* movavg filter */
} filt_data_struct_t;
#endif


typedef struct {
	conditional_t cond;
	at_filter_t filter;
	uint8_t sig_addr;
	uint8_t atom_addr;
	bool comp_is_sig;
	type_t comp;

#ifdef R2U2_AT_ExtraFilters
	filt_data_struct_t filt_data_struct;
#endif
} at_instruction_t;

#endif
