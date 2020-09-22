#ifndef AT_INSTRUCTION_H
#define AT_INSTRUCTION_H

#include "filters/filter_movavg.h"

typedef enum {
	EQ  = 0b000,
	LT  = 0b001,
	LEQ = 0b010,
	GT  = 0b011,
	GEQ = 0b100
} comparison_t;

typedef enum {
	OP_ABS_DIFF_ANGLE = 0b000,
	OP_MOVAVG         = 0b001,
	OP_RATE           = 0b010,
	OP_BOOL           = 0b011,
	OP_INT            = 0b100,
	OP_DOUBLE         = 0b101
} at_opcode_t;

typedef union {
	uint8_t b;
	int32_t i;
	double d;
} type_t;

typedef union {
	double diff_angle;	/* abs_diff_angle filter */
	double *prev;		/* rate filter */
	movAvg_t *movavg;	/* movavg filter */
} filt_data_struct_t;

typedef struct {
	comparison_t comp;
	at_opcode_t opcode;
	uint8_t sig_addr;
	uint8_t atom_addr;
	type_t comp_const;
	filt_data_struct_t filt_data_struct;
} at_instruction_t;

#endif
