/*=======================================================================================
** File Name:  TL_observers.h
**
** Title:  Definition and data types for the TL engines
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
**
** Purpose:
**	Definition and data types for the TL engines
**
**
** Limitations, Assumptions, External Events, and Notes:
**	NA
**
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**
**=====================================================================================*/

#ifndef TL_OBSERVERS_H
#define TL_OBSERVERS_H

#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>

#include "R2U2Config.h"
//
// 5 bit opcodes
//
typedef enum {
	OP_START		= 0b01011,
	OP_END			= 0b01100,
	OP_END_SEQUENCE	= 0b11111,
	OP_NOP			= 0b11110,
	OP_NOT			= 0b00011,

	OP_AND			= 0b00100,
	OP_IMPL			= 0b00110,

	OP_FT_NOT		= 0b10100,
	OP_FT_AND		= 0b10101,
	OP_FT_IMPL		= 0b11011,

	OP_OR			= 0b00101,
	OP_EQUIVALENT	= 0b00111,

	// past time operations
	OP_PT_YESTERDAY			= 0b01000,
	OP_PT_ONCE			= 0b01001,
	OP_PT_HISTORICALLY			= 0b01010,
	OP_PT_SINCE			= 0b01110,

	// metric past and future time operations
	// intervals
	OP_PT_HISTORICALLY_INTERVAL		= 0b10010,
	OP_PT_ONCE_INTERVAL		= 0b10000,
	OP_PT_SINCE_INTERVAL		= 0b10011,

	OP_FT_GLOBALLY_INTERVAL		= 0b10111,
	OP_FT_FJ		= 0b11001,
	OP_FT_UNTIL_INTERVAL		= 0b11010,
	OP_FT_LOD		= 0b11100,

	// metric past and future time operations
	// end time points
	OP_PT_HISTORICALLY_TIMEPOINT		= 0b10001,
	OP_PT_ONCE_TIMEPOINT		= 0b01111,

	OP_FT_GLOBALLY_TIMEPOINT		= 0b10110,
	OP_FT_EVENTUALLY_TIMEPOINT		= 0b11000
} opcode_t;

//
// operand types
//
typedef enum {
	direct 		= 0b01,
	atomic 		= 0b00,
	subformula 	= 0b10,
	not_set 	= 0b11
} operand_type_t;

//
// data structure for operand
// not packed
//
typedef struct {
	operand_type_t	opnd_type;
	uint8_t	value;
} operand_t;

//
// data structure for instruction
// not packed
// instruction format for packed representation:
//  OPC:5 op1:10 op2:10 intvl:8 scratch:7
//
typedef struct {
	opcode_t	opcode;
	operand_t	op1;
	operand_t	op2;
	uint8_t	adr_interval;
	uint8_t	scratch;
} instruction_t;

// data structure for address info of SCQ
typedef struct {
	uint16_t start_addr;
	uint16_t end_addr;
}	addr_SCQ_t;

//
// data type for
// buffer head or tail distinction
//
typedef enum {
	dontcare = 0,
	tail = 1,
	head = 2
} head_or_tail_t;

//
// interval memory for intervals (not packed)
// LB:16 UB:16
//
typedef uint16_t interval_bound_t;
typedef struct {
	interval_bound_t	lb;
	interval_bound_t	ub;
} interval_t;

//
// data type for edge detection
//
typedef enum {
	none = 0,
	falling,
	rising
} edge_t;

//
// atomic inputs, Vector of Booleans
//
typedef bool atomics_vector_t[N_ATOMICS];

//
// instruction memory
//
typedef instruction_t instruction_mem_t[N_INSTRUCTIONS];

typedef interval_t interval_mem_t[N_INSTRUCTIONS];

typedef addr_SCQ_t addr_SCQ_map_t[N_INSTRUCTIONS];

//
// PT results vector
//
typedef bool results_pt_t[N_INSTRUCTIONS];

//
// Async queue array
typedef timestamp_t results_rising_pt_t[N_INSTRUCTIONS];

#if R2U2_TL_Formula_Names
typedef char* aux_str_map_t[N_INSTRUCTIONS];
typedef char aux_str_arena_t[L_AUX_STRINGS];
#endif

#if R2U2_TL_Contract_Status
typedef char* aux_con_map_t[N_INSTRUCTIONS];
typedef char aux_con_arena_t[L_AUX_STRINGS];
typedef size_t aux_con_forms_t[N_INSTRUCTIONS];
typedef size_t aux_con_max_t;
#endif

#ifdef __cplusplus
extern "C" {
#endif
//---------------------------------------------
// externals
//---------------------------------------------
extern timestamp_t			t_now;

extern int					r2u2_errno;

extern atomics_vector_t		atomics_vector;
extern atomics_vector_t		atomics_vector_prev;

extern instruction_mem_t	instruction_mem_ft;
extern instruction_mem_t	instruction_mem_pt;

extern interval_mem_t		interval_mem_pt;
extern interval_mem_t  		interval_mem_ft;

extern addr_SCQ_map_t		addr_SCQ_map_ft;

extern results_pt_t			results_pt;
extern results_pt_t			results_pt_prev;

extern results_rising_pt_t 	results_pt_rising;

#if R2U2_TL_Formula_Names
extern aux_str_map_t		aux_str_map;
extern aux_str_arena_t		aux_str_arena;
#endif

#if R2U2_TL_Contract_Status
extern aux_con_map_t 		aux_con_map;
extern aux_con_arena_t 		aux_con_arena;
extern aux_con_forms_t 		aux_con_forms;
extern aux_con_max_t		aux_con_max;
#endif

/* For no file handling option */
extern char *ptm_bin;
extern char *pti_bin;
extern char *ftscq_bin;
extern char *ftm_bin;
extern char *fti_bin;

//---------------------------------------------
// functions
//---------------------------------------------
void TL_config(char*, char*, char*, char*, char*);
void TL_aux_config(char*);

int TL_init();

int TL_update(FILE *fp);
int TL_update_pt(FILE *fp);
int TL_update_ft(FILE *fp);

#ifdef __cplusplus
}
#endif

#endif
