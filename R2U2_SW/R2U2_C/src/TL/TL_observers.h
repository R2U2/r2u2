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

#include "R2U2Config.h"
	//
	// 5 bit opcodes
	//
typedef enum {
	OP_START		= 0b01011,
	OP_END			= 0b01100,
	OP_END_SEQUENCE		= 0b11111,
	OP_NOP			= 0b11110,
	OP_NOT			= 0b00011,

	OP_AND			= 0b00100,
	OP_IMPL			= 0b00110,

	OP_FT_NOT		= 0b10100,
	OP_FT_AND		= 0b10101,
	OP_FT_IMPL	= 0b11011,

	OP_OR			= 0b00101,
	OP_EQUIVALENT		= 0b00111,

	// past time operations
	OP_PT_Y			= 0b01000,
	OP_PT_O			= 0b01001,
	OP_PT_H			= 0b01010,
	OP_PT_S			= 0b01110,

	// metric past and future time operations
	// intervals
	OP_PT_HJ		= 0b10010,
	OP_PT_OJ		= 0b10000,
	OP_PT_SJ		= 0b10011,

	OP_FT_GJ		= 0b10111,
	OP_FT_FJ		= 0b11001,
	OP_FT_UJ		= 0b11010,
	OP_FT_LOD		= 0b11100,

	// metric past and future time operations
	// end time points
	OP_PT_HT		= 0b10001,
	OP_PT_OT		= 0b01111,

	OP_FT_GT		= 0b10110,
	OP_FT_FT		= 0b11000
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
	unsigned char	value;
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
	unsigned char	adr_interval;
	unsigned char	scratch;
	} instruction_t;

// data structure for address info of SCQ
typedef struct {
	unsigned int start_addr;
	unsigned int end_addr;
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
typedef struct {
	unsigned int	lb;
	unsigned int	ub;
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
//typedef  results_a_ft_t[N_INSTRUCTIONS];
typedef int results_rising_pt_t[N_INSTRUCTIONS];

#ifdef __cplusplus
extern "C" {
#endif
//---------------------------------------------
// externals
//---------------------------------------------
extern int			t_now;

extern int			r2u2_errno;
extern int			max_time_horizon;

extern atomics_vector_t		atomics_vector;
extern atomics_vector_t		atomics_vector_prev;

extern instruction_mem_t	instruction_mem_ft;
extern instruction_mem_t	instruction_mem_pt;

extern addr_SCQ_map_t	addr_SCQ_map_ft;

extern interval_t		interval_mem_pt[];
extern int			l_interval_mem_pt;

// extern interval_t		interval_mem_ft[];

extern interval_mem_t  interval_mem_ft;

extern results_pt_t		results_pt;
extern results_pt_t		results_pt_prev;

extern results_rising_pt_t results_pt_rising;


//async future time synchronization queues
//TODO to remove extern ft_sync_queue_t	results_a_ft_sync_q;

//---------------------------------------------
// functions
//---------------------------------------------
void TL_config(char*, char*, char*, char*, char*);

int TL_init();

int TL_update(FILE *fp);
int TL_update_pt(FILE *fp);
int TL_update_ft(FILE *fp);

#ifdef __cplusplus
}
#endif

#endif
