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


//------------------------------------------------------------------
// definition of OPCODE for PT and FT engines
// Note: only needed when the engines are initialized with
// binary code and not the C data structures in TL_formula.c, TL_formula_int.c
//------------------------------------------------------------------
	//
	// length of registers in bits
	//
#define L_OPC			5
#define L_OP			10
#define L_INTVL			8
#define L_PMEM			7
#define L_SCRATCH		7
#define L_TIMESTAMP		16

	//
	// length of instruction
	//
#define L_INSTRUCTION		(L_OPC+L_OP+L_OP+L_INTVL+L_SCRATCH)

	// for the file .ftscq
#define L_SCQ_ADDRESS 8


	//
	// length of registers in bits for mapping
	//
#define L_MAP_PTFT		1
#define L_MAP_VALUE		8
#define L_MAP_SCRATCH		7
#define L_MAP			(L_MAP_PTFT+L_MAP_VALUE+L_MAP_SCRATCH)

#define L_INTVL_TS		16
#define L_INTERVAL		32

	//
	// \infopcode_tty for rising-edge
	// must be larger than any timestamp
	//
#define TL_INF			32767*32767

	//
	// sizes of vectors and memories
	// Note: these sizes conform to the FPGA configuration
	//

	//
	// number of Boolean inputs
	//
#define N_ATOMICS		128

	//
	// maximum number of instructions
	//
#define N_INSTRUCTIONS		256

	//
	// number of MAP entries
	//
#define N_MAP			256

	//
	// maximal number of past time INTERVAL ENTRIES
	// this is equal to maximal number of pt temporal operators
	//
#define N_INTERVAL		128

	//
	// length of each individual ring buffer for box operators
	//
#define L_DOT_BUFFER		64

	//
	// total size of pt buffer pool
	// Note: For a total number of buffers used of N_BUF
	// it must hold:
	//  N_BUF * L_DOT_BUFFER < N_DOT_BUFFERS_TOTAL
	// This is checked in TL_init.c
	//
#define N_DOT_BUFFERS_TOTAL	4096

	//
	// maximal number of future time INTERVAL ENTRIES
	// this is equal to maximal number of ft temporal operators
	//
//#define N_FT_INTERVAL		128

	//
	// length of each individual synchronization 
	// ring buffer for ft operators
	//
#define L_FT_BUFFER		64

	//
	// total size of ft buffer pool
	// Note: // Note: For a total number of buffers used of N_BUF
	// it must hold:
	//  N_BUF * L_FT_BUFFER < N_FT_BUFFERS_TOTAL
	// TODO: This has to be checked in TL_init.c
	//

	//
	// maximal number of future time sync queues for
	// subformula results
	//
#define N_SUBFORMULA_SNYC_QUEUES	N_INSTRUCTIONS

	//
	// maximal number of future time sync queues for
	// atomic inputs
	// TODO Stefan: how large does this have to be in the worst case
	//
#define N_PATCH_SNYC_QUEUES		N_SUBFORMULA_SNYC_QUEUES




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
	// map memory
	//
typedef unsigned char	map_mem_t[N_MAP];


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

extern map_mem_t		map_mem_pt;
extern map_mem_t		map_mem_ft;

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
#ifdef TL_INIT_FILES
int TL_init(const char *FN_ftm, const char *FN_fti,
	    const char *FN_ptm, const char *FN_pti,
	    const char *FN_map);
#else
int TL_init();
#endif

int TL_update(FILE *fp, FILE *fp2);
int TL_update_pt();
int TL_update_ft(FILE *fp, FILE *fp2);

#ifdef __cplusplus
}
#endif

#endif
