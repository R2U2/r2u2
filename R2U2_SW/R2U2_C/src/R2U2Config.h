#ifndef R2U2_CONGIG_H
#define R2U2_CONGIG_H

#define R2U2_C_VERSION_MAJOR 1
#define R2U2_C_VERSION_MINOR 0

typedef double r2u2_input_data_t;

// TODO: Clean this up
/* TL Engine configuration */
//
// length of registers in bits
//
#define L_OPC 5
#define L_OP 10
#define L_INTVL 8
#define L_PMEM 7
#define L_SCRATCH 7
#define L_TIMESTAMP 16

//
// length of instruction
//
#define L_INSTRUCTION (L_OPC + L_OP + L_OP + L_INTVL + L_SCRATCH)

// for the file .ftscq
#define L_SCQ_ADDRESS 8

//
// length of registers in bits for mapping
//
#define L_MAP_PTFT 1
#define L_MAP_VALUE 8
#define L_MAP_SCRATCH 7
#define L_MAP (L_MAP_PTFT + L_MAP_VALUE + L_MAP_SCRATCH)

#define L_INTVL_TS 16
#define L_INTERVAL 32

//
// \infopcode_tty for rising-edge
// must be larger than any timestamp
//
#define TL_INF 32767 * 32767

//
// sizes of vectors and memories
// Note: these sizes conform to the FPGA configuration
//

//
// number of Boolean inputs
//
#define N_ATOMICS 128

//
// maximum number of instructions
//
#define N_INSTRUCTIONS 256

//
// number of MAP entries
//
#define N_MAP 256

//
// maximal number of past time INTERVAL ENTRIES
// this is equal to maximal number of pt temporal operators
//
#define N_INTERVAL 128

//
// length of each individual ring buffer for box operators
//
#define L_DOT_BUFFER 64

//
// total size of pt buffer pool
// Note: For a total number of buffers used of N_BUF
// it must hold:
//  N_BUF * L_DOT_BUFFER < N_DOT_BUFFERS_TOTAL
// This is checked in TL_init.c
//
#define N_DOT_BUFFERS_TOTAL 4096

//
// maximal number of future time INTERVAL ENTRIES
// this is equal to maximal number of ft temporal operators
//
//#define N_FT_INTERVAL     128

//
// length of each individual synchronization
// ring buffer for ft operators
//
#define L_FT_BUFFER 64

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
#define N_SUBFORMULA_SNYC_QUEUES N_INSTRUCTIONS

//
// maximal number of future time sync queues for
// atomic inputs
// TODO Stefan: how large does this have to be in the worst case
//
#define N_PATCH_SNYC_QUEUES N_SUBFORMULA_SNYC_QUEUES

#endif