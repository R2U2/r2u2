#ifndef R2U2_CONFIG_H
#define R2U2_CONFIG_H

#define N_SIGS 256
#define N_ATOMICS 256
#define N_INSTRUCTIONS 256
#define N_AT 256
#define N_INTERVAL 128
#define L_OPC 5
#define L_OP 10
#define L_INTVL 8
#define L_SCRATCH 7
#define L_COMP 3
#define L_FILTER 4
#define L_NUM 32
#define L_INTERVAL 32
#define L_SCQ_SIZE 1024
#define L_SCQ_ADDRESS 16
#define L_DOT_BUFFER 64
#define N_PT_QUEUES 128
#define TL_INF 1073676289
#define MAX_LINE 128
#define L_VARIABLE 8
#define N_FORMULAS 64
#define L_ATOMIC_ADDR 8
#define L_SIG_ADDR 8
#define L_INSTRUCTION 40
#define L_AT_INSTRUCTION 88
#define N_DOT_BUFFERS_TOTAL 8192
#define N_SUBFORMULA_SNYC_QUEUES 256
typedef double r2u2_input_data_t;
typedef unsigned int timestamp_t;
typedef char signal_names[N_SIGS*L_VARIABLE];
typedef char formula_names[N_FORMULAS*L_VARIABLE];

#endif