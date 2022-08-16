#ifndef BZ_STACK_H
#define BZ_STACK_H

#define BZ_STACK_SIZE 16

#include <stdbool.h>

typedef union bz_val {
    bool b;
    uint32_t i;
    float f;
} bz_val_t;

typedef struct bz_stack {
    bz_val_t stack[BZ_STACK_SIZE];
    uint32_t size;
} bz_stack_t;

void bz_stack_init(bz_stack_t *);
void bz_stack_free(bz_stack_t *);
void bz_stack_bpush(bz_stack_t *, bool);
void bz_stack_ipush(bz_stack_t *, uint32_t);
void bz_stack_fpush(bz_stack_t *, float);
bz_val_t *bz_stack_pop(bz_stack_t *);

#endif