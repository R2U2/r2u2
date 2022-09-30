#include <stdio.h>
#include <stdlib.h>

#include "bz_stack.h"

void bz_stack_init(bz_stack_t *s)
{
    uint32_t i;
    for(i = 0; i < BZ_STACK_SIZE; ++i) {
        s->stack[i].i = 0;
    }

    s->size = 0;
}

void bz_stack_bpush(bz_stack_t *s, bool val)
{
    if(s->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max s size exceeded");
        exit(1);
    }

    s->stack[s->size].b = val;
    s->size++;
}

void bz_stack_ipush(bz_stack_t *s, uint32_t val)
{
    if(s->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max s size exceeded");
        exit(1);
    }

    s->stack[s->size].i = val;
    s->size++;
}

void bz_stack_fpush(bz_stack_t *s, float val)
{
    if(s->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max s size exceeded");
        exit(1);
    }

    s->stack[s->size].f = val;
    s->size++;
}

bz_val_t bz_stack_pop(bz_stack_t *s)
{
    if(s->size == 0) {
        bz_val_t err;
        err.b = false;
        return err;
    }

    bz_val_t top = s->stack[s->size-1];
    s->size--;

    return top;
}