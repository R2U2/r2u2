#include "BZ_stack.h"

void bz_stack_init(bz_stack_t *stack)
{
    stack->size = 0;
}

void bz_stack_bpush(bz_stack_t *stack, bool val)
{
    if(stack->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max stack size exceeded");
        exit(1);
    }

    stack[stack->size].b = val;
    stack->size++;
}

void bz_stack_ipush(bz_stack_t *stack, uin32_t val)
{
    if(stack->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max stack size exceeded");
        exit(1);
    }

    stack[stack->size].i = val;
    stack->size++;
}

void bz_stack_bpush(bz_stack_t *stack, float val)
{
    if(stack->size == BZ_STACK_SIZE) {
        fprintf(stderr, "Error in Booleanizer: max stack size exceeded");
        exit(1);
    }

    stack[stack->size].f = val;
    stack->size++;
}

bz_val_t *bz_stack_pop(bz_stack_t *stack)
{
    if(stack->size == 0) {
        return NULL;
    }

    stack->size--;
    return stack[stack->size+1];
}