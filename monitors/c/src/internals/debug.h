#ifndef R2U2_DEBUG_H
#define R2U2_DEBUG_H

#include <stdio.h>
#include <stdbool.h>

/* Portable form of marking unused  */
// From: https://stackoverflow.com/a/3599170 [CC BY-SA 3.0]
#define UNUSED(x) (void)(x)

/* Debug Conditionals */
#if R2U2_DEBUG
    extern FILE* r2u2_debug_fptr;
    #define R2U2_DEBUG_PRINT(...) do{ if (r2u2_debug_fptr != NULL) {fprintf( r2u2_debug_fptr, __VA_ARGS__ );} } while( false )
#else
    #define R2U2_DEBUG_PRINT(...)
#endif

#if R2U2_DEBUG
    static void r2u2_scq_arena_print(r2u2_scq_arena_t arena) {
    R2U2_DEBUG_PRINT("\t\t\tShared Connection Queue Arena:\n\t\t\t\tBlocks: <%p>\n\t\t\t\tQueues: <%p>\n\t\t\t\tSize: %ld\n", arena.control_blocks, arena.queue_mem, ((void*)arena.queue_mem) - ((void*)arena.control_blocks));
    }

    static void r2u2_scq_queue_print(r2u2_scq_arena_t arena, r2u2_time queue_id) {
    r2u2_scq_control_block_t *ctrl = &((arena.control_blocks)[queue_id]);

    R2U2_DEBUG_PRINT("\t\t\tID: |");
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
        R2U2_DEBUG_PRINT(" <%p> |", (void*)&((ctrl->queue)[i]));
    }
    R2U2_DEBUG_PRINT("\n\t\t\t%3d |", queue_id);
    for (r2u2_time i = 0; i < ctrl->length; ++i) {
        R2U2_DEBUG_PRINT("  %s:%9d  |", (get_verdict_truth((ctrl->queue)[i])) ? "T" : "F", get_verdict_time((ctrl->queue)[i]));
    }
    R2U2_DEBUG_PRINT("\n");
    }
#endif

#if R2U2_TRACE
    #define R2U2_TRACE_PRINT(...) do{ fprintf( stderr, __VA_ARGS__ ); } while( false )
#else
    #define R2U2_TRACE_PRINT(...)
#endif

#endif /* R2U2_DEBUG_H */
