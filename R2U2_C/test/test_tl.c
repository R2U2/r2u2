#include <stdio.h>
#include <stdbool.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/TL/TL_observers.h"
#include "../src/TL/TL_queue_ft.h"

FILE* r2u2_debug_fptr = NULL;
/* Test Suite Layout
**
** This file creates the `test_at_operations` test executable  which runs tests
** for `at_operations.c` which are contained in `at_operations_suite`
**
** To organize the tests, the `at_operations_suite` contains a list of
** sub-suites, `function_suites`, one per function of `at_operations.c`
**
** New tests should be added to the per-function test-suites such as
** `op_rate_tests` which will propagated automatically.
**
*/

static void* test_setup(const MunitParameter params[], void* user_data)
{
    int i;

    t_now = 0;
    r2u2_errno = 0;

    //
    // reset execution engine (TBD)
    // initialize input and output vectors
    // and local memories
    //
    for (i=0; i<N_INSTRUCTIONS;i++){
        //
        // initialize PT results
        //
        results_pt[i]= false;
        results_pt_prev[i]= false;
        results_pt_rising[i] = TL_INF;
        //
        // initialize FT results
        //
        // results_ft[i].async_val = false;
        // results_ft[i].async_val = false;
        // initialize to false due to edge detection
        // results_ft[i].sync_val  = F;
    }
    // Call pt_prev_init() function; check if error code, else pass
    //if(pt_prev_init() == 1){
    //    printf("Failed to initialize PT's previous time steps\n");
    //}

    //
    // initialize atomics
    //
    for (i = 0; i < N_ATOMICS; i++) {
        atomics_vector[i] = false;
        atomics_vector_prev[i] = false;
    }

    // Initialize ft-sync queues
    for (i = 0; i < N_SUBFORMULA_SNYC_QUEUES; i++) {
        ft_sync_queues[i].wr_ptr = 0;
        ft_sync_queues[i].rd_ptr = 0;
        ft_sync_queues[i].rd_ptr2 = 0;
        ft_sync_queues[i].m_edge = 0;
        ft_sync_queues[i].preResult = 0;
        ft_sync_queues[i].desired_time_stamp = 0;
        switch (instruction_mem_ft[i].opcode) {
        case OP_FT_GLOBALLY_INTERVAL:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { false, -1 };
            break;
        case OP_FT_UNTIL_INTERVAL:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { true, -1 };
            break;
        default:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { true, 0 };
        }
    }

    for(int count = 0; count < 10; count++){
        addr_SCQ_map_ft[count].start_addr = count*10;
        addr_SCQ_map_ft[count].end_addr = 9 + count*10;
    }
}

static MunitResult test_tl_config_call (const MunitParameter params[], void* data) {

    TL_config(NULL, NULL, NULL, NULL, NULL);

    return MUNIT_OK;
}

static MunitResult tl_config_parse (const MunitParameter params[], void* data) {

    // TODO: Assumes testing working dir, fix this when we unify bin parser
    TL_config("./test/data/ftm.bin", "./test/data/fti.bin", "./test/data/ftscq.bin", "./test/data/ptm.bin", "./test/data/pti.bin");

    atomics_vector[0] = true;
    atomics_vector[1] = true;

    TL_update_ft(stderr);

    int* rd_ptr = &(ft_sync_queues[1].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[1].start_addr],*rd_ptr);
    munit_assert_int(true, ==, value.v_q);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult test_tl_update (const MunitParameter params[], void* data) {

    instruction_mem_pt[0].opcode = OP_END_SEQUENCE;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_AND;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].op2.opnd_type = subformula;
    instruction_mem_ft[2].op2.value = 1;
    instruction_mem_ft[3].opcode = OP_END_SEQUENCE;

    atomics_vector[0] = false;
    atomics_vector[1] = true;

    TL_update(NULL);

    munit_assert_int(false, ==, atomics_vector_prev[0]);
    munit_assert_int(true, ==, atomics_vector_prev[1]);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;

}

static MunitResult test_tl_init (const MunitParameter params[], void* data) {

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[1].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[2].opcode = OP_FT_UNTIL_INTERVAL;

    TL_init();

    munit_assert_int(true, ==, ft_sync_queues[0].pre.v_q);
    munit_assert_int(0, ==, ft_sync_queues[0].pre.t_q);

    munit_assert_int(false, ==, ft_sync_queues[1].pre.v_q);
    munit_assert_int(-1, ==, ft_sync_queues[1].pre.t_q);

    munit_assert_int(true, ==, ft_sync_queues[2].pre.v_q);
    munit_assert_int(-1, ==, ft_sync_queues[2].pre.t_q);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;

}

/* Test runner setup */
static const MunitTest function_tests[] = {
    {
        "/tl_config_call",
        test_tl_config_call,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/tl_config_parse",
        tl_config_parse,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/tl_update",
        test_tl_update,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/tl_init",
        test_tl_init,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite tl_suite = {
  "tl", /* name */
  function_tests, /* tests */
  NULL, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  r2u2_debug_fptr = stderr;
  return munit_suite_main(&tl_suite, NULL, argc, argv);
}
