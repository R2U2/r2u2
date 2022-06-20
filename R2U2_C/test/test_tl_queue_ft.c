#include <stdio.h>
#include <stdbool.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/TL/TL_observers.h"
#include "../src/TL/TL_queue_ft.h"

FILE* r2u2_debug_fptr = NULL;
/* Test Suite Layout
**
** This file creates the `test_at_checkers` test executable  which runs tests
** for `at_checkers.c` which are contained in `at_checkers_suite`
**
** To organize the tests, the `at_checkers_suite` contains a list of
** sub-suites, `function_suites`, one per function of `at_checkers.c`
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

static MunitResult queue_ft_add (const MunitParameter params[], void* data) {

    elt_ft_queue_t newData = {true, 2};
    elt_ft_queue_t newData2 = {true, 3};
    elt_ft_queue_t newData3 = {false, 4};

  // Set the SCQ's write pointer
  int scq_size_wr = addr_SCQ_map_ft[0].end_addr - addr_SCQ_map_ft[0].start_addr;

  // And add asynchrounous results to the shared connection queue
  add(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, newData, &(ft_sync_queues[0].wr_ptr));

    int* rd_ptr = &(ft_sync_queues[0].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[0].start_addr],*rd_ptr);
    munit_assert_int(2, ==, value.t_q);

    add(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, newData2, &(ft_sync_queues[0].wr_ptr));
    value = pop(&SCQ[addr_SCQ_map_ft[0].start_addr],*rd_ptr);
    munit_assert_int(3, ==, value.t_q);

    (&SCQ[addr_SCQ_map_ft[0].start_addr]+ft_sync_queues[0].wr_ptr)->t_q = -1;
    add(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, newData3, &(ft_sync_queues[0].wr_ptr));
    isEmpty(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, ft_sync_queues[0].wr_ptr, rd_ptr, 4);
    value = pop(&SCQ[addr_SCQ_map_ft[0].start_addr],*rd_ptr);
    munit_assert_int(4, ==, value.t_q);




    return MUNIT_OK;
}

static MunitResult queue_ft_isEmpty(const MunitParameter params[], void* data) {

    elt_ft_queue_t newData = {true, 2};
    int scq_size_wr = addr_SCQ_map_ft[0].end_addr - addr_SCQ_map_ft[0].start_addr;
    add(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, newData, &(ft_sync_queues[0].wr_ptr));

    int* rd_ptr = &(ft_sync_queues[0].rd_ptr);
    bool boolIsEmpty = isEmpty(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, NULL, rd_ptr, 1);

    munit_assert_false(boolIsEmpty);

    *rd_ptr = ft_sync_queues[0].wr_ptr;
    boolIsEmpty = isEmpty(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, ft_sync_queues[0].wr_ptr, rd_ptr, 10);
    munit_assert_true(boolIsEmpty);

    return MUNIT_OK;

}

/* Test runner setup */
static const MunitTest function_tests[] = {
    {
        "/add",
        queue_ft_add,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/isEmpty",
        queue_ft_isEmpty,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite tl_suite = {
  "tl_queue_ft", /* name */
  function_tests, /* tests */
  NULL, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  r2u2_debug_fptr = stderr;
  return munit_suite_main(&tl_suite, NULL, argc, argv);
}
