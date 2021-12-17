#include <stdio.h>
#include <stdbool.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/TL/TL_observers.h"
#include "../src/TL/TL_queue_ft.h"

elt_ft_queue_t pop_cap(int pc, int obNum, elt_ft_queue_t* scq, int rd_ptr);
bool isEmpty_cap(int pc, int ObNum, elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp);

FILE* r2u2_debug_fptr = NULL;

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

static MunitResult end_sequence_operator (const MunitParameter params[], void* data) {
    
    //TL_config("/home/r2u2/r2u2/R2U2_C/src/binParser", NULL, NULL, NULL, NULL);

    instruction_mem_ft[0].opcode = OP_END_SEQUENCE;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult end_operator (const MunitParameter params[], void* data) {
    
    //TL_config("/home/r2u2/r2u2/R2U2_C/src/binParser", NULL, NULL, NULL, NULL);

    instruction_mem_ft[0].opcode = OP_END;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_lod (const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_END_SEQUENCE;

    TL_update_ft(NULL);

    int* rd_ptr = &(ft_sync_queues[0].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[0].start_addr],*rd_ptr);
    munit_assert_int(true, ==, value.v_q);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_not (const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = atoi(munit_parameters_get(params, "bool1"));
    int expected_verdict = !atomics_vector[0];

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_NOT;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;

    TL_update_ft(NULL);

    int* rd_ptr = &(ft_sync_queues[1].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[1].start_addr],*rd_ptr);
    munit_assert_int(expected_verdict, ==, value.v_q);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_globally (const MunitParameter params[], void* data) {

    TL_init();

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[1].adr_interval = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_globally_true(const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[1].adr_interval = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 0;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_globally_rising_edge(const MunitParameter params[], void* data) {

    TL_init();

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[1].adr_interval = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    atomics_vector[0] = false;
    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    t_now++;
    atomics_vector[0] = true;
    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_globally_true_too_early(const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[1].adr_interval = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 1;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_and (const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = atoi(munit_parameters_get(params, "bool1"));
    atomics_vector[1] = atoi(munit_parameters_get(params, "bool2"));

    int expected_verdict = atomics_vector[0] && atomics_vector[1];

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

    TL_update_ft(NULL);

    int* rd_ptr = &(ft_sync_queues[2].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[2].start_addr],*rd_ptr);
    printf("Expected %d, Got %d", expected_verdict, value.v_q);
    munit_assert_int(expected_verdict, ==, value.v_q);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_and_op_1_empty (const MunitParameter params[], void* data) {

    TL_init();

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].adr_interval = 0;
    instruction_mem_ft[3].opcode = OP_FT_AND;
    instruction_mem_ft[3].op1.opnd_type = subformula;
    instruction_mem_ft[3].op1.value = 2;
    instruction_mem_ft[3].op2.opnd_type = subformula;
    instruction_mem_ft[3].op2.value = 1;
    instruction_mem_ft[4].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    atomics_vector[0] = true;
    atomics_vector[1] = true;
    t_now++;
    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    // TOOD: Expecte Empty Queue
    // int* rd_ptr = &(ft_sync_queues[2].rd_ptr);
    // elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[2].start_addr],*rd_ptr);
    // printf("Expected %d, Got %d", expected_verdict, value.v_q);
    // munit_assert_int(expected_verdict, ==, value.v_q);

    return MUNIT_OK;
}

static MunitResult op_and_op_2_empty (const MunitParameter params[], void* data) {

    TL_init();

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_GLOBALLY_INTERVAL;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].adr_interval = 0;
    instruction_mem_ft[3].opcode = OP_FT_AND;
    instruction_mem_ft[3].op1.opnd_type = subformula;
    instruction_mem_ft[3].op1.value = 0;
    instruction_mem_ft[3].op2.opnd_type = subformula;
    instruction_mem_ft[3].op2.value = 2;
    instruction_mem_ft[4].opcode = OP_END_SEQUENCE;

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    atomics_vector[0] = true;
    atomics_vector[1] = true;
    t_now++;
    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    // TOOD: Expecte Empty Queue
    // int* rd_ptr = &(ft_sync_queues[2].rd_ptr);
    // elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[2].start_addr],*rd_ptr);
    // printf("Expected %d, Got %d", expected_verdict, value.v_q);
    // munit_assert_int(expected_verdict, ==, value.v_q);

    return MUNIT_OK;
}

static MunitResult op_until (const MunitParameter params[], void* data) {

    TL_init();

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_UNTIL_INTERVAL;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].op2.opnd_type = subformula;
    instruction_mem_ft[2].op2.value = 1;
    instruction_mem_ft[2].adr_interval = 0;
    instruction_mem_ft[3].opcode = OP_END_SEQUENCE;
    

    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);

    atomics_vector[0] = true;
    atomics_vector[1] = true;
    t_now++;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_until_trivial_true(const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[1] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_UNTIL_INTERVAL;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].op2.opnd_type = subformula;
    instruction_mem_ft[2].op2.value = 1;
    instruction_mem_ft[2].adr_interval = 0;
    instruction_mem_ft[3].opcode = OP_END_SEQUENCE;


    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 1;

    TL_update_ft(NULL);

    atomics_vector[0] = true;
    atomics_vector[1] = true;

    TL_update_ft(NULL);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_until_time_out(const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_FT_LOD;
    instruction_mem_ft[1].op1.value = 1;
    instruction_mem_ft[2].opcode = OP_FT_UNTIL_INTERVAL;
    instruction_mem_ft[2].op1.opnd_type = subformula;
    instruction_mem_ft[2].op1.value = 0;
    instruction_mem_ft[2].op2.opnd_type = subformula;
    instruction_mem_ft[2].op2.value = 1;
    instruction_mem_ft[2].adr_interval = 0;
    instruction_mem_ft[3].opcode = OP_END_SEQUENCE;


    interval_mem_ft[0].lb = 0;
    interval_mem_ft[0].ub = 0;

    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);
    t_now++;

    TL_update_ft(NULL);
    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_illegal (const MunitParameter params[], void* data) {
    
    instruction_mem_ft[0].opcode = OP_OR;

    TL_update_ft(NULL);

    munit_assert_int(1, ==, r2u2_errno);

    return MUNIT_OK;
}

static MunitResult op_end (const MunitParameter params[], void* data) {

    TL_init();

    atomics_vector[0] = true;

    instruction_mem_ft[0].opcode = OP_FT_LOD;
    instruction_mem_ft[0].op1.value = 0;
    instruction_mem_ft[1].opcode = OP_END;
    instruction_mem_ft[1].op1.opnd_type = subformula;
    instruction_mem_ft[1].op1.value = 0;
    instruction_mem_ft[1].op2.opnd_type = subformula;
    instruction_mem_ft[1].op2.value = 0;
    instruction_mem_ft[2].opcode = OP_END_SEQUENCE;


    TL_update_ft(stderr);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;

}

static MunitResult isEmpty_cap_bad_obNum(const MunitParameter params[], void* data) {

    assert_true(isEmpty_cap(0, 3, NULL, 0, 0, NULL, 0));

    return MUNIT_OK;
}

static MunitResult isEmpty_cap_not_set(const MunitParameter params[], void* data) {
    instruction_mem_ft[0].op1.opnd_type = not_set;
    instruction_mem_ft[0].op1.value = 0;
    assert_true(isEmpty_cap(0, 1, NULL, 0, 0, NULL, 0));

    return MUNIT_OK;
}

static MunitResult isEmpty_cap_atomic(const MunitParameter params[], void* data) {
    instruction_mem_ft[0].op1.opnd_type = atomic;
    instruction_mem_ft[0].op1.value = 0;
    assert_false(isEmpty_cap(0, 1, NULL, 0, 0, NULL, 0));

    return MUNIT_OK;
}

static MunitResult isEmpty_cap_illegal(const MunitParameter params[], void* data) {
    instruction_mem_ft[0].op1.opnd_type = 7;
    instruction_mem_ft[0].op1.value = 0;
    assert_true(isEmpty_cap(0, 1, NULL, 0, 0, NULL, 0));

    return MUNIT_OK;
}

static MunitResult pop_cap_bad_obNum(const MunitParameter params[], void* data) {
    elt_ft_queue_t res = pop_cap(0, 3, NULL, 0);
    elt_ft_queue_t tst = {false, -1};

    assert_memory_equal(sizeof(elt_ft_queue_t), &res, &tst);

    return MUNIT_OK;
}

static MunitResult pop_cap_direct(const MunitParameter params[], void* data) {
    instruction_mem_ft[0].op1.opnd_type = direct;
    instruction_mem_ft[0].op1.value = 0;
    elt_ft_queue_t res = pop_cap(0, 1, NULL, 0);
    elt_ft_queue_t tst = {0, 0};

    assert_memory_equal(sizeof(elt_ft_queue_t), &res, &tst);

    return MUNIT_OK;
}

static MunitResult pop_cap_illegal(const MunitParameter params[], void* data) {
    instruction_mem_ft[0].op1.opnd_type = 7;
    instruction_mem_ft[0].op1.value = 0;
    elt_ft_queue_t res = pop_cap(0, 1, NULL, 0);
    elt_ft_queue_t tst = {false, -1};

    assert_memory_equal(sizeof(elt_ft_queue_t), &res, &tst);

    return MUNIT_OK;
}

static char* bool1_params[] = {
    "0", "1", NULL
};

static char* bool2_params[] = {
    "0", "1", NULL
};

static MunitParameterEnum unary_bool_params[] = {
    {"bool1", bool1_params},
    {NULL, NULL}
};

static MunitParameterEnum binary_bool_params[] = {
    {"bool1", bool1_params},
    {"bool2", bool2_params},
    {NULL, NULL}
};

MunitTest end_sequence_operator_tests[] = {
    {
        "/loop_break",
        end_sequence_operator,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest load_operator_tests[] = {
    {
        "/read_atom",
        op_lod,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest not_operator_tests[] = {
    {
        "/bools",
        op_not,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        unary_bool_params
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest globally_operator_tests[] = {
    {
        "/false_0-1",
        op_globally,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/true",
        op_globally_true,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/rising_edge",
        op_globally_rising_edge,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/true_too_early",
        op_globally_true_too_early,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest and_operator_tests[] = {
    {
        "/bools",
        op_and,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        binary_bool_params
    },
    {
        "/op_1_empty",
        op_and_op_1_empty,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_2_empty",
        op_and_op_2_empty,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest until_operator_tests[] = {
    {
        "/false_0-1",
        op_until,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/trivial_true",
        op_until_trivial_true,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/time_out",
        op_until_time_out,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest illegal_operator_tests[] = {
    {
        "/crash",
        op_illegal,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest end_operator_tests[] = {
    {
        "/load_subformula",
        op_end,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

static const MunitSuite TL_update_ft_operator_suites[] = {
  { "/end_sequence_operator", end_sequence_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/load_operator", load_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/not_operator", not_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/globally_operator", globally_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/and_operator", and_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/until_operator", until_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/illegal_operator", illegal_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/end_operator", end_operator_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

MunitTest pop_cap_tests[] = {
    {
        "/bad_obNum",
        pop_cap_bad_obNum,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/direct",
        pop_cap_direct,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/illegal",
        pop_cap_illegal,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

MunitTest isEmpty_cap_tests[] = {
    {
        "/bad_obNum",
        isEmpty_cap_bad_obNum,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/not_set",
        isEmpty_cap_not_set,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/atomic",
        isEmpty_cap_atomic,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/illegal",
        isEmpty_cap_illegal,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

// MunitTest read_atomic_tests[] = {
//     {
//         "/op_end",
//         op_end,
//         test_setup,
//         NULL,
//         MUNIT_TEST_OPTION_NONE,
//         NULL
//     },
//     {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
// };

/* Test runner setup */
static const MunitSuite function_suites[] = {
  { "/pop_cap", pop_cap_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/isEmpty_cap", isEmpty_cap_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/tl_update_ft", NULL, TL_update_ft_operator_suites, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/read_atomic", read_atomic_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite suite = {
    "/tl_update_ft",
    NULL,
    function_suites,
    1,
    MUNIT_SUITE_OPTION_NONE
};

int main(int argc, const char* argv[]) {
    r2u2_debug_fptr = stderr;
    return munit_suite_main(&suite, NULL, argc, argv);
}
