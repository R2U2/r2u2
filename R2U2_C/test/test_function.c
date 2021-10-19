#include "munit/munit.h"
#include <stdbool.h>
#include "../src/TL/TL_observers.h"
#include "../src/TL/TL_queue_ft.h"

static MunitResult queue_ft_add (const MunitParameter params[], void* data) {
    
    elt_ft_queue_t newData = {true, 12};

	// Set the SCQ's write pointer
	int scq_size_wr = addr_SCQ_map_ft[0].end_addr - addr_SCQ_map_ft[0].start_addr;

	// And add asynchrounous results to the shared connection queue
	add(&SCQ[addr_SCQ_map_ft[0].start_addr], scq_size_wr, newData, &(ft_sync_queues[0].wr_ptr));

    int* rd_ptr = &(ft_sync_queues[0].rd_ptr);
    elt_ft_queue_t value = pop(&SCQ[addr_SCQ_map_ft[0].start_addr],*rd_ptr);
    munit_assert_int(12, ==, value.t_q);


    return MUNIT_OK;
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

static MunitResult op_illegal (const MunitParameter params[], void* data) {
    
    instruction_mem_ft[0].opcode = OP_OR;

    TL_update_ft(NULL);

    munit_assert_int(1, ==, r2u2_errno);

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

MunitTest tests[] = {
    {
        "/queue_ft_add",
        queue_ft_add,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/end_sequence_operator",
        end_sequence_operator,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_lod",
        op_lod,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_not",
        op_not,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        unary_bool_params
    },
    {
        "/op_and",
        op_and,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        binary_bool_params
    },
    {
        "/op_illegal",
        op_illegal,
        NULL,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL}
};

static const MunitSuite suite = {
    "/tests",
    tests,
    NULL,
    1,
    MUNIT_SUITE_OPTION_NONE
};

int main(int argc, const char* argv[]) {
    return munit_suite_main(&suite, NULL, argc, argv);
}