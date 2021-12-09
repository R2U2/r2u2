#include "munit/munit.h"
#include <stdbool.h>
#include <stdio.h>
#include "../src/TL/TL_observers.h"
#include "../src/TL/TL_queue_ft.h"

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
    interval_mem_ft[1].ub = 1;

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
    interval_mem_ft[1].ub = 1;

    TL_update_ft(NULL);

    atomics_vector[0] = true;
    atomics_vector[1] = true;

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
    
    FILE *f;
    f = fopen("log.txt", "w");

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


    TL_update_ft(f);

    munit_assert_int(0, ==, r2u2_errno);

    return MUNIT_OK;

}

static MunitResult test_tl_config (const MunitParameter params[], void* data) {
    
    TL_config("./test/test_ftm.bin", "./test/test_fti.bin", "./test/test_ftscq.bin", NULL, NULL);

    atomics_vector[0] = true;
    atomics_vector[1] = true;

    TL_update_ft(NULL);

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
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/queue_ft_isEmpty",
        queue_ft_isEmpty,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/end_sequence_operator",
        end_sequence_operator,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_lod",
        op_lod,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_not",
        op_not,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        unary_bool_params
    },
    {
        "/op_globally",
        op_globally,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_and",
        op_and,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        binary_bool_params
    },
    {
        "/op_until",
        op_until,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_illegal",
        op_illegal,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/op_end",
        op_end,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/test_tl_config",
        test_tl_config,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/test_tl_update",
        test_tl_update,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
    {
        "/test_tl_init",
        test_tl_init,
        test_setup,
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
    r2u2_debug_fptr = stderr;
    return munit_suite_main(&suite, NULL, argc, argv);
}