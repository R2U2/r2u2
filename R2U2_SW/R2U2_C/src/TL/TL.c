#include <string.h>

#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_ft.h"
#include "TL_queue_pt.h"
#include "parse.h"

void TL_config(TL_asm_files files)
{
    // TODO: Does this crash on bad bins?
    // TODO: Weird memory stuff to be checked
    parse_inst(files[0]);
    parse_interval(files[1]);
    parse_scq_size(files[2]);
}

int TL_init()
{
    int i;
    int j;
    int n_queues_pt;
    int n_queues_ft;

    t_now = 0;
    r2u2_errno = 0;

    //
    // reset execution engine (TBD)
    // initialize input and output vectors
    // and local memories
    //
    // for (i=0; i<N_INSTRUCTIONS;i++){
    //      //
    //      // initialize PT results
    //      //
    //  results_pt[i]= false;
    //  results_pt_prev[i]= false;
    //  results_pt_rising[i] = TL_INF;
    //      //
    //      // initialize FT results
    //      //
    //  results_ft[i].async_val = false;
    //  results_ft[i].async_val = false;
    //  results_ft[i].sync_val  = F;  //initialize to false due to edge
    // detection

    // }

    //
    // initialize atomics
    //
    for (i = 0; i < N_ATOMICS; i++) {
        atomics_vector[i] = false;
        atomics_vector_prev[i] = false;
    }

    //
    // initialize queues
    //

    // get number of pt queues
    n_queues_pt = l_interval_mem_pt;

    if (n_queues_pt * L_DOT_BUFFER > N_DOT_BUFFERS_TOTAL) {
        DEBUG_PRINT("not enough pt-queue space\n");
        r2u2_errno = 1;
        return 1; // TODO: Error codes
    }

    // set up pt queues
    // for (i=0; i< n_queues_pt;i++){
    //  pt_box_queues[i].head = 0;
    //  pt_box_queues[i].tail = 0;
    //  pt_box_queues[i].n_elts = 0;
    //  pt_box_queues[i].queue = pt_box_queue_mem + i * L_DOT_BUFFER;
    //  }

    // Initialize ft-sync queues
    for (i = 0; i < N_SUBFORMULA_SNYC_QUEUES; i++) {
        ft_sync_queues[i].wr_ptr = 0;
        ft_sync_queues[i].rd_ptr = 0;
        ft_sync_queues[i].rd_ptr2 = 0;
        ft_sync_queues[i].m_edge = 0;
        ft_sync_queues[i].preResult = 0;
        ft_sync_queues[i].desired_time_stamp = 0;
        switch (instruction_mem_ft[i].opcode) {
        case OP_FT_GJ:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { false, -1 };
            break;
        case OP_FT_UJ:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { true, -1 };
            break;
        default:
            ft_sync_queues[i].pre = (elt_ft_queue_t) { true, 0 };
        }
    }

    return 0;
}

int TL_update(FILE* log_file)
{

    r2u2_errno = 0;

    // TL_update_pt();
    TL_update_ft(log_file);

    //
    // do temporal housekeeping:
    // data -> data_prev
    // increment time stamp

    //
    // put the current atomics into the previous one
    //
    // TODO: Would it be better to dubble flip buffers?
    memcpy(atomics_vector_prev, atomics_vector, sizeof(atomics_vector_t));

    //
    // increase time stamp
    //
    t_now++;

    return 0;
}