#include <string.h>
#include <stdio.h>

#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_ft.h"
#include "TL_queue_pt.h"
#include "parse.h"

#ifndef CONFIG // TODO: Do we need to conditionally compile these?
void TL_config(const char* ftm, const char* fti, const char* ftscq, const char* ptm, const char* pti)
{
    // TODO: Does this crash on bad bins?
    // TODO: Weird memory stuff to be checked
    parse_inst_ft_file(ftm);
    parse_interval_ft_file(fti);
    parse_scq_size_file(ftscq);

    parse_inst_pt_file(ptm);
    parse_interval_pt_file(pti);
}
#else
void TL_config(const char* ftm, const char* fti, const char* ftscq, const char* ptm, const char* pti)
{
    /* Future Time Configuration */
    parse_inst_ft_bin(ftm);
    parse_interval_ft_bin(fti);
    parse_scq_size_bin(ftscq);

    /* Past Time Configuration */
    parse_inst_pt_bin(ptm);
    parse_interval_pt_bin(pti);
}
#endif

/* Extended Output Configuration */
// Keeping this separate from binParser until configuration unification
void TL_aux_config(const char* aux){
    char type, line[MAX_LINE];

    #if R2U2_TL_Formula_Names
    char *next_ptr;
    size_t f_num;
    next_ptr = aux_str_arena;
    #endif

    #if R2U2_TL_Contract_Status
    size_t c_num=0;
    aux_con_map[0] = aux_con_arena;
    #endif

    #if R2U2_AT_Signal_Sets
    int indx;
    size_t r_num=0;
    FILE *stream;
    aux_signal_set_map[0] = aux_signal_set_arena;
    #endif

    FILE *file = fopen ( aux, "r" );
    if ( file != NULL ) {
        while ( fgets (line, sizeof(line), file ) != NULL ) { /* read a line */
            if (sscanf(line, "%c", &type) == 1) {
                switch(type){

                    #if R2U2_TL_Formula_Names
                        case 'F': {
                            sscanf(line, "%*c %s %zu", next_ptr, &f_num);
                            aux_str_map[f_num] = next_ptr;
                            next_ptr += strlen(next_ptr) + 1; // Skip past Null
                            R2U2_DEBUG_PRINT("Saved name '%s' for formula %zu\n", aux_str_map[f_num], f_num);
                            break;
                        }
                    #endif

                    #if R2U2_TL_Contract_Status
                        case 'C': {
                            sscanf(line, "%*c %s %zu %zu %zu", aux_con_map[c_num], &aux_con_forms[3*c_num], &aux_con_forms[3*c_num+1], &aux_con_forms[3*c_num+2]);
                            aux_con_map[c_num+1] = aux_con_map[c_num] + strlen(aux_con_map[c_num]) + 1; // Leave a Null
                            c_num++;
                            break;
                        }
                    #endif

                    #if R2U2_AT_Signal_Sets
                        case 'R': {
                            stream = fmemopen(line, strlen(line), "r");
                            R2U2_TRACE_PRINT("\n\nSignal Set:\n\tInput: %s", line);
                            fscanf(stream, "%*c %*s %u", &indx);
                            R2U2_TRACE_PRINT("\tIndex: %d\n", indx);
                            aux_signal_set_map[indx] = &(aux_signal_set_arena[r_num]);
                            R2U2_TRACE_PRINT("\tArena start: (%p)\n",aux_signal_set_arena);
                            R2U2_TRACE_PRINT("\tArena offset: %d (%p)\n", r_num, &aux_signal_set_arena[r_num]);
                            R2U2_TRACE_PRINT("\tArena Value: %d\n", aux_signal_set_arena[r_num]);
                            R2U2_TRACE_PRINT("\tMap start: (%p)\n", &aux_signal_set_map);
                            R2U2_TRACE_PRINT("\tMap offset: %d (%p)\n", indx, &(aux_signal_set_map[indx]));
                            R2U2_TRACE_PRINT("\tMap Value: (%p)\n", aux_signal_set_map[indx]);
                            R2U2_TRACE_PRINT("\tMap Deref: %d\n", *(aux_signal_set_map[indx]));
                            *(aux_signal_set_map[indx]) = 0;
                            r_num++; /* Index of next empty spot in array */
                            R2U2_TRACE_PRINT("\tScanning members:\n");
                            while(fscanf(stream, " %d", &(aux_signal_set_arena[r_num])) == 1){
                                R2U2_TRACE_PRINT("\t\tGot member: %d\n", aux_signal_set_arena[r_num]);
                                (*aux_signal_set_map[indx])++;
                                r_num++;
                            }
                            R2U2_TRACE_PRINT("\tNumber of members: %d\n", *aux_signal_set_map[indx]);
                            R2U2_TRACE_PRINT("\tMembers:\n\t\t");
                            for (int i = 1; i <= *aux_signal_set_map[indx]; ++i) {
                                R2U2_TRACE_PRINT("%d, ", *(aux_signal_set_map[indx]+i));
                            }
                            R2U2_TRACE_PRINT("\n");
                            R2U2_TRACE_PRINT("\tStored Values\n\t\tthis set: %d\n\t\tall sets: %zu\n", *aux_signal_set_map[indx], r_num);
                            break;
                        }
                    #endif

                    default: {
                        R2U2_DEBUG_PRINT("Aux: No handler enabled for type %c\n", type);
                        break;
                    }
                }
            } else {
                // Error? Skip bad line
                R2U2_DEBUG_PRINT("Aux: Skipping bad line in aux file\n");
            }
        }

        #if R2U2_TL_Contract_Status
        aux_con_max = c_num;
        #endif

        fclose ( file );
    } else {
        perror ( aux ); /* why didn't the file open? */
    }
}

int TL_init()
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

    //
    // initialize queues
    //

    if (N_PT_QUEUES * L_DOT_BUFFER > N_DOT_BUFFERS_TOTAL) {
        R2U2_DEBUG_PRINT("not enough pt-queue space\n");
        r2u2_errno = 1;
        return 1; // TODO: Error codes
    }

    // set up pt queues
    for (i=0; i< N_PT_QUEUES;i++){
        pt_box_queues[i].head = 0;
        pt_box_queues[i].tail = 0;
        pt_box_queues[i].n_elts = 0;
        pt_box_queues[i].queue = &(pt_box_queue_mem[i * L_DOT_BUFFER]);
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

    return 0;
}

int TL_update(FILE* log_file)
{

    r2u2_errno = 0;

    R2U2_DEBUG_PRINT("\n\tPT Update\n");
    TL_update_pt(log_file);
    R2U2_DEBUG_PRINT("\n\tFT Update\n");
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
