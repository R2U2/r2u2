/*=======================================================================================
** File Name:  TL_update_ft.c
**
** Title:  One execution step for the FT logic engine
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
** Functions Defined:
**  TL_update_ft()
**
** Purpose:
**  execute all TL instructions for the FT engine
**  gets input from atomics_vector and places
**  outputs into results_ft
**
** Limitations, Assumftions, External Events, and Notes:
**  NA
**
**
** Modification History:
**   Date | Author | Descriftion
**   ---------------------------
** Stefan Jaksic, Patrick Moosbruger
** Apr.14.2019 | Pei  | Clean up the code and rewrite the function
** Apr.05.2020 | Matt | Updated print statements for standard & debug modes
**=====================================================================================*/


#include <stdio.h>
#include <string.h>

#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_ft.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y))

/**
*   get_interval_lb_ft
*   get the lower bound (or time point) from temporal information
*   for instruction at pc
*/
inline int  get_interval_lb_ft(int pc);

/**
*   get_interval_ub_ft
*   get the upper bound (or time point) from temporal information
*   for instruction at pc
*/
inline int  get_interval_ub_ft(int pc);

elt_ft_queue_t pop_cap(int pc, int obNum, elt_ft_queue_t* scq, int rd_ptr);

bool isEmpty_cap(int pc, int ObNum, elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp);


//--------------------------------------------------------------------
//  TL_update_ft()
//  main routine to run the PT engine on compiled instructions
//  * executes all instructions
//  * updates results_ft and queues
//--------------------------------------------------------------------
int TL_update_ft(FILE *log_file) {
	int pc   = 0;
	int progress = 0;

	while (progress < 1) {

	    // Sequentially iterate through the program instructions
		for(pc = 0; pc < N_INSTRUCTIONS; pc++) {
			if(instruction_mem_ft[pc].opcode == OP_END_SEQUENCE) {
	            DEBUG_PRINT("PC:%d END_SEQUENCE\n", pc);
	            break;
	        }

	        // Case statement for determining which opcode is currently in the program counter 'pc'
	        switch(instruction_mem_ft[pc].opcode)
	        {

			//----------------------------------------------------
			// OP_END, OP_END_SEQUENCE
			//----------------------------------------------------
			case OP_END: {
				int op1 = 0, scq_size_rd = 0, input_wr_ptr = 0;

	            // Declare a new pointer for the SCQ's operand
	            elt_ft_queue_t *scq_seg = NULL;

	            // If the opcode type is a subformula
	            if(instruction_mem_ft[pc].op1.opnd_type == subformula) {
	                // Grab the op1 value from the instruction memory
	                op1 = instruction_mem_ft[pc].op1.value;
	                // Set the SCQ's read pointer
	                scq_size_rd = addr_SCQ_map_ft[op1].end_addr - addr_SCQ_map_ft[op1].start_addr;
        	        // Grab the values within the SCQ at the start address
        	        scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
        	        // Set the input's write pointer (old queue structure)
        	        input_wr_ptr = ft_sync_queues[op1].wr_ptr;
        	    }
        	    // Set the SCQ's write pointer
        	    int scq_size_wr = addr_SCQ_map_ft[pc].end_addr - addr_SCQ_map_ft[pc].start_addr;
        	    int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);

        	    // While the formula is not complete, i.e., the SCQ is non-empty
        	    while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
        	        // Pop the sequence from the SCQ
        	        elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
        	        // Copy over the sequence from input to res
        	        elt_ft_queue_t res = {input.v_q,input.t_q};
        	        // Add the new element to the SCQ
        	        add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
        	        // Synchronize the queues
        	        ft_sync_queues[pc].desired_time_stamp = input.t_q+1;

        	        DEBUG_PRINT("PC:%d END = (%d,%d)\n", pc, res.t_q, res.v_q);
        	        fprintf(log_file,"%d:%d,%s\n", (int)instruction_mem_ft[pc].op2.value, res.t_q, res.v_q?"T":"F");
				}
				progress = 1;
				break;
			}

        	//----------------------------------------------------
        	// OP_FT_LOD
        	//----------------------------------------------------
        	case OP_FT_LOD: {
        	    bool v;
        	    unsigned int t_e;

        	    // Retrieve the Boolean atomic from the pre-processing layer
        	    read_atomic(pc, &v, &t_e);


        	    // Set 'newData' as the newly read atomic
        	    elt_ft_queue_t newData = {v,t_e};

        	    // Set the SCQ's write pointer
        	    int scq_size_wr = addr_SCQ_map_ft[pc].end_addr - addr_SCQ_map_ft[pc].start_addr;

	            // And add asynchrounous results to the shared connection queue
	            add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, newData, &(ft_sync_queues[pc].wr_ptr));

	            //add_and_aggregate_queue_ft(&ft_sync_queues[pc], v, t_e);

	            // If the dbg_flag is set, print to log and command line
	            DEBUG_PRINT("PC:%d LOAD = (%d,%d)\n", pc, t_e, v);
		    progress = 1;
	            break;

	        }

	        //----------------------------------------------------
	        // OP_FT_NOT
	        //----------------------------------------------------
	        case OP_FT_NOT: {
	            int op1=0, scq_size_rd=0, input_wr_ptr=0;

	            // Declare a new pointer for the SCQ's operand
	            elt_ft_queue_t *scq_seg = NULL;

	            // If the opcode type is a subformula
	            if(instruction_mem_ft[pc].op1.opnd_type == subformula) {
	                // Grab the operand's value
	                op1 = instruction_mem_ft[pc].op1.value;
	                // Set the SCQ's read pointer
	                scq_size_rd = addr_SCQ_map_ft[op1].end_addr - addr_SCQ_map_ft[op1].start_addr;
	                // Grab the values within the SCQ at the start address
	                scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
	                // Set the input's write pointer (old queue structure)
	                input_wr_ptr = ft_sync_queues[op1].wr_ptr;
	            }

	            // Set the SCQ's write pointer
	            int scq_size_wr = addr_SCQ_map_ft[pc].end_addr - addr_SCQ_map_ft[pc].start_addr;
	            int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);

	            // While the formula is not complete, i.e., the SCQ is non-empty
	            while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
	                // Pop the sequence from the SCQ
	                elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
	                // Copy over the sequence from input to res
	                elt_ft_queue_t res = {!input.v_q,input.t_q};
	                // Add the new element to the SCQ
	                add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
	                // Synchronize the queues
	                ft_sync_queues[pc].desired_time_stamp = input.t_q+1;
	                // The code is generated as 'make debug', print to log and command line
	                DEBUG_PRINT("PC:%d NOT = (%d,%d)\n", pc, res.t_q, res.v_q);
	            }
		    progress = 1;
	            break;
	        }

	        //----------------------------------------------------
	        // OP_FT_AND
	        //----------------------------------------------------

	        case OP_FT_AND: {
	            DEEP_PRINT("\n\n--AND--\n");
	            int op1=0, op2=0, scq_size_rd_1=0, scq_size_rd_2=0, input_wr_ptr_1=0, input_wr_ptr_2=0;

	            // Declare new pointers for the SCQ's operandds
	            elt_ft_queue_t *scq_seg_1 = NULL, *scq_seg_2 = NULL;

	            // If the first operand's opcode is a subformula
	            if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
	                // Grab the op1 value from the instruction memory
	                op1 = instruction_mem_ft[pc].op1.value;
	                // Set the SCQ's read pointer for the first operand
	                scq_size_rd_1 = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
	                // Grab the values within the SCQ at the start address
	                scq_seg_1 = &SCQ[addr_SCQ_map_ft[op1].start_addr];
	                // Set the input's write pointer (old queue structure)
	                input_wr_ptr_1 = ft_sync_queues[op1].wr_ptr;
	            }
	            // If the second operand's opcode is a subformula
	            if(instruction_mem_ft[pc].op2.opnd_type==subformula) {
	                // Grab the op2 value from the instruction memory
	                op2 = instruction_mem_ft[pc].op2.value;
	                // Set the SCQ's read pointer for the second operand
	                scq_size_rd_2 = addr_SCQ_map_ft[op2].end_addr-addr_SCQ_map_ft[op2].start_addr;
	                // Grab the values within the SCQ at the start address
	                scq_seg_2 = &SCQ[addr_SCQ_map_ft[op2].start_addr];
	                // Set the input's write pointer (old queue structure)
	                input_wr_ptr_2 = ft_sync_queues[op2].wr_ptr;
	            }

	            int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr;
	            int* rd_ptr_1 = &(ft_sync_queues[pc].rd_ptr);
	            int* rd_ptr_2 = &(ft_sync_queues[pc].rd_ptr2);
	            DEEP_PRINT("rd_ptr_1: %d, rd_ptr_2: %d\n", *rd_ptr_1, *rd_ptr_2);
	            // Initialize the loop conditions
	            bool isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
	            bool isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
	            DEEP_PRINT("isEmpty_1: %d, isEmpty_2: %d\n", isEmpty_1, isEmpty_2);
	            // While the formula is not complete, i.e., one of the operands within the SCQ is non-empty
	            while(!isEmpty_1|| !isEmpty_2) {
	                DEEP_PRINT("in loop: isEmpty_1: %d, isEmpty_2: %d\n", isEmpty_1, isEmpty_2);
	                elt_ft_queue_t res = {false,-1};
	                // If both are still non-empty
	                if(!isEmpty_1 && !isEmpty_2) {
	                    elt_ft_queue_t res_1 = pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
	                    elt_ft_queue_t res_2 = pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
	                    if(res_1.v_q && res_2.v_q) res = (elt_ft_queue_t){true, min(res_1.t_q, res_2.t_q)};
	                    else if (!res_1.v_q && !res_2.v_q) res = (elt_ft_queue_t){false, max(res_1.t_q, res_2.t_q)};
	                    else if (res_1.v_q) res = (elt_ft_queue_t){false, res_2.t_q};
	                    else res = (elt_ft_queue_t){false, res_1.t_q};
	                }
	                // If the first operand's is empty
	                else if(isEmpty_1) {
	                    elt_ft_queue_t res_2 = pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
	                    if(!res_2.v_q) res = (elt_ft_queue_t){false, res_2.t_q};
	                }
	                // if the second operand's is empty
	                else {
	                    DEEP_PRINT("YYYY\n");
	                    elt_ft_queue_t res_1 = pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
	                    if(!res_1.v_q) res = (elt_ft_queue_t){false, res_1.t_q};
	                }
	                // If the time is not -1
	                if(res.t_q != -1) {
	                    // Add the new element to the SCQ
	                    add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
	                    // Synchronize the queues
	                    //ft_sync_queues[pc].desired_time_stamp += 1;
	                    ft_sync_queues[pc].desired_time_stamp = res.t_q+1;
	                    // The code is generated as 'make debug', print to log and command
	                    DEBUG_PRINT("PC:%d AND = (%d,%d)\n", pc, res.t_q, res.v_q);
	                } else break;

	                // Update the loop conditions
	                isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
	                isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
	                DEEP_PRINT("endwhile\n");
	            }
	            DEEP_PRINT("endL rd_ptr_1: %d, rd_ptr_2: %d\n", *rd_ptr_1, *rd_ptr_2);
	            DEEP_PRINT("\n\n");
		    progress = 1;
	            break;
	        }

	        //----------------------------------------------------
	        // OP_FT_FT (enventually, time-point:  F[t]
	        //----------------------------------------------------
	        case OP_FT_FT:
		    progress = 1; 
	            break;

	        //----------------------------------------------------
	        // OP_FT_GT (globally, time-point:  G[t]
	        //----------------------------------------------------
	        case OP_FT_GT:
		    progress = 1;
	            break;

	        //----------------------------------------------------
	        // OP_FT_GJ (globally, interval:  G[t1,t2])
	        //----------------------------------------------------
	        case OP_FT_GJ: {
	            DEEP_PRINT("\n");
	            int op1=0, scq_size_rd=0, input_wr_ptr=0;
	            elt_ft_queue_t *scq_seg = NULL;
	            if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
	                op1 = instruction_mem_ft[pc].op1.value;
	                DEEP_PRINT("op1: %d\n", op1);
	                scq_size_rd = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
	                scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
	                DEEP_PRINT("start_addr: %d\n",addr_SCQ_map_ft[op1].start_addr);
	                input_wr_ptr = ft_sync_queues[op1].wr_ptr;
	            }

	            int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr;
	            int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);

	            int lb = get_interval_lb_ft(pc);
	            int ub = get_interval_ub_ft(pc);
	            DEEP_PRINT("pc: %d, lb: %d, ub: %d, rd_ptr: %d, \n",pc,lb,ub, *rd_ptr);
	            //printf("ft_sync_queues[pc].desired_time_stamp: %d\n", ft_sync_queues[pc].desired_time_stamp);
	            while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
	                //printf("not empty, rd_ptr: %d\n", *rd_ptr);
	                elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
	                //printf("input.v_q: %d, t_q: %d\n", input.v_q, input.t_q);
	                ft_sync_queues[pc].desired_time_stamp += 1;
	                // If the verdict is true and we have not seen a previously false verdict
	                if(input.v_q && !ft_sync_queues[pc].pre.v_q) {
	                    // Increment the time-step for synchronizing the queues
	                    ft_sync_queues[pc].m_edge = ft_sync_queues[pc].pre.t_q + 1; // rising edge
	                }
	                // If the verdict is true,
	                if(input.v_q) {
	                    //printf("has true\n");
	                    // and if the time is within the time upper and lower bounds,
	                    if((signed)input.t_q-ft_sync_queues[pc].m_edge >= ub-lb && (signed)input.t_q-ub >= 0) {
	                        // Set res to a true verdict and the time stamp of the input time minus the upper bound
	                        elt_ft_queue_t res = (elt_ft_queue_t){true, input.t_q-ub};
	                        // And add asynchrounous results to the shared connection queue
	                        add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
	                        // The code is generated as 'make debug', print to log and command
	                        DEBUG_PRINT("PC:%d G[%d,%d] = (%d,%d)\n",pc,lb,ub,res.t_q,res.v_q);
	                    }
	                }
	                // If the verdict is false and the time stamp is after the lower bound,
	                else if((signed)input.t_q-lb >= 0) {
	                    // Set res to a false verdict with a timestamp of the input time minus the lower bound,
	                    elt_ft_queue_t res = (elt_ft_queue_t){false, input.t_q-lb};
	                    // And add asynchrounous results to the shared connection queue
	                    add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
	                    // The code is generated as 'make debug', print to log and command
	                    DEBUG_PRINT("PC:%d G[%d,%d] = (%d,%d)\n",pc,lb,ub,res.t_q,res.v_q);
	                }

	                ft_sync_queues[pc].pre = input;
	            }
		    progress = 1;
	            break;
	        }

	        //----------------------------------------------------
	        // OP_FT_UJ (until, interval:  U[t1,t2])
	        //----------------------------------------------------
	        case OP_FT_UJ:
	        {
	            //
	            int op1=0, op2=0, scq_size_rd_1=0, scq_size_rd_2=0, input_wr_ptr_1=0, input_wr_ptr_2=0;

	            // Initialize the scq_sec pointers
	            elt_ft_queue_t *scq_seg_1 = NULL, *scq_seg_2 = NULL;

	            // If the first operand's opcode is a subformula
	            if(instruction_mem_ft[pc].op1.opnd_type == subformula) {
	                // Grab the op1 value from the instruction memory
	                op1 = instruction_mem_ft[pc].op1.value;
	                // Set the SCQ's read pointer for the first operand
	                scq_size_rd_1 = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
	                // Grab the values within the SCQ at the start address
	                scq_seg_1 = &SCQ[addr_SCQ_map_ft[op1].start_addr];
	                // Set the input's write pointer (old queue structure)
	                input_wr_ptr_1 = ft_sync_queues[op1].wr_ptr;
	            }
	            // If the second operand's opcode is a subformula
	            if(instruction_mem_ft[pc].op2.opnd_type == subformula) {
	                // Grab the op2 value from the instruction memory
	                op2 = instruction_mem_ft[pc].op2.value;
	                // Set the SCQ's read pointer for the second operand
	                scq_size_rd_2 = addr_SCQ_map_ft[op2].end_addr - addr_SCQ_map_ft[op2].start_addr;
	                // Grab the values within the SCQ at the start address
	                scq_seg_2 = &SCQ[addr_SCQ_map_ft[op2].start_addr];
	                // Set the input's write pointer (old queue structure)
	                input_wr_ptr_2 = ft_sync_queues[op2].wr_ptr;
	            }

	            int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr;

	            int* rd_ptr_1 = &(ft_sync_queues[pc].rd_ptr);
	            int* rd_ptr_2 = &(ft_sync_queues[pc].rd_ptr2);

	            int lb = get_interval_lb_ft(pc);
	            int ub = get_interval_ub_ft(pc);

	            // Initialize the loop conditions
	            bool isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
	            bool isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);

	            // While the formula is not complete, i.e., one of the operands within the SCQ is non-empty
	            while(!isEmpty_1 && !isEmpty_2) {
	                // Initialize the result as false and with a negative time stamp
	                elt_ft_queue_t res = (elt_ft_queue_t){false, -1};
	                // Pop the first operands's verdict and time stamp from its SCQ
	                elt_ft_queue_t input_1 =  pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
	                // Pop the second operands's verdict and time stamp from its SCQ
	                elt_ft_queue_t input_2 =  pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
	                // Determine which operand has the lower time stamp
	                int tau = min(input_1.t_q, input_2.t_q);
	                // Snychronize the queues with the lower time stamp
	                ft_sync_queues[pc].desired_time_stamp = tau+1;
	                // If there is a true verdict from the synchronization and the other operand's verict is false,
	                if(ft_sync_queues[pc].pre.v_q && !input_2.v_q) {
	                    //
	                    ft_sync_queues[pc].m_edge = ft_sync_queues[pc].pre.t_q;
	                }
	                // If the second operand is true,
	                if(input_2.v_q) {
	                    // Set res to true and the time stamp to the minimum timestamp minus the lower bound
	                    res = (elt_ft_queue_t){true, tau-lb};
	                }
	                // Else, if the first operand is false,
	                else if(!input_1.v_q) {
	                    // Set res to false and the time stamp to the minimum timestamp minus the lower bound
	                    res = (elt_ft_queue_t){false, tau-lb};
	                }
	                // Else, if the minimum timestamp is greater than the difference b/w the upper and lower bounds plus the queue's synch edge
	                else if(tau>=ub-lb+ft_sync_queues[pc].m_edge) {
	                    // Set res to false and the time stamp to be the minimum timestamp minus the upper bound
	                    res = (elt_ft_queue_t){false, tau-ub};
	                }
	                // If the result's time stamp is larger than the previously synch'd result
	                if((signed)res.t_q >= (signed)ft_sync_queues[pc].preResult) {
	                    // And add asynchrounous result to the shared connection queue
	                    add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
	                    // Update the previous synch result
	                    ft_sync_queues[pc].preResult = res.t_q + 1;
	                    // The code is generated as 'make debug', print to log and command
	                    DEBUG_PRINT("PC:%d U[%d,%d] = (%d,%d)\n", pc, lb, ub,res.t_q,res.v_q);
	                }
	                // Update the synchronous queues with the second operand
	                ft_sync_queues[pc].pre = input_2;

	                // Update the loop conditions
	                isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
	                isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
	            }
		    progress = 1;
	            break;
	        }

	        //----------------------------------------------------
	        // OTHERS ARE ILLEGAL INSTRUCTIONS
	        //----------------------------------------------------
	        // IMPLIES = !a0 OR a1 == !(a0 AND !a1)
	        case OP_IMPL:
	        // Equivalent
	        case OP_EQUIVALENT:
	        // OR = !(!a0 AND !a1)
	        case OP_OR:
	        default:
	            DEBUG_PRINT("%d\t[ERR]::FT:: illegal instruction\n",pc);
	            r2u2_errno = 1;
		    progress = 1;
	            break;
	        }
	    }
	    return 0;
	}
}
//-------------------------------------------------------------------
//
//-------------------------------------------------------------------
void read_atomic(int pc, bool* v, unsigned int* t_e) {
    //OPERAND TYPES: (op/opnd_type)
    //direct        = 0b01,  atomic     = 0b00,
    //subformula    = 0b10,  not_set    = 0b11
    operand_t op = instruction_mem_ft[pc].op1;
    *v = atomics_vector[op.value];
    *t_e = t_now;
}

//-------------------------------------------------------------------
//
//--------------------------------------------------------------------
int get_interval_lb_ft(int pc){
    int adr = instruction_mem_ft[pc].adr_interval;
    return interval_mem_ft[adr].lb;
}

//-------------------------------------------------------------------
//
//--------------------------------------------------------------------
int get_interval_ub_ft(int pc){
    int adr = instruction_mem_ft[pc].adr_interval;
    return interval_mem_ft[adr].ub;
}

//-------------------------------------------------------------------
// Function that determines if the SCQ is empty. If it is, then it
//
//-------------------------------------------------------------------
bool isEmpty_cap(int pc, int obNum, elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp) {
    // If unitary operator
    if(obNum==1) {
        switch(instruction_mem_ft[pc].op1.opnd_type) {
            case atomic:
                return false;
            case subformula:
                return isEmpty(scq, size, wr_ptr, rd_ptr, desired_time_stamp);
            case direct:
                return false;
            case not_set:
                return true;
            default:
                printf("operand Error\n");
        }
    }
    // If binary operator
    else if(obNum==2) {
        switch(instruction_mem_ft[pc].op2.opnd_type)
        {
            case atomic:
                return false;
            case subformula:
                return isEmpty(scq, size, wr_ptr, rd_ptr, desired_time_stamp);
            case direct:
                return false;
            case not_set:
                return true;
            default:
                printf("operand Error\n");
        }
    }
    else {
        printf("obNum Error\n");
    }
    return true;
}

//-------------------------------------------------------------------
//
//-------------------------------------------------------------------
elt_ft_queue_t pop_cap(int pc, int obNum, elt_ft_queue_t* scq, int rd_ptr) {
    // If unary operator
    if(obNum==1) {
        switch(instruction_mem_ft[pc].op1.opnd_type)
        {
            case atomic:// return anything you want
                break;
            case subformula:
                //printf("pop: rd_ptr: %d, v_q: %d\n", rd_ptr, scq[rd_ptr].v_q);
                return pop(scq, rd_ptr);
            case direct:
                return (elt_ft_queue_t){instruction_mem_ft[pc].op1.value, t_now};
            case not_set:// return anything you want
                break;
            default:
                printf("operand Error\n");
        }
    }
    // If binary operator
    else if(obNum==2) {
        switch(instruction_mem_ft[pc].op2.opnd_type)
        {
            case atomic:// return anything you want
                break;
            case subformula:
                return pop(scq, rd_ptr);
            case direct:
                return (elt_ft_queue_t){instruction_mem_ft[pc].op2.value, t_now};
            case not_set:// return anything you want
                break;
            default:
                printf("operand Error\n");
        }
    }
    else{
        printf("obNum Error\n");
    }
    return (elt_ft_queue_t){false, -1};
}

