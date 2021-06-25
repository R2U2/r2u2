/*=======================================================================================
** File Name:  TL_update_pt.c
**
** Title:  One execution step for the PT logic engine
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
** Functions Defined:
**	TL_update_pt()
**
** Purpose:
**	execute all TL instructions for the PT engine
**	gets input from atomics_vector and places
** 	outputs into results_pt
**
** Limitations, Assumptions, External Events, and Notes:
**	NA
**
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**
**=====================================================================================*/

#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_pt.h"
#include <stdio.h>
#include <string.h>

bool get_opnd1_pt(int pc);
bool get_opnd1_prev_pt(int pc);
bool get_opnd2_pt(int pc);
bool get_opnd2_prev_pt(int pc);
edge_t opnd1_edge(int pc);
edge_t opnd2_edge(int pc);
interval_bound_t get_interval_lb_pt(int pc);
interval_bound_t get_interval_ub_pt(int pc);
int get_queue_addr_pt(int pc);

//--------------------------------------------------------------------
//	TL_update_pt()
//	main routine to run the PT engine on compiled instructions
//	* executes all instructions
//	* updates results_pt and queues
//--------------------------------------------------------------------
int TL_update_pt(FILE* log_file)
{
    int pc = 0;
    edge_t edge;
    timestamp_t t_s, t_e;
    pt_box_queue_t* bq_addr;

    // put the current output into the previous one
    memcpy(results_pt_prev, results_pt, sizeof(results_pt_t));

    // Sequentially iterate through the program instructions
    for (pc = 0; pc < N_INSTRUCTIONS; pc++) {

        //----------------------------------------------------
        // OP_END_SEQUENCE
        //----------------------------------------------------
        if (instruction_mem_pt[pc].opcode == OP_END_SEQUENCE){
            R2U2_DEBUG_PRINT("PC:%d END_SEQUENCE\n", pc);
            break;
        }

        // Case statement for determining which opcode is currently in the program counter 'pc'
        switch (instruction_mem_pt[pc].opcode) {

        //----------------------------------------------------
        // OP_END
        //----------------------------------------------------
        case OP_END:
            R2U2_DEBUG_PRINT("PC:%d END = (%d,%d)\n", pc, t_now, results_pt[instruction_mem_pt[pc].op1.value]);
            #if R2U2_TL_Formula_Names
            if (aux_str_map[(int)instruction_mem_pt[pc].op2.value] == NULL)
            {
                /* No formula name - use numbered output format */
                fprintf(log_file, "%d:%u,%s\n",
                        (int)instruction_mem_pt[pc].op2.value,t_now,
                        results_pt[instruction_mem_pt[pc].op1.value] ? "T" : "F");
            } else {
                /* Use formula name from aux file */
                fprintf(log_file, "%s:%u,%s\n",
                    aux_str_map[(int)instruction_mem_pt[pc].op2.value],t_now,
                    results_pt[instruction_mem_pt[pc].op1.value] ? "T" : "F");
            }
            #else
            fprintf(log_file, "%d:%u,%s\n",
                    (int)instruction_mem_pt[pc].op2.value,t_now,
                    results_pt[instruction_mem_pt[pc].op1.value] ? "T" : "F");
            #endif
            break;

        //----------------------------------------------------
        // OP_LOD
        //----------------------------------------------------
        case OP_FT_LOD:
            results_pt[pc] = get_opnd1_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d LOAD = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_NOT
        //----------------------------------------------------
        case OP_NOT:
            results_pt[pc] = !get_opnd1_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d NOT = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_AND
        //----------------------------------------------------
        case OP_AND:
            results_pt[pc] = get_opnd1_pt(pc) && get_opnd2_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d AND = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_IMPL
        //----------------------------------------------------
        case OP_IMPL:
            results_pt[pc] = (!get_opnd1_pt(pc)) || get_opnd2_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d IMPL = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_OR
        //----------------------------------------------------
        case OP_OR:
            results_pt[pc] = get_opnd1_pt(pc) || get_opnd2_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d OR = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_EQUIVALENT
        //----------------------------------------------------
        case OP_EQUIVALENT:
            results_pt[pc] = (get_opnd1_pt(pc) == get_opnd2_pt(pc));
            R2U2_DEBUG_PRINT("PC:%d EQ = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_PT_Y  (yesterday)
        //----------------------------------------------------
        case OP_PT_YESTERDAY:
            results_pt[pc] = get_opnd1_prev_pt(pc);
            R2U2_DEBUG_PRINT("PC:%d Y = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_PT_O  (once)  TODO
        //----------------------------------------------------
        case OP_PT_ONCE:
            printf("%d\tinstruction not implemented\n", pc);
            break;

        //----------------------------------------------------
        // OP_PT_H (historically) TODO
        //----------------------------------------------------
        case OP_PT_HISTORICALLY:
            printf("%d\tinstruction not implemented\n", pc);
            break;

        //----------------------------------------------------
        // OP_PT_S ( P since Q )
        //----------------------------------------------------
        case OP_PT_SINCE:
            results_pt[pc] = get_opnd2_pt(pc) || (get_opnd1_pt(pc) && results_pt_prev[pc]);
            R2U2_DEBUG_PRINT("PC:%d S = (%d,%d)\n", pc, t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // metric past time operations: intervals
        //----------------------------------------------------

        //----------------------------------------------------
        // OP_PT_HJ (historically, interval:  H[t1,t2] P
        // Algorithm:  algorithm 7  in [Reinbacher thesis]
        //      box-box-interval
        // 	+ garbage collect
        // Matt C: In 'Performance Aware HW Runtime Monitors,
        //         it looks to be Algorithm 3: Observer for
        //         'invariant previously'
        //----------------------------------------------------
        case OP_PT_HISTORICALLY_INTERVAL:
            // Get the box queue's address
            bq_addr = pt_box_queues + get_queue_addr_pt(pc);

            // Print, I'm assuming for troubleshooting?
            //print_pt_queue(bq_addr);

            //----- Garbage collection ----- //
            // Look into the queue and get the timestamps
            peek_queue_pt(bq_addr, &t_s, &t_e);
            //R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) = %u\n",t_e + get_interval_lb_pt(pc));
            //R2U2_DEBUG_PRINT("(t_e + get_interval_lb_pt(pc)) < t_now = %d\n",(t_e + get_interval_lb_pt(pc)) < t_now);
            
            // If the end time stamp (t_e) is less than the difference
            // between the current time stamp (t_now) and the interval's
            // lower bound, remove the head from the queue.
            if ((t_e + get_interval_lb_pt(pc)) < t_now) {
                //R2U2_DEBUG_PRINT("***** Garbage Collection *****\n");
                //remove_head_queue_pt(bq_addr, &t_s, &t_e);
                remove_tail_queue_pt(bq_addr, &t_s, &t_e);
            }

            //----- Edge Detection and box queue update -----//
            // Determine the edge of the operand: either "rising",
            // "falling", or "none"
            edge = opnd1_edge(pc);
            // If it is the rising edge,
            //if ((t_now == 0) || (edge == rising)) {
            if (edge == rising) {
                //R2U2_DEBUG_PRINT("***** Rising Edge of Op *****\n");
                // Add to the box queue that there was an edge at t_now
                add_queue_pt(bq_addr, t_now, TL_INF);
            }
            // If the edge is falling and the box queue is not empty
            else if ((edge == falling) && !isempty_queue_pt(bq_addr)) {
                //R2U2_DEBUG_PRINT("***** Falling Edge of Op *****\n");
                // Remove the tail of the box queue
                remove_head_queue_pt(bq_addr, &t_s, &t_e);
                //remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) = %u\n",(t_now + get_interval_lb_pt(pc)));
                //R2U2_DEBUG_PRINT("(t_s + get_interval_ub_pt(pc) + 1) = %u\n",(t_s + get_interval_ub_pt(pc) + 1));
                //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)));
                //R2U2_DEBUG_PRINT("(t_now == 0) = %u\n",(t_now == 0));
                //R2U2_DEBUG_PRINT("(get_interval_lb_pt(pc) >= 1) = %u\n",(get_interval_lb_pt(pc) >= 1));
                //R2U2_DEBUG_PRINT("((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)));
                //if ((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) {
                if(((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1))){
                    //R2U2_DEBUG_PRINT("***** Feasibility Check *****\n");
                    add_queue_pt(bq_addr, t_s, t_now - 1);
                }
            }

            // Look into the queue and get the timestamps
            peek_queue_pt(bq_addr, &t_s, &t_e);
            
            //print_pt_queue(bq_addr);
            //R2U2_DEBUG_PRINT("***** Result Calculation *****\n");
            //R2U2_DEBUG_PRINT("t_now = %u\n",t_now);

            //R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) = %u\n",get_interval_ub_pt(pc));
            //R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) = %u\n",get_interval_lb_pt(pc));

            /*
            R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) > t_now = %u\n",get_interval_ub_pt(pc) > t_now);
            if(get_interval_ub_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_s <= 0 = %u\n",t_s <= 0);
            }else{
                R2U2_DEBUG_PRINT("t_s + get_interval_ub_pt(pc) <= t_now = %u\n",t_s + get_interval_ub_pt(pc) <= t_now );
            }
            
            R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) > t_now = %u\n",get_interval_lb_pt(pc) > t_now);
            if(get_interval_lb_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_e >= 0 = %u\n",1);
            }else{
                R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) >= t_now = %u\n",t_e + get_interval_lb_pt(pc) >= t_now);
            }
            */
            //----- Calculate the result -----//
            // If the sum of the start time stamp (t_s) and the lower bound
            // are less than the current timestamp (t_now), AND the sum of
            // the end time stamp (t_e) and the lower bound is greater than
            // the current time stamp (t_now), then the result is true; else,
            // the result is false.
            results_pt[pc] = ((get_interval_ub_pt(pc) > t_now)?(t_s <= 0):(t_s + get_interval_ub_pt(pc) <= t_now )) && ((get_interval_lb_pt(pc) > t_now)?(1):(t_e + get_interval_lb_pt(pc) >= t_now)); 
            
            R2U2_DEBUG_PRINT("PC:%d H[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_PT_OJ (once, interval:  o[t1,t2] P )
        //
        // OJ is implemented as equivalence to
        //   <> = ~[](~phi)
        //----------------------------------------------------
        case OP_PT_ONCE_INTERVAL:

            bq_addr = pt_box_queues + get_queue_addr_pt(pc);
            
            // garbage collection
            peek_queue_pt(bq_addr, &t_s, &t_e);
            //R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) = %u\n",t_e + get_interval_lb_pt(pc));
            //R2U2_DEBUG_PRINT("(t_e + get_interval_lb_pt(pc)) < t_now = %d\n",(t_e + get_interval_lb_pt(pc)) < t_now);
            if ((t_e + get_interval_lb_pt(pc)) < t_now) {
                //R2U2_DEBUG_PRINT("***** Garbage Collection *****\n");
                //remove_head_queue_pt(bq_addr, &t_s, &t_e);
                remove_tail_queue_pt(bq_addr, &t_s, &t_e);
            }

            // for falling edge
            edge = opnd1_edge(pc);
            //if ((t_now == 1) || (edge == falling)) {
            if (edge == falling) {
                //R2U2_DEBUG_PRINT("***** Falling Edge of Op *****\n");
                add_queue_pt(bq_addr, t_now, TL_INF);
            } else if ((edge == rising) && !isempty_queue_pt(bq_addr)) {
                //R2U2_DEBUG_PRINT("***** Rising Edge of Op *****\n");
                remove_head_queue_pt(bq_addr, &t_s, &t_e);
                //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) = %u\n",(t_now + get_interval_lb_pt(pc)));
                //R2U2_DEBUG_PRINT("(t_s + get_interval_ub_pt(pc) + 1) = %u\n",(t_s + get_interval_ub_pt(pc) + 1));
                //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)));
                //R2U2_DEBUG_PRINT("(t_now == 0) = %u\n",(t_now == 0));
                //R2U2_DEBUG_PRINT("(get_interval_lb_pt(pc) >= 1) = %u\n",(get_interval_lb_pt(pc) >= 1));
                //R2U2_DEBUG_PRINT("((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)));
                //if ((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) {
                if(((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1))){
                    //R2U2_DEBUG_PRINT("***** Feasibility Check *****\n");
                    add_queue_pt(bq_addr, t_s, t_now - 1);
                }
            }

            peek_queue_pt(bq_addr, &t_s, &t_e);
            
            //R2U2_DEBUG_PRINT("***** Result Calculation *****\n");
            //R2U2_DEBUG_PRINT("t_now = %u\n",t_now);

            //R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) = %u\n",get_interval_ub_pt(pc));
            //R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) = %u\n",get_interval_lb_pt(pc));

            /*
            R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) > t_now = %u\n",get_interval_ub_pt(pc) > t_now);
            if(get_interval_ub_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_s <= 0 = %u\n",t_s <= 0);
            }else{
                R2U2_DEBUG_PRINT("t_s + get_interval_ub_pt(pc) <= t_now = %u\n",t_s + get_interval_ub_pt(pc) <= t_now );
            }
            
            R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) > t_now = %u\n",get_interval_lb_pt(pc) > t_now);
            if(get_interval_lb_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_e >= 0 = %u\n",1);
            }else{
                R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) >= t_now = %u\n",t_e + get_interval_lb_pt(pc) >= t_now);
            }
            */
            results_pt[pc] = !(((get_interval_ub_pt(pc) > t_now)?(t_s <= 0):(t_s + get_interval_ub_pt(pc) <= t_now )) && ((get_interval_lb_pt(pc) > t_now)?(1):(t_e + get_interval_lb_pt(pc) >= t_now)));
            R2U2_DEBUG_PRINT("PC:%d O[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_PT_SJ (since, interval:  P1 S[t1,t2] P2
        // Algorithm:  algorithm 8  in [Reinbacher thesis]
        // 	+ garbage collect
        //----------------------------------------------------
        case OP_PT_SINCE_INTERVAL:
            bq_addr = pt_box_queues + get_queue_addr_pt(pc);

            // garbage collection
            peek_queue_pt(bq_addr, &t_s, &t_e);
            //R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) = %u\n",t_e + get_interval_lb_pt(pc));
            //R2U2_DEBUG_PRINT("(t_e + get_interval_lb_pt(pc)) < t_now = %d\n",(t_e + get_interval_lb_pt(pc)) < t_now);
            if ((t_e + get_interval_lb_pt(pc)) < t_now) {
                //R2U2_DEBUG_PRINT("***** Garbage Collection *****\n");
                //remove_head_queue_pt(bq_addr, &t_s, &t_e);
                remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                // TODO: THese seem like they should need to be here - but don't?
                // results_pt[pc] = false;
                // break;
            }

            if (get_opnd1_pt(pc)) {
                //R2U2_DEBUG_PRINT("***** Op1 = True *****\n");
                edge = opnd2_edge(pc);
                // falling egde of p2
                //if ((t_now == 0) || (edge == falling)) {
                if (edge == falling) {
                    //R2U2_DEBUG_PRINT("***** Falling Edge of Op2 *****\n");
                    add_queue_pt(bq_addr, t_now, TL_INF);
                } else if ((edge == rising) && !isempty_queue_pt(bq_addr)) {
                    //R2U2_DEBUG_PRINT("***** Rising Edge of Op2 *****\n");
                    remove_head_queue_pt(bq_addr, &t_s, &t_e);
                    //remove_tail_queue_pt(bq_addr, &t_s, &t_e);

                    //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) = %u\n",(t_now + get_interval_lb_pt(pc)));
                    //R2U2_DEBUG_PRINT("(t_s + get_interval_ub_pt(pc) + 1) = %u\n",(t_s + get_interval_ub_pt(pc) + 1));
                    //R2U2_DEBUG_PRINT("(t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)));
                    //R2U2_DEBUG_PRINT("(t_now == 0) = %u\n",(t_now == 0));
                    //R2U2_DEBUG_PRINT("(get_interval_lb_pt(pc) >= 1) = %u\n",(get_interval_lb_pt(pc) >= 1));
                    //R2U2_DEBUG_PRINT("((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)) = %u\n",((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1)));
                    //if ((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) {
                    if(((t_now + get_interval_lb_pt(pc)) >= (t_s + get_interval_ub_pt(pc) + 1)) && ((t_now == 0) || (get_interval_lb_pt(pc) >= 1))){
                        //R2U2_DEBUG_PRINT("***** Feasibility Check *****\n");
                        add_queue_pt(bq_addr, t_s, t_now - 1);
                    }
                } 
            } else { // p1 does not hold
                //R2U2_DEBUG_PRINT("***** Op1 = False *****\n");
                if (get_opnd2_pt(pc)) {
                    // TODO: Rechability at t_now = 0?
                    //R2U2_DEBUG_PRINT("***** Op2 = True *****\n");
                    remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                    add_queue_pt(bq_addr, 0, t_now - 1);
                } else {
                    //R2U2_DEBUG_PRINT("***** Op2 = False *****\n");
                    remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                    add_queue_pt(bq_addr, 0, TL_INF);
                }
            }
            
            peek_queue_pt(bq_addr, &t_s, &t_e);
            //R2U2_DEBUG_PRINT("***** Result Calculation *****\n");
            //R2U2_DEBUG_PRINT("t_now = %u\n",t_now);

            //R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) = %u\n",get_interval_ub_pt(pc));
            //R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) = %u\n",get_interval_lb_pt(pc));

            /*
            //R2U2_DEBUG_PRINT("get_interval_ub_pt(pc) > t_now = %u\n",get_interval_ub_pt(pc) > t_now);
            if(get_interval_ub_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_s > 0 = %u\n",t_s > 0);
            }else{
                R2U2_DEBUG_PRINT("t_s + get_interval_ub_pt(pc) > t_now = %u\n",t_s + get_interval_ub_pt(pc) > t_now );
            }
            
            R2U2_DEBUG_PRINT("get_interval_lb_pt(pc) > t_now = %u\n",get_interval_lb_pt(pc) > t_now);
            if(get_interval_lb_pt(pc) > t_now){
                R2U2_DEBUG_PRINT("t_e < 0 = %u\n",0);
            }else{
                R2U2_DEBUG_PRINT("t_e + get_interval_lb_pt(pc) < t_now = %u\n",t_e + get_interval_lb_pt(pc) < t_now);
            }
            */
            results_pt[pc] = ((get_interval_ub_pt(pc) > t_now)?(t_s > 0):(t_s + get_interval_ub_pt(pc) > t_now )) || ((get_interval_lb_pt(pc) > t_now)?(0):(t_e + get_interval_lb_pt(pc) < t_now)); 

            R2U2_DEBUG_PRINT("PC:%d S[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // operators on time points
        //----------------------------------------------------

        //----------------------------------------------------
        // OP_PT_HT (historically, time point  H[t] P )
        //----------------------------------------------------
        case OP_PT_HISTORICALLY_TIMEPOINT:
            edge = opnd1_edge(pc);
            if (edge == rising) {
                results_pt_rising[pc] = t_now;
            } else if ((edge == falling) || (t_now == 1)) {
                results_pt_rising[pc] = TL_INF;
            }

            results_pt[pc] = (t_now >= (results_pt_rising[pc] + get_interval_lb_pt(pc)));
            R2U2_DEBUG_PRINT("PC:%d H[%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OP_PT_OT (once, time point  O[t] P )
        //
        // OJ is implemented as equivalence to
        //   <> = ~[](~phi)
        //----------------------------------------------------
        case OP_PT_ONCE_TIMEPOINT:
            edge = opnd1_edge(pc);
            if ((t_now == 1) || (edge == falling)) {
                results_pt_rising[pc] = t_now;
            } else {
                if (edge == rising) {
                    results_pt_rising[pc] = TL_INF;
                }
            }

            results_pt[pc] = !(t_now >= (results_pt_rising[pc] + get_interval_lb_pt(pc)));
            R2U2_DEBUG_PRINT("PC:%d O[%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), t_now, results_pt[pc]);
            break;

        //----------------------------------------------------
        // OTHERS ARE ILLEGAL INSTRUCTIONS
        //----------------------------------------------------
        default:
            printf("%d\t[ERR]::PT:: illegal instruction\n", pc);
            r2u2_errno = 1;
            break;
        }
    }

    return 0;
}

//--------------------------------------------------------------------
//  get_opnd1_pt
//	get 1st operand from instruction at pc
//	returns Boolean
//--------------------------------------------------------------------
bool get_opnd1_pt(int pc)
{

    bool res;

    operand_t op1 = instruction_mem_pt[pc].op1;

    switch (op1.opnd_type) {
    case direct:
        res = op1.value;
        break;

    case atomic:
        res = atomics_vector[op1.value];
        break;

    case subformula:
        res = results_pt[op1.value];
        break;

    case not_set:
        res = 0;
        break;
    }

    return res;
}

//--------------------------------------------------------------------
//  get_opnd1_prev_pt
//	get previous value of 1nd operand from instruction at pc
//	returns Boolean
// TODO: should be merged with get_opnd1_pt
//--------------------------------------------------------------------
bool get_opnd1_prev_pt(int pc)
{

    bool res;

    operand_t op1 = instruction_mem_pt[pc].op1;

    switch (op1.opnd_type) {
    case direct:
        res = op1.value;
        break;

    case atomic:
        res = atomics_vector_prev[op1.value];
        break;

    case subformula:
        res = results_pt_prev[op1.value];
        break;

    case not_set:
        res = 0;
        break;
    }
    return res;
}

//--------------------------------------------------------------------
//  get_opnd2_pt
//	get 1st operand from instruction at pc
//	returns Boolean
//--------------------------------------------------------------------
bool get_opnd2_pt(int pc)
{

    bool res;

    operand_t op2 = instruction_mem_pt[pc].op2;

    switch (op2.opnd_type) {
    case direct:
        res = op2.value;
        break;

    case atomic:
        res = atomics_vector[op2.value];
        break;

    case subformula:
        res = results_pt[op2.value];
        break;

    case not_set:
        res = 0;
        break;
    }

    return res;
}

//--------------------------------------------------------------------
//  get_opnd2_prev_pt
//	get 1st operand from instruction at pc
//	returns Boolean
//--------------------------------------------------------------------
bool get_opnd2_prev_pt(int pc)
{

    bool res;

    operand_t op2 = instruction_mem_pt[pc].op2;

    switch (op2.opnd_type) {
    case direct:
        res = op2.value;
        break;

    case atomic:
        res = atomics_vector_prev[op2.value];
        break;

    case subformula:
        res = results_pt_prev[op2.value];
        break;

    case not_set:
        res = 0;
        break;
    }

    return res;
}

//--------------------------------------------------------------------
//  opnd1_egde
//	get "none","rising", or "falling" information from operand 1
//--------------------------------------------------------------------
edge_t opnd1_edge(int pc)
{

    bool v;
    bool v_p;
    operand_t op1 = instruction_mem_pt[pc].op1;
    switch (op1.opnd_type) {
    case direct:
        v = false;
        v_p = false;
        break;

    case atomic:
        v = atomics_vector[op1.value];
        v_p = atomics_vector_prev[op1.value];
        break;

    case subformula:
        v = results_pt[op1.value];
        v_p = results_pt_prev[op1.value];
        break;
    case not_set:
        v = false;
        v_p = false;
        break;
    }
    // At t_now = 0, we need either a rising or falling edge.
    // v determines the edge
    if (v && (!v_p || !t_now)) {
        return rising;
    }
    if (!v && (v_p || !t_now)) {
        return falling;
    }
    return none;
}

//--------------------------------------------------------------------
//  opnd2_egde
//	get "none","rising", or "falling" information from operand 2
// TODO: should be merged with opnd1_edge
//--------------------------------------------------------------------
edge_t opnd2_edge(int pc)
{

    bool v;
    bool v_p;
    operand_t op2 = instruction_mem_pt[pc].op2;

    switch (op2.opnd_type) {
    case direct:
        v = false;
        v_p = false;
        break;

    case atomic:
        v = atomics_vector[op2.value];
        v_p = atomics_vector_prev[op2.value];
        break;

    case subformula:
        v = results_pt[op2.value];
        v_p = results_pt_prev[op2.value];
        break;

    case not_set:
        v = false;
        v_p = false;
        break;
    }
    // At t_now = 0, we need either a rising or falling edge.
    // v determines the edge
    if (v && (!v_p || !t_now)) {
        return rising;
    }
    if (!v && (v_p || !t_now)) {
        return falling;
    }
    return none;
}

//--------------------------------------------------------------------
// get_interval_lb_pt
//	get the lower bound (or time point) from temporal information
//	for instruction at pc
//--------------------------------------------------------------------
interval_bound_t get_interval_lb_pt(int pc)
{

    int adr = instruction_mem_pt[pc].adr_interval;

    // TODO: check ranges to rule out FT compiler errors

    return interval_mem_pt[adr].lb;
}

//--------------------------------------------------------------------
// get_interval_ub_pt
//	get the upper bound from temporal information
//	for instruction at pc
//--------------------------------------------------------------------
interval_bound_t get_interval_ub_pt(int pc)
{

    int adr = instruction_mem_pt[pc].adr_interval;

    // TODO: check ranges to rule out FT compiler errors

    return interval_mem_pt[adr].ub;
}

//--------------------------------------------------------------------
// get_queue_addr_pt
//	get index of queue address into queue memory
//	for instruction at pc
//--------------------------------------------------------------------
int get_queue_addr_pt(int pc)
{

    return instruction_mem_pt[pc].adr_interval;
}
