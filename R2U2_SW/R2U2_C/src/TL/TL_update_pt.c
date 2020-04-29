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
    bool res;
    bool opnd;
    bool opnd1;
    bool opnd2;
    edge_t edge;
    unsigned int t_s;
    unsigned int t_e;
    pt_box_queue_t* bq_addr;

    // put the current output into the previous one
    memcpy(results_pt_prev, results_pt, sizeof(results_pt_t));

    // Sequentially iterate through the program instructions
    for (pc = 0; pc < N_INSTRUCTIONS; pc++) {

        // Case statement for determining which opcode is currently in the program counter 'pc'
        switch (instruction_mem_pt[pc].opcode) {
        //----------------------------------------------------
        // OP_END_SEQUENCE
        //----------------------------------------------------
        case OP_END_SEQUENCE:
            DEBUG_PRINT("PC:%d END_SEQUENCE\n", pc);
            break;

        //----------------------------------------------------
        // OP_END
        //----------------------------------------------------
        case OP_END:
            DEBUG_PRINT("PC:%d END = (%d,%d)\n", pc, t_now, res);
            fprintf(log_file, "%d:%d,%s\n", (int)instruction_mem_pt[pc].op2.value, t_now, res ? "T" : "F");
            break;

        //----------------------------------------------------
        // OP_LOD
        //----------------------------------------------------
        case OP_FT_LOD:
            opnd = get_opnd1_pt(pc);
            res = opnd;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d LOAD = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_NOT
        //----------------------------------------------------
        case OP_NOT:
            opnd = get_opnd1_pt(pc);
            res = !opnd;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d NOT = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_AND
        //----------------------------------------------------
        case OP_AND:
            opnd1 = get_opnd1_pt(pc);
            opnd2 = get_opnd2_pt(pc);
            res = opnd1 & opnd2;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d AND = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_IMPL
        //----------------------------------------------------
        case OP_IMPL:
            opnd1 = get_opnd1_pt(pc);
            opnd2 = get_opnd2_pt(pc);
            res = !opnd1 | opnd2;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d IMPL = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_OR
        //----------------------------------------------------
        case OP_OR:
            opnd1 = get_opnd1_pt(pc);
            opnd2 = get_opnd2_pt(pc);
            res = opnd1 | opnd2;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d OR = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_EQUIVALENT
        //----------------------------------------------------
        case OP_EQUIVALENT:
            opnd1 = get_opnd1_pt(pc);
            opnd2 = get_opnd2_pt(pc);
            res = (opnd1 == opnd2);
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d EQ = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_PT_Y  (yesterday)
        //----------------------------------------------------
        case OP_PT_Y:
            opnd1 = get_opnd1_prev_pt(pc);
            res = opnd1;
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d Y = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // OP_PT_O  (once)  TODO
        //----------------------------------------------------
        case OP_PT_O:
            printf("%d\tinstruction not implemented\n", pc);
            break;

        //----------------------------------------------------
        // OP_PT_H (historically) TODO
        //----------------------------------------------------
        case OP_PT_H:
            printf("%d\tinstruction not implemented\n", pc);
            break;

        //----------------------------------------------------
        // OP_PT_S ( P since Q )
        //----------------------------------------------------
        case OP_PT_S:
            opnd1 = get_opnd1_pt(pc);
            opnd2 = get_opnd2_pt(pc);
            res = opnd2 | (opnd1 & results_pt_prev[pc]);
            results_pt[pc] = res;
            DEBUG_PRINT("PC:%d S = (%d,%d)\n", pc, t_now, res);
            break;

        //----------------------------------------------------
        // metric past time operations: intervals
        //----------------------------------------------------

        //----------------------------------------------------
        // OP_PT_HJ (historically, interval:  H[t1,t2] P
        // Algorithm:  algorithm 7  in [Reinbacher thesis]
        //      box-box-interval
        // 	+ garbage collect
        //----------------------------------------------------
        case OP_PT_HJ:

            bq_addr = pt_box_queues + get_queue_addr_pt(pc);
            print_pt_queue(bq_addr);
            // garbage collection
            peek_queue_pt(bq_addr, &t_s, &t_e);

            if (t_e < t_now - get_interval_lb_pt(pc)) {
                remove_head_queue_pt(bq_addr, &t_s, &t_e);
            }

            // for rising edge
            edge = opnd1_edge(pc);
            if (edge == rising) {
                add_queue_pt(bq_addr, t_now, TL_INF);
            }

            // for falling edge
            if ((edge == falling) && !isempty_queue_pt(bq_addr)) {
                remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                // feasibility check
                //   feasible((t_s,n-1),n,J)
                if (((t_now - 1) - t_s) >= (get_interval_ub_pt(pc) - get_interval_lb_pt(pc))) {
                    add_queue_pt(bq_addr, t_s, t_now - 1);
                }
            }

            peek_queue_pt(bq_addr, &t_s, &t_e);

            res = (t_s + get_interval_lb_pt(pc) <= t_now ) & (t_e + get_interval_lb_pt(pc) >= t_now);
            results_pt[pc] = res;

            DEBUG_PRINT("PC:%d H[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, res);
            break;

        //----------------------------------------------------
        // OP_PT_OJ (once, interval:  o[t1,t2] P )
        //
        // OJ is implemented as equivalence to
        //   <> = ~[](~phi)
        //----------------------------------------------------
        case OP_PT_OJ:

            bq_addr = pt_box_queues + get_queue_addr_pt(pc);

            // garbage collection
            peek_queue_pt(bq_addr, &t_s, &t_e);
            if (t_e < t_now - get_interval_lb_pt(pc)) {
                remove_head_queue_pt(bq_addr, &t_s, &t_e);
            }

            // for falling edge
            edge = opnd1_edge(pc);
            if ((t_now == 1) || (edge == falling)) {
                add_queue_pt(bq_addr, t_now, TL_INF);
            } else {
                // for rising edge
                if ((edge == rising) && !isempty_queue_pt(bq_addr)) {
                    remove_tail_queue_pt(bq_addr, &t_s, &t_e);
                    // feasibility check
                    //   feasible((t_s,n-1),n,J)
                    if (((t_now - 1) - t_s) >= (get_interval_ub_pt(pc) - get_interval_lb_pt(pc))) {
                        add_queue_pt(bq_addr, t_s, t_now - 1);
                    }
                }
            }

            peek_queue_pt(bq_addr, &t_s, &t_e);

            res = !((t_s + get_interval_ub_pt(pc) <= t_now) & (t_e + get_interval_lb_pt(pc) >= t_now));
            results_pt[pc] = res;

            DEBUG_PRINT("PC:%d O[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, res);
            break;

        //----------------------------------------------------
        // OP_PT_SJ (since, interval:  P1 S[t1,t2] P2
        // Algorithm:  algorithm 8  in [Reinbacher thesis]
        // 	+ garbage collect
        //----------------------------------------------------
        case OP_PT_SJ:
            bq_addr = pt_box_queues + get_queue_addr_pt(pc);

            // garbage collection
            peek_queue_pt(bq_addr, &t_s, &t_e);

            if (t_e < t_now - get_interval_lb_pt(pc)) {
                remove_head_queue_pt(bq_addr, &t_s, &t_e);
            }

            opnd1 = get_opnd1_pt(pc);
            if (opnd1) {
                edge = opnd2_edge(pc);
                // falling egde of p2
                if (edge == falling) {
                    add_queue_pt(bq_addr, t_now, TL_INF);
                }

                // for rising edge
                if ((edge == rising) && !isempty_queue_pt(bq_addr)) {
                    remove_tail_queue_pt(bq_addr, &t_s, &t_e);

                    // feasibility check
                    //   feasible((t_s,n-1),n,J)
                    if (((t_now - 1) - t_s) >= (get_interval_ub_pt(pc) - get_interval_lb_pt(pc))) {
                        add_queue_pt(bq_addr, t_s, t_now - 1);
                    }
                }
            } else { // p1 does not hold

                opnd2 = get_opnd2_pt(pc);
                if (opnd2) {
                    add_queue_pt(bq_addr, 0, t_now - 1);
                } else {
                    add_queue_pt(bq_addr, 0, TL_INF);
                }
            }

            peek_queue_pt(bq_addr, &t_s, &t_e);
            res = ((t_s + get_interval_ub_pt(pc) > t_now) & (t_e +  get_interval_lb_pt(pc) < t_now));
            results_pt[pc] = res;

            DEBUG_PRINT("PC:%d S[%d,%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), get_interval_ub_pt(pc), t_now, res);
            break;

        //----------------------------------------------------
        // operators on time points
        //----------------------------------------------------

        //----------------------------------------------------
        // OP_PT_HT (historically, time point  H[t] P )
        //----------------------------------------------------
        case OP_PT_HT:
            edge = opnd1_edge(pc);
            if (edge == rising) {
                results_pt_rising[pc] = t_now;
            } else {
                if ((t_now == 1) || edge == falling) {
                    results_pt_rising[pc] = TL_INF;
                }
            }

            res = (t_now >= results_pt_rising[pc] + get_interval_lb_pt(pc));
            results_pt[pc] = res;

            DEBUG_PRINT("PC:%d H[%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), t_now, res);
            break;

        //----------------------------------------------------
        // OP_PT_OT (once, time point  O[t] P )
        //
        // OJ is implemented as equivalence to
        //   <> = ~[](~phi)
        //----------------------------------------------------
        case OP_PT_OT:
            edge = opnd1_edge(pc);
            if ((t_now == 1) || (edge == falling)) {
                results_pt_rising[pc] = t_now;
            } else {
                if (edge == rising) {
                    results_pt_rising[pc] = TL_INF;
                }
            }

            res = !(t_now >= results_pt_rising[pc] + get_interval_lb_pt(pc));
            results_pt[pc] = res;

            DEBUG_PRINT("PC:%d O[%d] = (%d,%d)\n", pc, get_interval_lb_pt(pc), t_now, res);
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
        //TRACE_OPND_PT(printf("opnd: atomic[%d]= %d\n",op1.value,res);)
        break;

    case subformula:
        res = results_pt[op1.value];
        //TRACE_OPND_PT(printf("opnd: subformula[%d]= %d\n",op1.value,res);)
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
        //TRACE_OPND_PT(printf("opnd: atomic[%d]= %d\n",op1.value,res);)
        break;

    case subformula:
        res = results_pt_prev[op1.value];
        //TRACE_OPND_PT(printf("opnd: subformula[%d]= %d\n",op1.value,res);)
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
        //TRACE_OPND_PT(printf("opnd: atomic[%d]= %d\n",op2.value,res);)
        break;

    case subformula:
        res = results_pt[op2.value];
        //TRACE_OPND_PT(printf("opnd: subformula[%d]= %d\n",op2.value,res);)
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
        //TRACE_OPND_PT(printf("opnd: atomic[%d]= %d\n",op2.value,res);)
        break;

    case subformula:
        res = results_pt_prev[op2.value];
        //TRACE_OPND_PT(printf("opnd: subformula[%d]= %d\n",op2.value,res);)
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

    //JSC 0913 if (v & !v_p){
    if (v & (!v_p || !t_now)) {
        return rising;
    }
    if (!v & v_p) {
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

    // 0913-- initialization
    if (v & (!v_p || !t_now)) {
        return rising;
    }
    if (!v & v_p) {
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
