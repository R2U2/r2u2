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
**	TL_update_ft()
**
** Purpose:
**	execute all TL instructions for the FT engine
**	gets input from atomics_vector and places
** 	outputs into results_ft
**
** Limitations, Assumftions, External Events, and Notes:
**	NA
**
**
** Modification History:
**   Date | Author | Descriftion
**   ---------------------------
** Stefan Jaksic, Patrick Moosbruger
** Apr.14.2019 | Pei | Clean up the code and rewrite the function
**=====================================================================================*/


#include <stdio.h>
#include <string.h>
#include "TL_observers.h"
#include "TL_queue_ft.h"

#define max(x,y) (((x)>(y))?(x):(y))
#define min(x,y) (((x)<(y))?(x):(y)) 

/**
*   get_interval_lb_ft
*	get the lower bound (or time point) from temporal information
*	for instruction at pc
*/
inline int	get_interval_lb_ft(int pc);

/**
*   get_interval_ub_ft
*	get the upper bound (or time point) from temporal information
*	for instruction at pc
*/
inline int	get_interval_ub_ft(int pc);

elt_ft_queue_t pop_cap(int pc, int obNum, elt_ft_queue_t* scq, int rd_ptr);

bool isEmpty_cap(int pc, int ObNum, elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp);


//--------------------------------------------------------------------
//	TL_update_ft()
//	main routine to run the PT engine on compiled instructions
//	* executes all instructions
//	* updates results_ft and queues
//--------------------------------------------------------------------
int TL_update_ft(FILE *fp, FILE *fp2){

	int  		pc=0;
	int 		stop = 0;


	for (pc=0; pc< N_INSTRUCTIONS;pc++){

		if (stop) break;

		switch(instruction_mem_ft[pc].opcode){

		//----------------------------------------------------
		// OP_END, OP_END_SEQUENCE
		//----------------------------------------------------
		case OP_END:
		case OP_END_SEQUENCE: {			
			int op1=0, scq_size_rd=0, input_wr_ptr=0;
			elt_ft_queue_t *scq_seg;
			if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
				op1 = instruction_mem_ft[pc].op1.value;
				scq_size_rd = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
				scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
				input_wr_ptr = ft_sync_queues[op1].wr_ptr;
			} 	

			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);
			while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
				elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
				elt_ft_queue_t res = {input.v_q,input.t_q};
				add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
				ft_sync_queues[pc].desired_time_stamp = input.t_q+1;
				fprintf(fp2, "PC:%d END = [%d,%s]\n", pc, res.t_q, res.v_q?"True":"False");
				printf("PC:%d END = (%d,%d)\n", pc, res.t_q, res.v_q);
			}
			stop=1;
			break;
		}

		//----------------------------------------------------
		// OP_FT_LOD
		//----------------------------------------------------
		case OP_FT_LOD: {
			//Retrieve Input Data
			bool v;
			unsigned int t_e;
			read_atomic(pc, &v, &t_e);
			elt_ft_queue_t newData = {v,t_e};
			//Add Asynchrounous Results to Queue
			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, newData, &(ft_sync_queues[pc].wr_ptr));
			//add_and_aggregate_queue_ft(&ft_sync_queues[pc], v, t_e);
			fprintf(fp2, "PC:%d LOAD = [%d,%s]\n", pc, t_e, v?"True":"False");
			printf("PC:%d LOAD = (%d,%d)\n", pc, t_e, v);
			break;
		}

		//----------------------------------------------------
		// OP_FT_NOT
		//----------------------------------------------------
		case OP_FT_NOT: {
			int op1=0, scq_size_rd=0, input_wr_ptr=0;
			elt_ft_queue_t *scq_seg;
			if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
				op1 = instruction_mem_ft[pc].op1.value;
				scq_size_rd = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;	
				scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
				input_wr_ptr = ft_sync_queues[op1].wr_ptr;
			} 	
			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);
			while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
				//Get the Next Input
				elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
				elt_ft_queue_t res = {!input.v_q,input.t_q};
				add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));

				fprintf(fp2, "PC:%d NOT = [%d,%s]\n", pc, res.t_q, res.v_q?"True":"False");
				printf("PC:%d NOT = (%d,%d)\n", pc, res.t_q, res.v_q);

				//Update desired time stamp
				ft_sync_queues[pc].desired_time_stamp = input.t_q+1;
			}

			break;
		}

		//----------------------------------------------------
		// OP_FT_AND
		//----------------------------------------------------

		case OP_FT_AND: {
			int op1=0, op2=0, scq_size_rd_1=0, scq_size_rd_2=0, input_wr_ptr_1=0, input_wr_ptr_2=0;
			elt_ft_queue_t *scq_seg_1, *scq_seg_2;
			if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
				op1 = instruction_mem_ft[pc].op1.value;
				scq_size_rd_1 = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
				scq_seg_1 = &SCQ[addr_SCQ_map_ft[op1].start_addr];
				input_wr_ptr_1 = ft_sync_queues[op1].wr_ptr;
			}
			if(instruction_mem_ft[pc].op2.opnd_type==subformula) {
				op2 = instruction_mem_ft[pc].op2.value;
				scq_size_rd_2 = addr_SCQ_map_ft[op2].end_addr-addr_SCQ_map_ft[op2].start_addr;
				scq_seg_2 = &SCQ[addr_SCQ_map_ft[op2].start_addr];
				input_wr_ptr_2 = ft_sync_queues[op2].wr_ptr;
			}

			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			int* rd_ptr_1 = &(ft_sync_queues[pc].rd_ptr);
			int* rd_ptr_2 = &(ft_sync_queues[pc].rd_ptr2);	

			bool isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
			bool isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
			while(!isEmpty_1|| !isEmpty_2) {
				elt_ft_queue_t res = {false,-1};
				if(!isEmpty_1 && !isEmpty_2) {
					elt_ft_queue_t res_1 = pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
					elt_ft_queue_t res_2 = pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
					if(res_1.v_q && res_2.v_q) res = (elt_ft_queue_t){true, min(res_1.t_q, res_2.t_q)};
					else if (!res_1.v_q && !res_2.v_q) res = (elt_ft_queue_t){false, max(res_1.t_q, res_2.t_q)};
					else if (res_1.v_q) res = (elt_ft_queue_t){false, res_2.t_q};
					else res = (elt_ft_queue_t){false, res_1.t_q};
				} else if(isEmpty_1) {
					elt_ft_queue_t res_2 = pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
					if(!res_2.v_q) res = (elt_ft_queue_t){false, res_2.t_q};
				} else {
					elt_ft_queue_t res_1 = pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
					if(!res_1.v_q) res = (elt_ft_queue_t){false, res_1.t_q};
				}
				
				if(res.t_q != -1) {
					add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
					ft_sync_queues[pc].desired_time_stamp += 1;
					fprintf(fp2, "PC:%d AND = [%d,%s]\n", pc, res.t_q, res.v_q?"True":"False");
					printf("PC:%d AND = (%d,%d)\n", pc, res.t_q, res.v_q);
				} else break;
				isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
				isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
			}

			break;
		}

		//----------------------------------------------------
		// OP_FT_FT (enventually, time-point:  F[t]
		//----------------------------------------------------
		case OP_FT_FT:
			break;

		//----------------------------------------------------
		// OP_FT_GT (globally, time-point:  G[t]
		//----------------------------------------------------
		//----------------------------------------------------
		// OP_FT_GJ (globally, interval:  G[t1,t2])
		//----------------------------------------------------
		
		case OP_FT_GT: 
		break;

		case OP_FT_GJ: {
			int op1=0, scq_size_rd=0, input_wr_ptr=0;
			elt_ft_queue_t *scq_seg;
			if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
				op1 = instruction_mem_ft[pc].op1.value;
				scq_size_rd = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;	
				scq_seg = &SCQ[addr_SCQ_map_ft[op1].start_addr];
				input_wr_ptr = ft_sync_queues[op1].wr_ptr;
			}

			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			int* rd_ptr = &(ft_sync_queues[pc].rd_ptr);

			int lb = get_interval_lb_ft(pc);
			int ub = get_interval_ub_ft(pc);
			// printf("%d,%d,%d\n",pc,lb,ub);
			while(!isEmpty_cap(pc, 1, scq_seg, scq_size_rd, input_wr_ptr, rd_ptr, ft_sync_queues[pc].desired_time_stamp)) {
				elt_ft_queue_t input = pop_cap(pc, 1, scq_seg, *rd_ptr);
				ft_sync_queues[pc].desired_time_stamp += 1;
				if(input.v_q && !ft_sync_queues[pc].pre.v_q) {
					ft_sync_queues[pc].m_edge = ft_sync_queues[pc].pre.t_q + 1; // rising edge
				}
				if(input.v_q) {
					if((signed)input.t_q-ft_sync_queues[pc].m_edge >= ub-lb && (signed)input.t_q-ub >= 0) {
						elt_ft_queue_t res = (elt_ft_queue_t){true, input.t_q-ub};
						add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
						fprintf(fp2, "PC:%d G[%d,%d] = [%d,%s]\n", pc, lb, ub, res.t_q, res.v_q?"True":"False");
						printf("PC:%d G[%d,%d] = (%d,%d)\n",pc,lb,ub,res.t_q,res.v_q);
					}
				} else if((signed)input.t_q-lb >= 0) {
					elt_ft_queue_t res = (elt_ft_queue_t){false, input.t_q-lb};
					add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
					fprintf(fp2, "PC:%d G[%d,%d] = [%d,%s]\n", pc, lb, ub, res.t_q, res.v_q?"True":"False");
					printf("PC:%d G[%d,%d] = (%d,%d)\n",pc,lb,ub,res.t_q,res.v_q);
				}
				ft_sync_queues[pc].pre = input;		
			}

			break;
		}
		
		//----------------------------------------------------
		// OP_FT_UJ (until, interval:  U[t1,t2])
		//----------------------------------------------------
		case OP_FT_UJ: {
			int op1=0, op2=0, scq_size_rd_1=0, scq_size_rd_2=0, input_wr_ptr_1=0, input_wr_ptr_2=0;
			elt_ft_queue_t *scq_seg_1, *scq_seg_2;
			if(instruction_mem_ft[pc].op1.opnd_type==subformula) {
				op1 = instruction_mem_ft[pc].op1.value;
				scq_size_rd_1 = addr_SCQ_map_ft[op1].end_addr-addr_SCQ_map_ft[op1].start_addr;
				scq_seg_1 = &SCQ[addr_SCQ_map_ft[op1].start_addr];
				input_wr_ptr_1 = ft_sync_queues[op1].wr_ptr;
			}
			if(instruction_mem_ft[pc].op2.opnd_type==subformula) {
				op2 = instruction_mem_ft[pc].op2.value;
				scq_size_rd_2 = addr_SCQ_map_ft[op2].end_addr-addr_SCQ_map_ft[op2].start_addr;
				scq_seg_2 = &SCQ[addr_SCQ_map_ft[op2].start_addr];
				input_wr_ptr_2 = ft_sync_queues[op2].wr_ptr;
			}
		
			int scq_size_wr = addr_SCQ_map_ft[pc].end_addr-addr_SCQ_map_ft[pc].start_addr; 
			
			int* rd_ptr_1 = &(ft_sync_queues[pc].rd_ptr);
			int* rd_ptr_2 = &(ft_sync_queues[pc].rd_ptr2);

			int lb = get_interval_lb_ft(pc);
			int ub = get_interval_ub_ft(pc);

			bool isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
			bool isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
			
			while(!isEmpty_1 && !isEmpty_2) {
				elt_ft_queue_t res = (elt_ft_queue_t){false, -1};
				elt_ft_queue_t input_1 =  pop_cap(pc, 1, scq_seg_1, *rd_ptr_1);
				elt_ft_queue_t input_2 =  pop_cap(pc, 2, scq_seg_2, *rd_ptr_2);
				int tau = min(input_1.t_q, input_2.t_q);
				ft_sync_queues[pc].desired_time_stamp = tau+1;
				if(ft_sync_queues[pc].pre.v_q && !input_2.v_q) {
					ft_sync_queues[pc].m_edge = ft_sync_queues[pc].pre.t_q;
				}
				if(input_2.v_q) res = (elt_ft_queue_t){true, tau-lb};
				else if(!input_1.v_q) res = (elt_ft_queue_t){false, tau-lb};
				else if(tau>=ub-lb+ft_sync_queues[pc].m_edge) res = (elt_ft_queue_t){false, tau-ub};
				if((signed)res.t_q >= (signed)ft_sync_queues[pc].preResult) {
					add(&SCQ[addr_SCQ_map_ft[pc].start_addr], scq_size_wr, res, &(ft_sync_queues[pc].wr_ptr));
					ft_sync_queues[pc].preResult = res.t_q + 1;
					fprintf(fp2, "PC:%d U[%d,%d] = [%d,%s]\n", pc, lb, ub, res.t_q, res.v_q?"True":"False");
					printf("PC:%d U[%d,%d] = (%d,%d)\n", pc, lb, ub,res.t_q,res.v_q);
				}
				ft_sync_queues[pc].pre = input_2;
				isEmpty_1 = isEmpty_cap(pc, 1, scq_seg_1, scq_size_rd_1, input_wr_ptr_1, rd_ptr_1, ft_sync_queues[pc].desired_time_stamp);
				isEmpty_2 = isEmpty_cap(pc, 2, scq_seg_2, scq_size_rd_2, input_wr_ptr_2, rd_ptr_2, ft_sync_queues[pc].desired_time_stamp);
			}
			break;
		}

		//----------------------------------------------------
		// OTHERS ARE ILLEGAL INSTRUCTIONS
		//----------------------------------------------------
		case OP_IMPL:
		case OP_EQUIVALENT:
		case OP_OR:
		default:
			printf("%d\t[ERR]::FT:: illegal instruction\n",pc);
			r2u2_errno = 1;
			break;
		}
	}
	return 0;
}


void read_atomic(int pc, bool* v, unsigned int* t_e) {
	//OPERAND TYPES: (op/opnd_type)
	//direct 		= 0b01,  atomic 	= 0b00,
	//subformula 	= 0b10,  not_set 	= 0b11
	operand_t op = instruction_mem_ft[pc].op1;
	*v = atomics_vector[op.value];
	*t_e = t_now;
}


//--------------------------------------------------------------------
int	get_interval_lb_ft(int pc){
	int adr = instruction_mem_ft[pc].adr_interval;
	return interval_mem_ft[adr].lb;
}

//--------------------------------------------------------------------
int	get_interval_ub_ft(int pc){
	int adr = instruction_mem_ft[pc].adr_interval;
	return interval_mem_ft[adr].ub;
}

//-------------------------------------------------------------------
bool isEmpty_cap(int pc, int obNum, elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp) {
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
	} else if(obNum==2){
		switch(instruction_mem_ft[pc].op2.opnd_type) {
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
	} else {
		printf("obNum Error\n");
	}	
	return true;
}


elt_ft_queue_t pop_cap(int pc, int obNum, elt_ft_queue_t* scq, int rd_ptr) {
	if(obNum==1) {
		switch(instruction_mem_ft[pc].op1.opnd_type) {
			case atomic:// return anything you want
				break;
			case subformula:
				return pop(scq, rd_ptr);
			case direct:
				return (elt_ft_queue_t){instruction_mem_ft[pc].op1.value, t_now};
			case not_set:// return anything you want
				break;
			default:
				printf("operand Error\n");
		}
	} else if(obNum==2){
		switch(instruction_mem_ft[pc].op2.opnd_type) {
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
	} else {
		printf("obNum Error\n");
	}
	return (elt_ft_queue_t){false, -1};
}

