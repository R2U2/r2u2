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
**=====================================================================================*/


#include <stdio.h>
#include <string.h>
#include "TL_observers.h"
#include "TL_queue_ft.h"
#include "TL_backpatch.c"


//TURN DEBUG_FT_FT ON OFF  // javey:
#define	TRACE_TOP_FT(X) X // Indicates that the Future Time (FT) engine begins
#define	TRACE_INSTR_FT(X) // Debug info on what the current instruction is (i.e. NOT, AND, UNTIL, Invariance)
#define	TRACE_OPND_FT(X) // Debug info on the current instructions operand type and value (direct, subformula, atomic, not set) idk what these mean yet
#define TRACE_RESULT_FT(X) // not used 
#define DEBUG_FT(X)  // Indicates time when the Future Time (FT) engine begins
#define TRACE_GLOBALLY_FT(X)  // Debug info for algorithm 2
#define TRACE_GLOBALLY_INTERVAL_FT(X) // Debug info for algorithm 4
#define	DEBUG_UNTIL_FT(X) // Debug info for algorithm 5
#define TRACE_OP_FT_AND(X)// Debug info for algorithm 3
#define TRACE_OP_FT_LOD(X) X


bool incRdPtr(int *read_ptr, int write_ptr);

static int nextInput(int tau_op, ft_sync_queue_t *ftq, int *read_ptr, int write_ptr, bool *valueInput, int *timeInput);

static int nextInput_UJ(int tau_op, ft_sync_queue_t *ftq, int *rd_ptr, int wr_ptr, bool *valueInput, int *timeInput);



/**
* Obtain the first operand of binary operation (tail element if applicable).
*/
static void get_opnd1_ft_tail(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync);

/**
* Obtain the second operand of binary operation (tail element if applicable).
*/
static void get_opnd2_ft_tail(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync);

/**
* Obtain the first operand of binary operation (head element if applicable).
*/
static void get_opnd1_ft_head(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync);

/**
* Obtain the second operand of binary operation (head element if applicable).
*/
static void get_opnd2_ft_head(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync);


/**
* General method for obtaining operands.
*/
static void get_opnd_ft(int pc, operand_t op, bool *v, unsigned int *t_e, ft_sync_t *sync, head_or_tail_t head_or_tail);

/**
* global synchronization queue for buffering async observers results
*/
ft_sync_queue_t *ft_q_addr;

/**
*   get_interval_lb_ft
*	get the lower bound (or time point) from temporal information
*	for instruction at pc
*/
int	get_interval_lb_ft(int pc);

/**
*   get_interval_ub_ft
*	get the upper bound (or time point) from temporal information
*	for instruction at pc
*/
int	get_interval_ub_ft(int pc);


/**
* Performing the asynchronous part of Future Time AND operator. (ALGORITHM 3 TACAS paper)
*/
static void op_ft_and(int *tau_op, FILE *fp, FILE *fp2, unsigned int pc, bool *v1, unsigned int *t_e1,bool *v2, unsigned int *t_e2);

/**
* Function implementing asynchronous observer for G[T] Future Time operator. (ALGORITHM 2 TACAS paper)
*/ 
static int op_ft_timed_globally(FILE *fp, FILE *fp2, unsigned int pc, bool *v, unsigned int *t_e, unsigned int lb);

/**
* Function which implements asynchronous observer for G[t1,t2].
* We provide the function with upper and lower bound value (ALGORITHM 4 TACAS paper)
*/
static void op_ft_interval_globally(FILE *fp, FILE *fp2, unsigned int pc, bool *v, unsigned int *t_e, unsigned int ub, unsigned int lb);

/**
* Function implementing asynchronous observer for U[J] Future Time operator. (ALGORITHM 5 TACAS paper)
*/
static void op_ft_timed_until(FILE *fp2, FILE *fp, unsigned int pc, bool v1, unsigned int t_e1,bool v2, unsigned int t_e2, unsigned int lb, unsigned int ub, bool *doWrite);


/**
* Dequeue an operand
*/
void dequeue_operand(int pc, unsigned int time2remove, unsigned int op_num);

/**
* Remove last used operand
*/
void remove_operand(int pc, unsigned int op_num);


/**
* One variable to memorize rising edge per every global timed TL instruction.
*/
//unsigned int t_rising_fi[N_SUBFORMULA_SNYC_QUEUES];

/**
* Array of values for memorizing next time moment timestamps
*/
//unsigned int t_tau_s[N_SUBFORMULA_SNYC_QUEUES]; //timestamp next time moment

/** 
* Pei: Array of values for memorizing last output timestamps
*/
//unsigned int t_tau[N_SUBFORMULA_SNYC_QUEUES];


/**
 * Helper function returns max of two timestamps
 */


unsigned int ts_max (int t_e1, int t_e2);

//--------------------------------------------------------------------
//	TL_update_ft()
//	main routine to run the PT engine on compiled instructions
//	* executes all instructions
//	* updates results_ft and queues
//--------------------------------------------------------------------
int TL_update_ft(FILE *fp, FILE *fp2){
	
int  		pc=0;
int 		stop = 0;
int 		attemptNum = 0;
bool 		doWrite = true;
//bool async verdicts 
bool		v;
bool		v1;
bool		v2;

bool valueInput1;
int timeInput1;
	
bool valueInput2;
int timeInput2;

//times from timestamp-verdict tuples
unsigned int	t_e;
unsigned int	t_e1;
unsigned int	t_e2;

int nextInputValue;
int nextInputValue2;
	
//sync FT verdicts
//sync FT verdicts
ft_sync_t 	sync;
ft_sync_t 	sync1;
ft_sync_t 	sync2;
	
unsigned int	lb;
unsigned int	ub;
	
//aux object 

DEBUG_FT(printf("\n[DBG] TL_update_ft::invoked at t=%d\n",t_now);)
TRACE_TOP_FT(printf("TL_update: %s[%d]\n",__FILE__,__LINE__);)

	

	//
	// put the current output into the previous one
	//
memcpy(results_ft_prev, results_ft, sizeof(results_ft_t));

	
		
	//
	// go through all instructions
	//
for (pc=0; pc< N_INSTRUCTIONS;pc++){

	if (stop){
		break;
		}

	switch(instruction_mem_ft[pc].opcode){

		//----------------------------------------------------
		// OP_END, OP_END_SEQUENCE
		//----------------------------------------------------
	case OP_END:
	case OP_END_SEQUENCE:
		attemptNum = 0;
		while(1){
			printf("END PC VALUE: %d\n", instruction_mem_ft[pc].op1.value);
			timeInput1 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
			if(timeInput1 >= ft_sync_queues[pc].tau_op){
				fprintf(fp2, "END PC:%d = (%d,%d)\n", pc, valueInput1, timeInput1);
				ft_sync_queues[pc].tau_op = timeInput1+1;
			}
			else{
				if(attemptNum == 0){
					fprintf(fp2, "END PC:%d = (-,-)\n", pc);
				}
				break;
			}
			attemptNum++;
		}
		printf(" * * * * * * END * * * * * *");
		int i;			
		stop=1;
		break;




		//----------------------------------------------------
		// OP_FT_LOD
		//----------------------------------------------------
	case OP_FT_LOD:
		//Retrieve Input Data
		get_opnd1_ft_tail(pc,&v, &t_e, &sync);
		
		//Add Asynchrounous Results to Queue
		add_and_aggregate_queue_ft(&ft_sync_queues[pc], v, t_e);
		fprintf(fp2, "LOAD PC:%d = (%d,%d)\n", pc, v, t_e);

		printf("-------LOAD--------\n");
		printf("Loading: (%d,%d)\n\n", v, t_e);


		if(DEBUG_FILE_OUTPUT == 1){
			fprintf(fp, "----LOADING DATA----\n");
			fprintf(fp, "PC: %d\n", pc);
			fprintf(fp, "Loading (%d, %d)\n", v, t_e);
			fprintf(fp, "Write Pointer Location: %d\n", ft_sync_queues[pc].write_ptr);
			fprintf(fp, "Queue Contents: ");
			print_ft_queue_file(&ft_sync_queues[pc], fp);
			fprintf(fp, "\n");
		}

		//Synchronous Observer Load Logic	
		switch (sync){
		case F:
			sync = F;
			break;
		case T:
			sync = T;
			break;
		default:
			sync = M;
		}
		results_ft[pc].sync_val = sync;
		results_ft[pc].async_val = sync;
		break;		



		//----------------------------------------------------
		// OP_FT_NOT
		//----------------------------------------------------
	case OP_FT_NOT:	
		doWrite=true;
		while(1){
			//Get the Next Input		
			timeInput1 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
		
			//If Queue is Empty, break out of observer. 
			if(nextInputValue == 0){
				if(doWrite) fprintf(fp2, "NOT PC:%d = (-,-)\n", pc);
				break;
			}


			//Observer Logic
			switch (valueInput1){
			case F:
				sync = T;
				break;
			case T:
				sync = F;
				break;
			default:
				sync = M;
			}

			//Save Data Results
			results_ft[pc].sync_val = sync;		
			results_ft[pc].async_val = !valueInput1;
			results_ft[pc].async_t = timeInput1;
			add_and_aggregate_queue_ft(&ft_sync_queues[pc], !valueInput1, timeInput1);
			doWrite=false;
			fprintf(fp2, "NOT PC:%d = (%d,%d)\n", pc, !valueInput1, timeInput1);

			//Update Tau_Op
			ft_sync_queues[pc].tau_op = timeInput1+1;

			//Debug Info
			if(DEBUG_FILE_OUTPUT == 1){
				fprintf(fp, "----NOT ALGORITHM----\n");
				fprintf(fp, "PC: %d\n", pc);
				fprintf(fp, "Input Queue PC Value: %d\n", instruction_mem_ft[pc].op1.value);
				fprintf(fp, "Retrieved Data: (%d, %d)\n", valueInput1, timeInput1);
				fprintf(fp, "Read Pointer Location: %d\n", ft_sync_queues[pc].read_ptr);
				fprintf(fp, "Not Algorithm Returns (%d, %d)\n", results_ft[pc].async_val, results_ft[pc].async_t);		
				fprintf(fp, "Queue Contents: ");
				print_ft_queue_file(&ft_sync_queues[pc], fp);
				fprintf(fp, "\n");
			}
		}
		
		break;




		//----------------------------------------------------
		// OP_FT_AND
		//----------------------------------------------------

	case OP_FT_AND:		

		attemptNum = 0;
		while(1){

			//Get the Next Input		
			timeInput1 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
			timeInput2 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op2.value], &ft_sync_queues[pc].read_ptr2, ft_sync_queues[instruction_mem_ft[pc].op2.value].write_ptr, &valueInput2, &timeInput2); 

			//Both Queues Empty
			if(timeInput1 == -1 && timeInput2 == -1){
				if(attemptNum == 0){
					fprintf(fp2, "AND PC:%d = (-,-)\n", pc);
				}
				break;
			}

			//One queue is empty and other queue is outputting "TRUE" thus we cannot make
			//a decision yet on the outcome
			if((timeInput1 == -1 && valueInput2 == 1) || (timeInput2 == -1 && valueInput1 == 1)) {
				if(attemptNum == 0){
					fprintf(fp2, "AND PC:%d = (-,-)\n", pc);
				}
				break;
			}

			//Debug Info
			if(DEBUG_FILE_OUTPUT == 1){
				fprintf(fp, "----AND OPERATION----\n");
				fprintf(fp, "PC: %d\n", pc);
				fprintf(fp, "Received Inputs (%d, %d) and (%d, %d)\n", valueInput1, timeInput1, valueInput2, timeInput2);
			}

			//Call to Asynchronous Observer Function
			//Function will update Tau_Op in accordance to the time stamp of the output
			op_ft_and(&ft_sync_queues[pc].tau_op, fp, fp2, pc, &valueInput1, &timeInput1, &valueInput2, &timeInput2); 

			//Print queue contents to file	
			fprintf(fp, "Queue Contents: ");
			print_ft_queue_file(&ft_sync_queues[pc], fp);
			attemptNum++;

			//Synchronous Observer Logic
		    sync1 = valueInput1;
			sync2 = valueInput2;
			switch (sync1){
			case F:
				sync = F;
				break;
			case T:
				sync = sync2;
				break;

			case M:
				switch (sync2){
				case F:
					sync = F;
					break;
				default:
					sync = M;
				}
			}
			results_ft[pc].sync_val = sync;
		}
		break;
		


		//----------------------------------------------------
		// operators on time points
		//----------------------------------------------------

		//----------------------------------------------------
		// OP_FT_FT (enventually, time-point:  F[t]
		//----------------------------------------------------
	case OP_FT_FT:
		TRACE_INSTR_FT(printf("%d\t%s\n",pc,"F[t]");)
		get_opnd1_ft_tail(pc,&v1, &t_e1, &sync1);

		lb = get_interval_lb_ft(pc);

			//
			// async: TODO
			//
		//pc].async_val = false;
		//results_ft[pc].async_t = TL_INF;

		switch(sync1){

		case T:
			sync = T;
			break;
		case F:
			if (lb == 0){
				sync = F;
				}
			else {
				sync = M;
				}
			break;
		case M:
			sync = M;
			break;
			}
		results_ft[pc].sync_val = sync;
		break;





		//----------------------------------------------------
		// OP_FT_GT (globally, time-point:  G[t]
		//----------------------------------------------------
	case OP_FT_GT:
		//while(1){
			//Get the Next Input		
			timeInput1 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
			lb = get_interval_lb_ft(pc);

			//If no new Input
			if(nextInputValue == 0){
				break;
			}

			//Debug Info
			if(DEBUG_FILE_OUTPUT == 1){			
				fprintf(fp, "----GLOBAL OPERATION----\n");
				fprintf(fp, "PC: %d\n", pc);	
				fprintf(fp, "Retrieved Data: (%d, %d)\n", valueInput1, timeInput1);
			}

			//async observer for G[T]
			op_ft_timed_globally(fp, fp2, pc, &valueInput1, &timeInput1, lb);

			//Print queue contents to file	
			fprintf(fp, "Queue Contents: ");
			print_ft_queue_file(&ft_sync_queues[pc], fp);
			fprintf(fp, "\n");

			//Synchronous Observer Logic
			sync1 = valueInput1;
			sync = M;
			switch(sync1){

			case F:
				sync = F;
				break;
			case T:
				if (lb == 0){
					sync = T;
					}
				else {
					sync = M;
					}
				break;
			case M:
				sync = M;
				break;
				}
			results_ft[pc].sync_val = sync;
			
			//Update Tau OP Value
			ft_sync_queues[pc].tau_op = timeInput1+1;

			printf("Num Elements End of Global: %d\n", ft_sync_queues[0].n_elts);

			
	//	}
		break;




		//----------------------------------------------------
		// operators on intervals
		//----------------------------------------------------

		//----------------------------------------------------
		// OP_FT_GJ (globally, interval:  G[t1,t2])
		//----------------------------------------------------
	case OP_FT_GJ:
		while(1){
			//Get the Next Input		
			printf("Tau Value: %d\n", ft_sync_queues[pc].tau_op);
			printf("Read Ptr: %d\n", ft_sync_queues[pc].read_ptr);
			timeInput1 = -1;
			nextInputValue = nextInput(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
			lb = get_interval_lb_ft(pc);
			ub = get_interval_ub_ft(pc);

			//If no new Input
			if(nextInputValue == 0){
				break;
			}
					
			//Debug Info
			if(DEBUG_FILE_OUTPUT == 1){
				fprintf(fp, "----GLOBAL INTERVAL OPERATION----\n");
				fprintf(fp, "PC: %d\n", pc);	
				fprintf(fp, "Retrieved Data: (%d, %d)\n", valueInput1, timeInput1);
				fprintf(fp, "Lower Bound: %d  Upper Bound: %d\n", lb, ub);
			}

			//async observer for G[t1,t2]
			op_ft_interval_globally(fp, fp2, pc, &valueInput1, &timeInput1, lb, ub);

			fprintf(fp, "Queue Contents: ");
			print_ft_queue_file(&ft_sync_queues[pc], fp);

			//Synchronous Observer Logic
			sync1 = valueInput1;
			sync = M;
			switch(sync1){

			case F:
				sync = F;
				break;
			case T:
				if ((lb == 0) && (ub == 0)){
					sync = T;
					}
				else {
					sync = M;
					}
				break;
			case M:
				sync = M;
				break;
				}
			results_ft[pc].sync_val = sync;

			//Update Tau OP Value
			ft_sync_queues[pc].tau_op = timeInput1 + 1;
		}

	break;




		//----------------------------------------------------
		// OP_FT_UJ (until, interval:  U[t1,t2])
		//----------------------------------------------------
		case OP_FT_UJ:
			doWrite = false;
			int min_tau = 0;
			while(1){
				printf("\n-------UNTIL--------\n");
				printf("Tau Op: %d\n\n", ft_sync_queues[pc].tau_op);

							
				printf("Getting Input 1:\n");
				timeInput1 = 0;
				printf("Getting:\n");
				nextInputValue = nextInput_UJ(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
				//nextInputValue = nextInput_UJ(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op1.value], &ft_sync_queues[pc].read_ptr, ft_sync_queues[instruction_mem_ft[pc].op1.value].write_ptr, &valueInput1, &timeInput1); 
				printf("read Ptr 1: %d\n\n", ft_sync_queues[pc].read_ptr);



				printf("Getting Input 2:\n");
				timeInput2 = 0;
				nextInputValue2 = nextInput_UJ(ft_sync_queues[pc].tau_op, &ft_sync_queues[instruction_mem_ft[pc].op2.value], &ft_sync_queues[pc].read_ptr2, ft_sync_queues[instruction_mem_ft[pc].op2.value].write_ptr, &valueInput2, &timeInput2); 
				printf("read Ptr 2: %d\n\n", ft_sync_queues[pc].read_ptr2);

				lb = get_interval_lb_ft(pc);
				ub = get_interval_ub_ft(pc);
				printf("Lower Bound: %d    Upper Bound: %d\n", lb, ub);

				if(nextInputValue == -1 || nextInputValue2 == -1){
					if(!doWrite) fprintf(fp2, "U[%d,%d] PC:%d = (-,-)\n",lb,ub,pc);
					printf("--------Not enough data\n");
					break;
				}

				min_tau = timeInput1<timeInput2?timeInput1:timeInput2;

				ft_sync_queues[pc].tau_op = min_tau+1; // or timeInput2+1, since they match with each other

				op_ft_timed_until(fp2, fp, pc, valueInput1, min_tau, valueInput2, min_tau, lb, ub, &doWrite);	


				//Debug Info
				if(DEBUG_FILE_OUTPUT == 1){
					fprintf(fp, "----UNTIL OPERATION----\n");
					fprintf(fp, "PC: %d\n", pc);	
					fprintf(fp, "Retrieved Data: (%d, %d) and (%d, %d)\n", valueInput1, timeInput1, valueInput2, timeInput2);
					fprintf(fp, "Lower Bound: %d  Upper Bound: %d\n", lb, ub);
				}

				//Async Until Logic Function
				//op_ft_timed_until(fp2, fp, &ft_sync_queues[pc].tau_op, pc, valueInput1, timeInput1, valueInput2, timeInput2, lb, ub);
				printf("UNTIL Done\n");

				// Synchronous Until
				sync1 = valueInput1;
				sync2 = valueInput2;
				sync = M;
				switch(sync1){

				case F:
					sync = F;
					break;
				case T:
					if ((sync2 == T) & (lb == 0)){
						sync = T;
						}
					else {
						sync = M;
						}
					break;
				case M:
					sync = M;
					break;
					}
				results_ft[pc].sync_val = sync;
			}
			break;



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

		//
		// at startup time (t_now = 0), we must set
		// the previous results accordingly, so that
		// complex formulas are initialized correctly
		//
		// TODO: check if necessary
		//
	if (t_now == 0){
		results_ft_prev[pc] = results_ft[pc];
		}
	
	//creates printable results foran instruction
	backpatch_async(pc);
		
	}

return 0;
}

//--------------------------------------------------------------------
//  get_opnd1_ft_tail
//	get 1st operand from instruction at pc (tail value if applicable)
//  get_opnd2_ft_tail
//	get 2nd operand from instruction at pc (tail value if applicable)
//--------------------------------------------------------------------
static void get_opnd1_ft_tail(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync){
	get_opnd_ft(pc, instruction_mem_ft[pc].op1, v, t_e, sync, tail);
	}

static void get_opnd2_ft_tail(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync){
	get_opnd_ft(pc, instruction_mem_ft[pc].op2, v, t_e, sync, tail);
	}

//--------------------------------------------------------------------
//  get_opnd1_ft_head
//	get 1st operand from instruction at pc (head value if applicable)
//  get_opnd2_ft_head
//	get 2nd operand from instruction at pc (head value if applicable)
//--------------------------------------------------------------------
static void get_opnd1_ft_head(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync){
	get_opnd_ft(pc, instruction_mem_ft[pc].op1, v, t_e, sync, head);
	}

static void get_opnd2_ft_head(int pc, bool *v, unsigned int *t_e, ft_sync_t *sync){
	get_opnd_ft(pc, instruction_mem_ft[pc].op2, v, t_e, sync, head);
	}

//--------------------------------------------------------------------
//  get_opnd_ft
//--------------------------------------------------------------------
static void get_opnd_ft(int pc, operand_t op, bool *v, unsigned int *t_e, ft_sync_t *sync, head_or_tail_t head_or_tail){
	
	//OPERAND TYPES:
	//direct 		= 0b01,  atomic 		= 0b00,
	//subformula 	= 0b10,  not_set 	= 0b11
		
	TRACE_OPND_FT(printf("[TRC]::get_opnd_ft: pc = %d;\t op = %d\top_type = %d\n", pc, op.value, op.opnd_type);)

switch (op.opnd_type){
		
		//ok sync, async
	case direct:
		*v = op.value;
		*sync = (ft_sync_t)op.value;
		*t_e = t_now;
		break;

		//ok sync, async
	case atomic:				

		//fetch from the atomic vector

		*v = atomics_vector[op.value];
		*t_e = t_now;

		*sync = (ft_sync_t)atomics_vector[op.value];
		break;

	case subformula:
		
		*v = results_ft[op.value].async_val;		//TODO - WHY WHY WHY IS THIS HERE!
		*t_e = results_ft[op.value].async_t;		//TODO - WHY WHY WHY IS THIS HERE!

		TRACE_OPND_FT(printf("[TRC]::get_opnd_ft:: queue_addr = %p\n", &ft_sync_queues[op.value]);)		
		TRACE_OPND_FT(print_ft_queue(&ft_sync_queues[op.value]));

		//peek_queue_ft_tail(pc, &ft_sync_queues[op.value], v, t_e);
		TRACE_OPND_FT(printf("\n[TRC]::t_opnd_ft:: obtained timestamp from queue[%d], (v,T) = (%d,%d)\n", op.value, *v, *t_e);)
		*sync = results_ft[op.value].sync_val;
		break;
	case not_set:
		*v = 0;
		*sync = M;
		*t_e = t_now;
		break;
	}
}



/**
* Dequeing operand1 or operand2
*/
void dequeue_operand(int pc, unsigned int time2remove, unsigned int op_num){

	operand_t op;

	op = (op_num==1) ? instruction_mem_ft[pc].op1 : instruction_mem_ft[pc].op2;

	switch (op.opnd_type){
		
		//ok sync, async
	case direct:
		//nothing to deque
		break;

	case atomic:				
		//nothing to deque
		break;

	case subformula:
		dequeue(&ft_sync_queues[op.value], time2remove);
		break;
	case not_set:

		break;
	}

}



/**
* Removing operand1 or operand2
*/
void remove_operand(int pc, unsigned int op_num){

	operand_t op;
bool b;
unsigned int t;

	op = (op_num==1) ? instruction_mem_ft[pc].op1 : instruction_mem_ft[pc].op2;

	switch (op.opnd_type){
		
		//ok sync, async
	case direct:
		//nothing to deque
		break;

	case atomic:
		//nothing to deque
		break;

	case subformula:
		remove_tail_queue_ft( &ft_sync_queues[op.value], &b, &t);
		break;
	case not_set:

		break;
	}

}




//--------------------------------------------------------------------
int	get_interval_lb_ft(int pc){

int adr = instruction_mem_ft[pc].adr_interval;

// TODO: check ranges to rule out FT compiler errors
//printf("[TRC]::get_interval_lb_ft:: PC , LB =  (%d,%d)\n", pc, interval_mem_ft[adr].lb);

return interval_mem_ft[adr].lb;
}

//--------------------------------------------------------------------
int	get_interval_ub_ft(int pc){

int adr = instruction_mem_ft[pc].adr_interval;

// TODO: check ranges to rule out FT compiler errors

//printf("[TRC]::get_interval_ub_ft:: PC , UB =  (%d,%d)\n", pc, interval_mem_ft[adr].ub);

return interval_mem_ft[adr].ub;
}




/**
* op_ft_and
* Function which generates the results for future time AND operator.
*/									 
static void op_ft_and(int *tau_op, FILE *fp, FILE *fp2, unsigned int pc, bool *v1, unsigned int *t_e1, bool *v2, unsigned int *t_e2){
	/*
	* The comments with the word "line"  below refer to the TACAS paper. 
	* This function should implement algorithm 3 for the conjunction of two 
	* prepositions formally outlined in the TACAS paper.
	*
	*	TACAS paper: T. Reinbacher, K. Rozier, J. Schumann "Temporal-Logic Based 
	*	Runtime Observer Pairs for System Health Management of Real-Time System",
	* 	TACAS, 2014
	*/
	results_ft_elt_t  result_ts;
	unsigned int aux_ix1;
	unsigned int aux_ix2; 

		//Algorithm 3: Line 2
		if ((*v1==true) && (*v2==true) && (*t_e1!= -1) && (*t_e2!= -1)) { 
			// line 3
			result_ts.async_val = true;
			result_ts.async_t   = (*t_e1 < *t_e2) ? *t_e1 : *t_e2; //min
			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp,"Output set to (true, min(t_e1 or t_e2))\n");		
		}

		//Algorithm 3: Line 4
		else if ((*v1==false) && (*v2==false) && (*t_e1!= -1) && (*t_e2!= -1)){ 
			// line 5
			result_ts.async_val = false;
			result_ts.async_t   = (*t_e1 > *t_e2) ? *t_e1 : *t_e2; //max
			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp,"Output set to (false, max(t_e1 or t_e2))\n");		
		}

		//Algorithm 3: Line 6
		else if ((*v1==false) && (*t_e1!= -1)){
			// line 7
			result_ts.async_val = false;
			result_ts.async_t   = *t_e1;
			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp,"Output set to (false, t_e1\n");		

		}

		//Algorithm 3: Line 8
		else if ((*v2==false) && (*t_e2!= -1)){
			// line 9
			result_ts.async_val = false;
			result_ts.async_t   = *t_e2;
			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp,"Output set to (false, t_e2)\n");
		}

		//Algorithm 3: Line 10
		else {
			// line 11
			result_ts.async_val = false; // according to the paper this else-block should output (_,_)
			result_ts.async_t   = TL_INF; // javey: <-- this must be how they identify (_,_) 
			//fprintf(fp2, "AND PC:%d = (-,-)", pc);
			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp, "Output set to (-,-)\n");
		}

		// the type for instruction_mem_ft (instruction_mem_t) is defined in TL_observers.h 
		// and the variable itself is filled with instruction in TL_formula_ft.c
		aux_ix1 = instruction_mem_ft[pc].op1.value; 
		aux_ix2 = instruction_mem_ft[pc].op2.value;					


		//if there was a valid result, put it into queue for other async observers
		if (result_ts.async_t != TL_INF	){
			
			// Pei: add tau variable to record the last time stamp
			t_tau[pc] = result_ts.async_t;
			ft_q_addr = &ft_sync_queues[pc];
			
			// Add Results to queue
			add_and_aggregate_queue_ft(ft_q_addr, result_ts.async_val, result_ts.async_t);
			add_and_aggregate_queue_ft(&ft_patch_queues[pc], result_ts.async_val, result_ts.async_t);			
	
			results_ft[pc].async_val = result_ts.async_val;
			results_ft[pc].async_t = result_ts.async_t;
			fprintf(fp2, "AND PC:%d = (%d,%d)\n", pc, result_ts.async_val, result_ts.async_t);
			*tau_op = results_ft[pc].async_t + 1; 

			if(DEBUG_FILE_OUTPUT == 1)
				fprintf(fp, "Algorithm Return (%d, %d)\n", results_ft[pc].async_val, results_ft[pc].async_t);
		}

		else{
			fprintf(fp2, "AND PC:%d = (-,-)", pc);
		}


		TRACE_OP_FT_AND(printf("TL_update_ft:: OP_FT_AND RESULTS value = %d\ttime = %d\n",result_ts.async_val,result_ts.async_t);)	
		// javey: it appears that instead of returning T_e "Tuple epsilon" (as in the TACAS algorithms)
		//			they use a queue(s) for recording results (add_and_aggregate_queue_ft())
}


///----------------------------------------------------------------------------------------///
					   
static int op_ft_timed_globally(FILE *fp, FILE *fp2, unsigned int pc, bool *v1, unsigned int *t_e1, unsigned int lb){
	/*
	* The comments with the word "line"  below refer to the TACAS paper. 
	* This function should implement algorithm 2 from the paper which is "Invariant within 
	* the Next Tau Time Stamps".
	*
	*	TACAS paper: T. Reinbacher, K. Rozier, J. Schumann "Temporal-Logic Based 
	*	Runtime Observer Pairs for System Health Management of Real-Time System",
	* 	TACAS, 2014+
	*/

	// parameter "lb" is Tau in the algorithm



		results_ft_elt_t  tuple_epsilon;
		int retval = 0;

		//Tuple_epsilon = Tuple_fi	
		tuple_epsilon.async_val = *v1;  // line 2
		tuple_epsilon.async_t   = *t_e1;	//results_ft[pc].sync_val = sync;
			
		//we are using sync val as previous value of operator, if it was false the sync result must be false as well
		TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally:: edge detection : tuple_epsilon.async_val=%d, results_ft[pc].sync_val=%d\n ",tuple_epsilon.async_val, results_ft[pc].sync_val);)
		if ((tuple_epsilon.async_val == true) && (results_ft[pc].sync_val == 0)) { // line 3
			TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally:: rising edge detected!, LB=%d",lb);)
			t_rising_fi[pc] = t_tau_s[pc]; // line 4
		}
		


		//if(DEBUG_FILE_OUTPUT == 1)
		//	fprintf(fp, "Rising time: %d\n", t_rising_fi[pc]);


		t_tau_s[pc] = *t_e1 + 1; // line 6
	


		if(DEBUG_FILE_OUTPUT == 1){
			//fprintf(fp, "Line 6 Mts: %d\n", t_tau_s[pc]);
			//fprintf(fp, "Tau: %d\n", lb);
		}


		if (tuple_epsilon.async_val == 1) { // line 7

			//if(DEBUG_FILE_OUTPUT == 1)
			//	fprintf(fp, "Input Value Holds True\n");

			
			TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally::t_rising_fi[%d]=%d, tuple_epsilon.async_t=%d, LB=%d\n ",pc , t_rising_fi[pc], tuple_epsilon.async_t, lb);)

			fprintf(fp, "TRISING: %d    LB: %d    TUPLE ASYNC T: %d\n", t_rising_fi[pc], lb, tuple_epsilon.async_t);

			if ( (t_rising_fi[pc] <= (tuple_epsilon.async_t - lb)) && (tuple_epsilon.async_t >= lb) ){ // line 8 with underflow check
				tuple_epsilon.async_t = tuple_epsilon.async_t - lb; // line 9
				TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally::TRUE RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
				

				//put to queues for other async observers
				//add_and_aggregate_queue_ft(&ft_sync_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);
				//remove_operand(pc, 1);
				
				//save or backpatch			

				add_and_aggregate_queue_ft(&ft_patch_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);
				fprintf(fp, "Algorithm Returns True (%d,%d)\n", tuple_epsilon.async_val, tuple_epsilon.async_t);
				results_ft[pc].async_val = tuple_epsilon.async_val;

				results_ft[pc].async_t = tuple_epsilon.async_t;
				t_tau[pc] = tuple_epsilon.async_t;// Pei: add this


				//if(DEBUG_FILE_OUTPUT == 1)
				//	fprintf(fp, "Return Data: (%d, %d)\n", results_ft[pc].async_val, results_ft[pc].async_t);
				
				fprintf(fp2, "G[%d] PC:%d = (%d,%d)\n", lb, pc, results_ft[pc].async_val, results_ft[pc].async_t);
				add_and_aggregate_queue_ft(&ft_sync_queues[pc], results_ft[pc].async_val, results_ft[pc].async_t);
				//remove_operand(pc, 1);


			}
			else {
				fprintf(fp2, "G[%d] PC:%d = (-,-)\n", lb, pc);
			}
		}
		else{
			add_and_aggregate_queue_ft(&ft_sync_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);

			//Pei: why we need the following operations? It appears there's no new output
			//save async verdict
			add_and_aggregate_queue_ft(&ft_patch_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);

			//if(DEBUG_FILE_OUTPUT == 1)
			//	fprintf(fp, "Return Data: (%d, %d)\n", tuple_epsilon.async_val, tuple_epsilon.async_t);


			results_ft[pc].async_val = tuple_epsilon.async_val;
			results_ft[pc].async_t = tuple_epsilon.async_t;
			fprintf(fp, "Algorithm Returns False (%d,%d)\n", tuple_epsilon.async_val, tuple_epsilon.async_t);
			TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally::FALSE RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
			fprintf(fp2, "G[%d] PC:%d = (%d,%d)\n", lb, pc, tuple_epsilon.async_val, tuple_epsilon.async_t);
		}


		//if(DEBUG_FILE_OUTPUT == 1)
		//	fprintf(fp, "\n");
	
	TRACE_GLOBALLY_FT(printf("[TRC]::op_ft_timed_globally:: t_now = %d\n",t_now);)
	return retval;

	// javey: it appears that instead of returning T_e "Tuple epsilon" (as in the TACAS algorithms)
	//			they use a queue(s) for recording results (add_and_aggregate_queue_ft())
		
}


///----------------------------------------------------------------------------------------///
					   
static void op_ft_interval_globally(FILE *fp, FILE *fp2, unsigned int pc, bool *v1, unsigned int *t_e1, unsigned int lb, unsigned int ub){
	/*
	* The comments with the word "line"  below refer to the TACAS paper. 
	* This function should implement algorithm 4 from the paper which is "Invariant within 
	* Future Interval".
	*
	*	TACAS paper: T. Reinbacher, K. Rozier, J. Schumann "Temporal-Logic Based 
	*	Runtime Observer Pairs for System Health Management of Real-Time System",
	* 	TACAS, 2014
	*/

	// lb: lower bound of interval
	// ub: upper bound of interval

	results_ft_elt_t  tuple_epsilon;
	unsigned int interval = ub - lb;

	//if the algorithm generates a tuple retval will be 1
	int retval = 0;
	
	//Tuple_epsilon = Tuple_fi	
	tuple_epsilon.async_val = *v1;
	tuple_epsilon.async_t   = *t_e1;	//results_ft[pc].sync_val = sync;

//-----------------------------------
// ALGORITHM FOR TIMED GLOBALLY 		// START line 2
	//we are using sync val as previous value of operator, if it was false the sync result must be false as well
	if ((tuple_epsilon.async_val == true) && (results_ft[pc].sync_val == 0)) {
	//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally:: rising edge detected!, LB=%d\n",lb);)
      t_rising_fi[pc] = t_tau_s[pc];
	}

	t_tau_s[pc] = *t_e1 + 1;
								 
	if (tuple_epsilon.async_val == 1) {
		
		//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::t_rising_fi[%d]=%d, tuple_epsilon.async_t=%d, LB=%d, INTERVAL=%d\n ",pc , t_rising_fi[pc], tuple_epsilon.async_t, lb, interval);)

		if ( (t_rising_fi[pc] <= (tuple_epsilon.async_t - interval)) && (tuple_epsilon.async_t >= interval) ){
			tuple_epsilon.async_t = tuple_epsilon.async_t - interval;	
			//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::TRUE RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
			
			retval = 1;
			//remove_operand(pc, 1);
			//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::TRUE RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
		}
		else {
			//do nothing
			//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::does nothing\n");)
			//remove_operand(pc, 1);  //removing the operand from input queue
		}
	}
	else{
		retval = 1;
		//remove_operand(pc, 1);
		//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::FALSE RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
	}
	
	//TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally:: t_now = %d\n",t_now);)
									// END line 2
//-----------------------------------

	if ((tuple_epsilon.async_t >= lb) && (retval == 1)) { // line 3
		tuple_epsilon.async_t = tuple_epsilon.async_t - lb;	// line 4
		add_and_aggregate_queue_ft(&ft_sync_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);
		add_and_aggregate_queue_ft(&ft_patch_queues[pc], tuple_epsilon.async_val, tuple_epsilon.async_t);
		
		TRACE_GLOBALLY_INTERVAL_FT(printf("[TRC]::op_ft_interval_globally::3 added RESULTS (%d,%d)\n",tuple_epsilon.async_val,tuple_epsilon.async_t);)
		fprintf(fp, "Algorithm Returns: (%d,%d)\n", tuple_epsilon.async_val, tuple_epsilon.async_t);
		results_ft[pc].async_val = tuple_epsilon.async_val;
		results_ft[pc].async_t = tuple_epsilon.async_t;
		fprintf(fp2, "G[%d,%d] PC:%d = (%d,%d)\n", lb, ub, pc, tuple_epsilon.async_val, tuple_epsilon.async_t);
		t_tau[pc] = tuple_epsilon.async_t + 1;//pei : add this
	}
	else{ // line 6
	//do nothing	
		fprintf(fp, "Algorithm Returns: (-,-)\n");
		fprintf(fp2, "G[%d,%d] PC:%d = (-,-)\n", lb, ub, pc);
		TRACE_GLOBALLY_INTERVAL_FT(printf("Algorithm Return (-,-)\n");)
	}

	// javey: it appears that instead of returning T_e "Tuple epsilon" (as in the TACAS algorithms)
	//			they use a queue(s) for recording results (add_and_aggregate_queue_ft())

}


///----------------------------------------------------------------------------------------///
static void op_ft_timed_until(FILE *fp2, FILE *fp, unsigned int pc, bool v1, unsigned int t_e1,bool v2, unsigned int t_e2, unsigned int lb, unsigned int ub, bool *doWrite) {
	/*
	* The comments with the word "line"  below refer to the TACAS paper. 
	* This function should implement algorithm 5 from the paper which is "Until within
	* Future Interval".
	*
	*	TACAS paper: T. Reinbacher, K. Rozier, J. Schumann "Temporal-Logic Based 
	*	Runtime Observer Pairs for System Health Management of Real-Time System",
	* 	TACAS, 2014
	*/

	//Pei: Note::ft_until_local_mem[pc].m_rising_phi_last actually is the falling edge of psi
	//Pei: Note::ft_until_local_mem[pc].phi_last_val actually is the last verdict of psi			

	//pc is program counter
	//v1 is the head value of first operand
	//t_e1 is head timestamp of first operand
	//v2 is head value of 2nd operand
	//t_e2 is head timestamp of second operand

	printf("UNTIL Alg Got: (%d,%d) and (%d,%d)\n", v1, t_e1, v2, t_e2);
	bool t_phi_val = v1;
	bool t_psi_val = v2;
	unsigned int t_e = t_e1;//or t_e = t_e2
	bool have_new_result = false;
	printf("ft_until_local_mem[pc].m_rising_phi_last: %d\n",ft_until_local_mem[pc].m_rising_phi_last);
	
	if((ft_until_local_mem[pc].phi_last_val == true ) && (t_psi_val == false)){
		ft_until_local_mem[pc].m_rising_phi_last = t_e;
	}

	if(t_psi_val == true){
		if(t_e >= lb){
			have_new_result = true;
			results_ft[pc].async_val = true;
			results_ft[pc].async_t = t_e - lb; 	
			printf("UNTIL* PC:%d = (%d,%d)\n",pc, results_ft[pc].async_val, results_ft[pc].async_t);
		}	
		
	}
	else if(t_phi_val == false && t_psi_val == false){
		if(t_e >= lb){
			have_new_result = true;
			results_ft[pc].async_val = false;
			results_ft[pc].async_t = t_e - lb; 
			printf("UNTIL** PC:%d = (%d,%d)\n",pc, results_ft[pc].async_val, results_ft[pc].async_t);
		}
	}
	else{
		if( t_e >= ub-lb + ft_until_local_mem[pc].m_rising_phi_last){
			if(t_e >= ub){
				have_new_result = true;
				results_ft[pc].async_val = false;
				results_ft[pc].async_t = t_e - ub; 	
			}			
		}	
	}
	
	ft_until_local_mem[pc].phi_last_val = t_psi_val;
	
	if (have_new_result) {
		add_and_aggregate_queue_ft(&ft_sync_queues[pc], results_ft[pc].async_val, results_ft[pc].async_t);
		add_and_aggregate_queue_ft(&ft_patch_queues[pc], results_ft[pc].async_val, results_ft[pc].async_t);
		fprintf(fp2, "U[%d,%d] PC:%d = (%d,%d)\n",lb,ub,pc, results_ft[pc].async_val, results_ft[pc].async_t);
		printf("UNTIL PC:%d = (%d,%d)\n",pc, results_ft[pc].async_val, results_ft[pc].async_t);
		*doWrite = true;
	}


}


//***************************************************************

#ifdef OK
//--------------------------------------------------------------------
//  opnd1_egde
//	get "none","rising", or "falling" information from operand 1
//--------------------------------------------------------------------
edge_t	opnd1_edge(int pc){  //FUNCTION NOT USED IN THIS FILE - CONSIDER MOVING/REMOVING

bool	v;
bool	v_p;
operand_t op1 = instruction_mem_ft[pc].op1;

switch (op1.opnd_type){
	case direct:
		v = false;
		v_p = false;
		break;
	
	case atomic:
		v = atomics_vector[op1.value];
		v_p = atomics_vector_prev[op1.value];
		break;

	case subformula:
		v = results_ft[op1.value];
		v_p = results_ft_prev[op1.value];
		break;
	case not_set:
		v = false;
		v_p = false;
		break;
	}

if (v & !v_p){
	return rising;
	}
if (!v & v_p){
	return falling;
	}
return none;
}

/**
* get_interval_lb_ft
* get the lower bound (or time point) from temporal information
* for instruction at pc
*/
int	get_interval_lb_ft(int pc){

	int adr = instruction_mem_ft[pc].adr_interval;

	// TODO: check ranges to rule out FT compiler errors

	return interval_mem_ft[adr].lb;
}

/**
* get_interval_ub_ft
* get the upper bound from temporal information
* for instruction at pc
*/
int	get_interval_ub_ft(int pc){

	int adr = instruction_mem_ft[pc].adr_interval;

	// TODO: check ranges to rule out FT compiler errors

	return interval_mem_ft[adr].ub;
}
#endif

/**
* get_queue_addr_ft
* get index of queue address into queue memory
* for instruction at pc
*/
int	get_queue_addr_ft(int pc){

return instruction_mem_ft[pc].adr_interval;
}

/**
 * Helper function returns max of two timestamps
 */
unsigned int ts_max (int t_e1, int t_e2){
	return (unsigned int) (t_e1 > t_e2) ? t_e1 : t_e2;
}



static int nextInput(int tau_op, ft_sync_queue_t *ftq, int *read_ptr, int write_ptr, bool *valueInput, int *timeInput){
	
	while(1){
		//Valid Useful Data found in queue
		int temp = ftq->ft_queue[*read_ptr].t_q;
		printf("TEMP: %d\n", temp);
		printf("Write Ptr: %d\n", write_ptr);
		printf("Buffer Size: %d\n", L_FT_BUFFER);
		if(tau_op <= temp){
			printf("Valid Data\n");
			*valueInput = ftq->ft_queue[*read_ptr].v_q;
			*timeInput = ftq->ft_queue[*read_ptr].t_q;
			return 1;
		}

		//Queue is Empty
		if(write_ptr != 0){
			if(*read_ptr == write_ptr-1){
				return 0;
			}
		}
		else{
//TODO Is this way to test initiation empty correct??
			if(*read_ptr == L_FT_BUFFER - 1){
				return 0;
			}
			else if(*read_ptr == write_ptr){
				return 0;
			}
		}
		//Queue non-empty, look at next available data
		if(*read_ptr == L_FT_BUFFER-1){
			*read_ptr = 0;
		}
		else{
			printf("Increase Rd Ptr Size\n");
			*read_ptr = *read_ptr + 1;
		}
		
	}
}



// a function that can increase the read pointer. It will return false if the read_pointer == writer_pointer or read_pointer == writer_pointer - 1.
bool incRdPtr(int *read_ptr, int write_ptr){
//test if we can increase the rdptr: If it's empty, return false. If not, increase rdptr and return true
	printf("read_ptr:%d, write_ptr:%d\n",*read_ptr,write_ptr);

	int tempRdPtr = *read_ptr + 1;
	if(tempRdPtr == L_FT_BUFFER){
		tempRdPtr = 0;
	}

//TODO Is this way to test initiation empty correct??
	if(write_ptr == 0 && *read_ptr == write_ptr){//at the initiation, this is not a good way to do so
		//*read_ptr = tempRdPtr;
		return false;
	}


	if(tempRdPtr == write_ptr){
		return false;
	}

	*read_ptr = *read_ptr + 1;
	
	if(*read_ptr == L_FT_BUFFER){
		*read_ptr = 0;
	}

	return true;
}

static int nextInput_UJ(int tau_op, ft_sync_queue_t *ftq, int *rd_ptr, int wr_ptr, bool *valueInput, int *timeInput){
	int temp;
	//store the current read pointer
	temp = ftq->ft_queue[*rd_ptr].t_q;
	printf("tau_op:%d\n",tau_op);
	while(temp < tau_op){
		if(! incRdPtr(rd_ptr, wr_ptr)){
			printf("Queue empty\n");
			return -1; //queue is empty
		}
		temp = ftq->ft_queue[*rd_ptr].t_q;
		printf("temp value:%d\n",temp);
	}
	*valueInput = ftq->ft_queue[*rd_ptr].v_q;
	*timeInput = temp;
	//*timeInput = tau_op;//for lock step mode
	return 1;
}


