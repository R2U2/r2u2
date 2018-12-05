/** =======================================================================================
** @file TL_queue_ft.h
**
** @author Patrick Moosbrugger
** @version	1
** @date      2016-11-22
**
** @brief Routines for the future time queues
**
** These Queues are used for the (time) synchronization of the R2U2 algorithm
** of the future time operators. It instantiates and array of circular buffers for every
** subformula/instruction or every atomic input. The stored tuples represent the signal values
** within intervals corresponding to their time stamps.
** Currently, for the subformula/instruction results, the R2U2 program (instruction) counter
** is used to address the correct queue in the array. For the atomic inputs, the index
** of the input is used to address the correct queue in the array of queues.
** Accessing the elements of the queue can be achieved using the methods
** provided in this file.
**
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**
**=====================================================================================*/
#include <stdio.h>
#include "TL_observers.h"
#include "TL_queue_ft.h"

#define DEBUG_FT(X)
#define	TRACE_OPND_FT(X) X
#define TRACE_QUEUE_FT(X) X
#define DEBUG_FT_DEQ(X) 

#define FT_Q_PRINT_REVERSE 0	/** changes the order in which tuples are output when calling
									print_ft_queue */
#define FT_Q_ADDRESS_CHECK 1	/** set to 1 to check address space on every queue operation
								 ** trade off: lower performance and execution time varies
								 ** (depends on address), but higher protection against
								 ** segmentation fault
								 */




/** synchronization queues for instructions */
extern sync_queues_ft_t		ft_sync_queues;

extern unsigned int t_rising_fi[N_SUBFORMULA_SNYC_QUEUES];
extern unsigned int t_tau_s[N_SUBFORMULA_SNYC_QUEUES];
extern unsigned int t_tau[N_SUBFORMULA_SNYC_QUEUES];

/* Function Prototypes */
int add_queue_ft(ft_sync_queue_t *ftq, bool v_q, unsigned int t_q);
#if FT_Q_ADDRESS_CHECK
bool is_queue_address_valid(ft_sync_queue_t *ftq);
#endif

/**
* @brief Function checks if the pointer ftq is a valid queue address
*
* 		 checks if ftq is a valid queue address,
* 		 execution time varies (depends on address),
* 		 due to the search.
* 		 The function can be disabled in the whole file using the
* 		 preprocessor constant FT_Q_ADDRESS_CHECK
* 		 (set to 1=enabled, 0=disabled)
*
* @param *ftq is the address to be checked
* @return true if a valid address, false otherwise
*/
#if FT_Q_ADDRESS_CHECK
bool is_queue_address_valid(ft_sync_queue_t *ftq){

	int i;

	DEBUG_FT(printf("[DBG]::is_queue_address_valid()\n");)
				/* loop counter */
	ft_sync_queue_t *ftq_valid;		/* pointer to a valid queues address */

	/* check if invalid pointer address */
	if (ftq == NULL) {
		TRACE_QUEUE_FT(printf("[DBG]::is_queue_address_valid() INVALID ADDRESS!\n");)
		return false;
	}

	/* go to the first valid subformula sync queue */
	ftq_valid = &ft_sync_queues[0];

	/* test if address is a valid subformula sync queues address */
	/* performance could be optimized using search algorithm */
	/* other possibility, only check range instead of comparing
	 * start addresses of queues */
	for (i = 0; i < N_SUBFORMULA_SNYC_QUEUES; i++) {
		if (ftq == ftq_valid) {
			return true;
		}
		ftq_valid++;
	}


	/* go to the first valid atomic sync queue   */
	ftq_valid = &ft_patch_queues[0];

	/* test if address is a valid patch sync queues address */
	for (i = 0; i < N_PATCH_SNYC_QUEUES; i++) {
		if (ftq == ftq_valid) {
			return true;
		}
		ftq_valid++;
	}

	TRACE_QUEUE_FT(printf("[DBG]::is_queue_address_valid() INVALID ADDRESS!\n");)
	return false;
}
#endif

/*
** @brief tries to add (with aggregate) a tuple to the head of the queue
**
**        aggregate means that rather than adding the tuple for every time step
**        it aggregates tuples with the same value such that tuples are only
**        stored when the value changes. Hence, the values within the interval
**        between the timestamps of two consecutive tuples is constant,
**        on error r2u2_errno is set
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param v_q the boolean value of a tuple to be added
** @param t_q the timestamp of the value to be added
** @return 0 on success (either aggregated or added), 1 otherwise
*/
int add_and_aggregate_queue_ft(ft_sync_queue_t *ftq, bool v_q, unsigned int t_q){
	unsigned int nhead;

	#if FT_Q_ADDRESS_CHECK
		 if (!is_queue_address_valid(ftq)) {
			r2u2_errno = 1;
			return 1;
	 	}
	#endif





	// if q is not empty - can we aggregate?
	if(ftq->write_ptr==0){
		if ((!isempty_queue_ft(ftq)) && (ftq->ft_queue[L_FT_BUFFER-1].v_q == v_q)) {
			// overwrite the head element
			ftq->ft_queue[ftq->write_ptr-1].t_q = t_q;
			return 0;
		}
	}
	else{
		if ((!isempty_queue_ft(ftq)) && (ftq->ft_queue[ftq->write_ptr-1].v_q == v_q)) {
			// overwrite the head element
			ftq->ft_queue[ftq->write_ptr-1].t_q = t_q;
			return 0;
		}
	}


	// if we can not aggregate, we try to add the new element
	return add_queue_ft(ftq, v_q, t_q);

}


/**
* Function which adds a tuple at the head of the queue.
* @param *ftq is the queue
* @param v_q value to be added to the queue.
* @param t_q is a timestamp.
* @return 0 as an OK indication
*/
int add_queue_ft(ft_sync_queue_t *ftq, bool v_q, unsigned int t_q){
	unsigned int nhead;

	if(ftq->n_elts != L_FT_BUFFER){
		ftq->n_elts++;
	}
	
	ftq->ft_queue[ftq->write_ptr].v_q = v_q;
	ftq->ft_queue[ftq->write_ptr].t_q = t_q;
	nhead = ftq->write_ptr + 1;
	if (nhead == L_FT_BUFFER){
		nhead = 0;
		}

	ftq->write_ptr = nhead;
	return 0;
}

/*
** @brief peaks the head element of a queue without consuming
**
**        peaks the head element(tuple) of the queue addressed by parameter ftq,
**        and writes the boolean value to parameter v_q, and the corresponding
**        timestamp to parameter t_q
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param v_q location where the boolean value (head) shall be stored
** @param t_q locaion where the timestamp corresponding to value v_q shall be stored
** @return none
*/
void peek_queue_ft_head(ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q){

int hd;

#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return;
	 }
#endif

DEBUG_FT(printf("[DBG]:: peek_queue_ft_head invoked: N_elts=%d\n",ftq->n_elts);)

if (!(ftq->n_elts)){
	//
	// queue empty
	//
	*v_q = false;
	*t_q = TL_INF;
	}
else
	{
	hd = ftq->write_ptr -1;//TODO @Stefan
					// Patrick: Note to stefan, head-1 because the
					// head always points to the next free element rather
					// than the latest element, so this is correct
	//hd = ftq->head;
	if (hd < 0){
		hd = L_FT_BUFFER -1;
		}

	*v_q = ftq->ft_queue[hd].v_q;
	*t_q = ftq->ft_queue[hd].t_q;
	}
}

/*
** @brief peaks the tail element of a queue without consuming
**
**        peaks the tail element(tuple) of the queue addressed by parameter ftq,
**        and writes the boolean value to parameter v_q, and the corresponding
**        timestamp to parameter t_q
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param v_q location where the boolean value (tail) shall be stored
** @param t_q locaion where the timestamp corresponding to value v_q shall be stored
** @return none
*/
void peek_queue_ft_tail(int pc, int readptr, ft_sync_queue_t *ftq2, ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q){
#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return;
	 }
#endif
	if (!(ftq->n_elts)){
		*v_q = false;
		*t_q = TL_INF;
		}
	else
		{
		if (readptr > (L_FT_BUFFER - 1)) {
			readptr = 0;
			}
		*v_q = ftq->ft_queue[readptr].v_q;
		*t_q = ftq->ft_queue[readptr].t_q;
		}
}


/*
** @brief reads and consumes the tail element of a queue
**
**        reads the tail element (tuple) of the queue addressed by parameter ftq,
**        and consumes it, on error r2u2_errno is set
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param v_q location where the boolean value (tail) shall be stored
** @param t_q locaion where the timestamp corresponding to value v_q shall be stored
** @return 0 on success, 1 otherwise
*/
int remove_tail_queue_ft(ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q){

#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return 1;
	 }
#endif

DEBUG_FT(printf("[DBG]::queue_ft::remove-tail invoked \n");)
DEBUG_FT(printf("[DBG]::queue_ft:: N_elts=%d\n",ftq->n_elts);)

if (!ftq->n_elts){
	//
	// queue empty
	//
	*v_q = false;
	*t_q = TL_INF;
	r2u2_errno = 1;
	return 1;
	}

*v_q = ftq->ft_queue[ftq->read_ptr].v_q;
*t_q = ftq->ft_queue[ftq->read_ptr].t_q;

ftq->read_ptr++;
if (ftq->read_ptr >= L_FT_BUFFER){
	ftq->read_ptr = 0;
	}
ftq->n_elts--;
return 0;
}

/*
** @brief reads and consumes the head element of a queue
**
**        reads the head  element (tuple) of the queue addressed by parameter ftq,
**        and consumes it, on error r2u2_errno is set
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param v_q location where the boolean value (head) shall be stored
** @param t_q locaion where the timestamp corresponding to value v_q shall be stored
** @return 0 on success, 1 otherwise
*/
int remove_head_queue_ft(ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q){

#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return 1;
	 }
#endif

DEBUG_FT(printf("[DBG]::queue_ft::remove-head invoked \n");)
DEBUG_FT(printf("N_elts=%d\n",ftq->n_elts);)

if (!ftq->n_elts){
	//
	// queue empty
	//
	*v_q = false;
	*t_q = TL_INF;
	r2u2_errno = 1;
	return 1;
	}


if (ftq->write_ptr == 0){
	ftq->write_ptr = L_FT_BUFFER-1;
	}
else {
	ftq->write_ptr--;
	}
*v_q = ftq->ft_queue[ftq->write_ptr].v_q;
*t_q = ftq->ft_queue[ftq->write_ptr].t_q;

ftq->n_elts--;

return 0;
}

/*
** @brief returns if the queue is empty (has no elements)
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @return true if empty, false otherwise
*/
bool isempty_queue_ft(ft_sync_queue_t *ftq){
	/* Check if queue address is a valid queue address */
#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return true;
	 }
#endif
	return !(ftq->n_elts);
}

/*
** @brief outputs all elements of a particular queue to stdout
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @return none
*/


void print_ft_queue_file(ft_sync_queue_t *ftq, FILE *fp){
	/* Check if queue address is a valid queue address */
#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return;
	 }
#endif

int i;
#if FT_Q_PRINT_REVERSE
i=0;

printf("t=%d N=%d <",t_now, ftq->n_elts);
 if (!isempty_queue_pt(ftq)){
    do {
	if (i == ftq->n_elts){
		break;
	}
	
	
	fprintf(fp, "(%d,%d) ", ftq->ft_queue[i].v_q, ftq->ft_queue[i].t_q);
	i++;
	} while(1);
    }
fprintf(fp, ">\n");
#else
	
i=0;
fprintf(fp,"t=%d N=%d <",t_now, ftq->n_elts);
    do {
	if (i == ftq->n_elts){
		break;
	}
	fprintf(fp,"(%d,%d) ", ftq->ft_queue[i].v_q, ftq->ft_queue[i].t_q);
	i++;

	} while(1);
    
fprintf(fp,">\n");

#endif
}






void print_ft_queue(ft_sync_queue_t *ftq){

/* Check if queue address is a valid queue address */
#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return;
	 }
#endif

int i;
#if FT_Q_PRINT_REVERSE
i=ftq->write_ptr;

printf("t=%d N=%d <",t_now, ftq->n_elts);
 if (!isempty_queue_pt(ftq)){
    do {
	if (i == ftq->read_ptr[0])
		break;
	i--;
	if (i < 0){
		i= L_FT_BUFFER -1;
		}
	printf("(%d,%d) ", ftq->ft_queue[i].v_q, ftq->ft_queue[i].t_q);
	} while(1);
    }
printf(">\n");
#else
	
i=ftq->read_ptr;

printf("t=%d N=%d <",t_now, ftq->n_elts);
 if (!isempty_queue_pt(ftq)){
    do {
	if (i == ftq->write_ptr)
		break;
	if (i == L_FT_BUFFER){
		i= 0;
		}
	printf("(%d,%d) ", ftq->ft_queue[i].v_q, ftq->ft_queue[i].t_q);
	i++;

	} while(1);
    }
printf(">\n");

#endif
}

//TODO make sure this does not react to T_INF
/*
** @brief removes tail elements that are older or equal to t_e,
**        on error, r2u2_errno is set
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @param t_e elements <= t_e are removed from the queue (beginning from the tail)
** @return 0 on success, 1 otherwise
*/
int dequeue(ft_sync_queue_t *ftq, const unsigned int t_e){

	bool v_q;
	unsigned int t_q;
	int ret;

#if FT_Q_ADDRESS_CHECK
	 if (!is_queue_address_valid(ftq)) {
		r2u2_errno = 1;
		return 1;
	 }
#endif

	if (!ftq->n_elts){
		//
		// queue empty, nothing to do
		//
		return 0;
		}

	/* remove tail elements up to the t_e or until the queue is empty */
	while ((ftq->ft_queue[ftq->read_ptr].t_q <= t_e) && (ftq->n_elts)) {
		ret=remove_tail_queue_ft(ftq, &v_q,&t_q);
		if (ret!=0) {
			r2u2_errno = 1;
			return ret;
		}
		DEBUG_FT_DEQ(printf("DEQUEUE: dropped tuple: <%d,%d>\n", v_q, t_q);)
		DEBUG_FT_DEQ(printf("DEQUEUE(q, TE=%d): dropped tuple: <%d,%d>\n", t_e, v_q, t_q);)
	}

	return 0;

}


