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
**	Apr.14.2019 | Pei | Clean up the code and rewrite the function. Consistent with the definition of Shared Connection Queue (SCQ)
**  Jun.20.2019 | Pei | fix a bug when checking if an SCQ is empty
**=====================================================================================*/
#include <stdio.h>
#include "TL_observers.h"
#include "R2U2.h"
#include "TL_queue_ft.h"
#include "R2U2.h"

#define	TRACE_OPND_FT(X) X

#define AGGREGATION  // do aggregation

// //* synchronization queues for instructions
// extern sync_queues_ft_t		ft_sync_queues;


// input ptr is relative to addr_start
// size = addr_end - addr_start+1
static inline int inc_ptr(int ptr, int size) {
	if(ptr==size-1) return 0;
	return ptr+1;
}
static inline int dec_ptr(int ptr, int size) {
	if(ptr==0) return size-1;
	return ptr-1;
}

// add new element to the SCQ
void add(elt_ft_queue_t* const scq, int size, elt_ft_queue_t newData, int* wr_ptr) {
	#ifdef AGGREGATION
		//if ( (scq+*wr_ptr)->v_q == false && (scq+dec_ptr(*wr_ptr, size))->v_q == false) { // case during initialization
		if ( (scq+*wr_ptr)->t_q == -1 ) { // case during initialization
			*(scq+*wr_ptr) = newData;
			*wr_ptr = inc_ptr(*wr_ptr, size);
			return;
		}
		if((scq+dec_ptr(*wr_ptr, size))->v_q == newData.v_q && \
			(scq+dec_ptr(*wr_ptr, size))->t_q < newData.t_q) { // assign to previous address
			*(scq+dec_ptr(*wr_ptr,size)) = newData;
		} else {
			*(scq+*wr_ptr) = newData;
			*wr_ptr = inc_ptr(*wr_ptr, size);
		}
		//printf("%d,%d\n",(scq+dec_ptr(*wr_ptr,size))->v_q, (scq+dec_ptr(*wr_ptr,size))->t_q);
	#else
		*(scq+*wr_ptr) = newData;
		*wr_ptr = inc_ptr(*wr_ptr, size);
	#endif
}

static void print_scq(elt_ft_queue_t* const scq, int size) {
	printf("--------------PRINT SCQ @%p\n", (void *) scq);
	for (int i=0; i<size; i++) {
		printf("addr: %d, verdict: %d, timstamp: %d\n", i, scq[i].v_q, scq[i].t_q);
	}
	printf("---------------END SCQ @%p\n", (void *) scq);
}


// *scq points to the curent node info structure
// size: size of the current SCQ assign to the specific node (addr_end - addr_start + 1)
// wr_ptr and rd_ptr are relative to addr_start (counting from 0~size-1)
bool isEmpty(elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp){
	//print_scq(scq, size);
	R2U2_TRACE_PRINT("inQueue, size: %d, rd_ptr: %d, wr_ptr: %d, desired_time_stamp: %d\n", size, *rd_ptr, wr_ptr, desired_time_stamp);
	R2U2_TRACE_PRINT("inQueue data content: t_q: %d, v_q: %d\n", scq[1].t_q, scq[1].v_q);
	if ((int)(scq+*rd_ptr)->t_q >= desired_time_stamp) {
		return false;
	} else if (*rd_ptr!=wr_ptr){
		while(*rd_ptr!=wr_ptr && (scq+*rd_ptr)->t_q < desired_time_stamp) {
			*rd_ptr = inc_ptr(*rd_ptr, size);
		}
		if ((scq+*rd_ptr)->t_q < desired_time_stamp) {
			*rd_ptr = dec_ptr(*rd_ptr, size);
			return true;
		} else {
			return false;
		}
	} else { //*rd_ptr==wr_ptr and no result
		// this is the case when space = 1 or initialization 
		return true;
	}
}

// always check isEmpty first before pop();
elt_ft_queue_t pop(elt_ft_queue_t* scq, int rd_ptr) {
	return scq[rd_ptr];
}
