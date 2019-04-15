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
**	Apr.14.2019 | Pei | Clean up the code and rewrite the function
**=====================================================================================*/
#include <stdio.h>
#include "TL_observers.h"
#include "TL_queue_ft.h"

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

// *scq points to the curent node info structure
// size: size of the current SCQ assign to the specific node (addr_end - addr_start + 1)
// wr_prt and rd_ptr are relative to addr_start (counting from 0~size-1)
bool isEmpty(elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp){
	bool isEmpty = false;
	bool curCheck = true;
	while((*rd_ptr != wr_ptr || curCheck) && (scq+*rd_ptr)->t_q < desired_time_stamp) {
		curCheck = false;
		*rd_ptr = inc_ptr(*rd_ptr, size);
	}
	if(*rd_ptr == wr_ptr) isEmpty = true;
	return isEmpty;
}

// always check isEmpty first before pop();
elt_ft_queue_t pop(elt_ft_queue_t* scq, int rd_ptr) {
	return scq[rd_ptr];
}
