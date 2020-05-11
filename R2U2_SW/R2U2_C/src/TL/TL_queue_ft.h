/** =======================================================================================
** @file TL_queue_ft.h
**
** @author Patrick Moosbrugger
** @version	1
** @date      2016-11-22
**
** @brief definition and data types for the FT queues
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

#ifndef _TL_QUEUE_FT_H_
#define _TL_QUEUE_FT_H_

/** @struct elt_ft_queue_t
    @brief defines the tuples stored in the queue
*/
typedef struct {
	bool	v_q;			/** stores boolean value from atomic inputs and
							 ** subformulas corresponding to the timestamp */
	unsigned int	t_q;	/** timestamp corresponding to the boolean value */
	} elt_ft_queue_t;

/** @struct ft_sync_queue_t
**	This struct manages all info for a single node/instruction
*/
typedef struct 
{
	int wr_ptr;
	int rd_ptr;
	int rd_ptr2; /** For binary operators, need two read ptr*/
	int m_edge;
	elt_ft_queue_t pre;
	int preResult;
	int desired_time_stamp;
} ft_sync_queue_t;



//TODO talk to stefan about dequeue comment: make sure this doesnot react to T_INF
// can deque be called with TINF
//------------------------------------------------------
//TODO- to improve: this is overapproximation. N_INTERVAL should be used

/**
** The type sync_queues_ft_t defines an array of synchronization queues which
** are used to store results for the subformulas/instrustions.
** Thus, for every instruction, the program counter is used to address
** the corresponding circular buffer.
** within this array of circular buffers.
*/
typedef ft_sync_queue_t	sync_queues_ft_t[N_SUBFORMULA_SNYC_QUEUES];

typedef elt_ft_queue_t SCQ_t[L_SCQ_SIZE]; // Pei: pre assign total size to the SCQ

/*
** This is the array of queues for the subformulas/instructions.
** The definition of this element can be found in the file TL_globals.c
 */
extern sync_queues_ft_t	ft_sync_queues;

extern SCQ_t SCQ;


static inline int inc_ptr(int ptr, int size);
static inline int dec_ptr(int ptr, int size);
elt_ft_queue_t pop(elt_ft_queue_t* scq, int rd_ptr);

void add(elt_ft_queue_t* const scq, int size, elt_ft_queue_t newData, int* wr_ptr);
bool isEmpty(elt_ft_queue_t* const scq, int size, const int wr_ptr, int* rd_ptr, int desired_time_stamp);

void read_atomic(int pc, bool* v, unsigned int* t_e);

#endif
