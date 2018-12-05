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
**	This struct manages a single circular buffer (queue)
*/
typedef struct {
	int		write_ptr; 	/**	The head points to the next free element within	the circular buffer */
	//int		tail;	/** The tail points to the oldest element within the circular buffer (end) */
	int read_ptr;
	int read_ptr2;
	int tau_op;
	int		n_elts;	/** Number of stored elements in the circular buffer */
	elt_ft_queue_t	ft_queue[L_FT_BUFFER];	/** this array of tuples is used to store all the elements
	 	 	 	 	 	 	 	 	 	 	 	of the circular buffer. The head and tail elements of
	 	 	 	 	 	 	 	 	 	 	 	the struct are used to access the elements. */
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

/* Queues for backpatching */
typedef ft_sync_queue_t patch_queues_ft_t[N_PATCH_SNYC_QUEUES];


/*
** This is the array of queues for the subformulas/instructions.
** The definition of this element can be found in the file TL_globals.c
 */
extern sync_queues_ft_t		ft_sync_queues;

/*
** Queues used for backpatching.
 */
extern patch_queues_ft_t		ft_patch_queues;

extern unsigned int t_rising_fi[N_SUBFORMULA_SNYC_QUEUES];
extern unsigned int t_tau_s[N_SUBFORMULA_SNYC_QUEUES];
extern unsigned int t_tau[N_SUBFORMULA_SNYC_QUEUES];



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
void peek_queue_ft_head(ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q);

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
void peek_queue_ft_tail(int pc, int readptr, ft_sync_queue_t *ftq2, ft_sync_queue_t *ftq, bool *v_q, unsigned int * t_q);

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
int add_and_aggregate_queue_ft(ft_sync_queue_t *ftq, bool v_q, unsigned int t_q);

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
int remove_tail_queue_ft(ft_sync_queue_t *ftq, bool *v_q, unsigned int *t_q);

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
int remove_head_queue_ft(ft_sync_queue_t *ftq, bool *v_q, unsigned int *t_q);

/*
** @brief returns if the queue is empty (has no elements)
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @return true if empty, false otherwise
*/
bool isempty_queue_ft(ft_sync_queue_t *ftq);

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
int dequeue(ft_sync_queue_t *ftq, const unsigned int t_e); //make sure this doesnot react to T_INF

/*
** @brief outputs all elements of a particular queue to stdout
**
** @param ftq pointer to the address space of a particular queue within the
** 			  array of queues, the correct array element is addressed using
** 			  either the instruction (program) counter for the subformulas,
** 			  or the index for the atomic inputs.
** @return none
*/
void print_ft_queue(ft_sync_queue_t *ftq);


	
#endif
