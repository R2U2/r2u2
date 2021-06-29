
#include <stdio.h>
#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_pt.h"

/*******************************************************************
Return the values of t_s and t_e, the two timestamp tuples, at the top of the queue
*******************************************************************/
void peek_queue_pt(pt_box_queue_t* bq, timestamp_t* t_s, timestamp_t* t_e)
{
    //R2U2_DEBUG_PRINT("-------- Peak at Box Queue ---------\n");

    //R2U2_DEBUG_PRINT("Number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("Head of boxqueue (bq) = %d\n", bq->head);
    //R2U2_DEBUG_PRINT("Tail of boxqueue (bq) = %d\n", bq->tail);
    int hd;

    // If the queue is empty, return the timestamps as TL_INF
    if (!(bq->n_elts)) {

        *t_s = TL_INF;
        *t_e = TL_INF;
        //R2U2_DEBUG_PRINT("Queue is empty\n");
    }
    // else,
    else {
        // Grab the box queue's top value (one below the head index)
        //hd = bq->head - 1;
        hd = bq->tail;
        // If the box queue's top value is less than zero,
        if (hd < 0) {
            // Update hd to 63 (latest index of the ring buffer; see R2U2Config.h for L_DOT_BUFFER's hardcoded value)
            //R2U2_DEBUG_PRINT("Buffer underflow, reset head to 63\n");
            hd = L_DOT_BUFFER - 1;
        }
        // Return t_s and t_e at the top of the queue
        *t_s = bq->queue[hd].t_s;
        *t_e = bq->queue[hd].t_e;
    }
    //R2U2_DEBUG_PRINT("t_s = %d\n",*t_s);
    //R2U2_DEBUG_PRINT("t_e = %d\n",*t_e);
    //R2U2_DEBUG_PRINT("------------------------------------\n");
}

/*******************************************************************
Pushes a new timestamp tuple and advances the head of the queue
*******************************************************************/
int add_queue_pt(pt_box_queue_t* bq, timestamp_t t_s, timestamp_t t_e)
{

    int nhead;

    //R2U2_DEBUG_PRINT("----- Add Element to Box Queue -----\n");
    //R2U2_DEBUG_PRINT("Add (%d,%d) to the queue's head\n", t_s, t_e);
    //R2U2_DEBUG_PRINT("Prior to Add, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("Prior to Add, head of queue = %d\n",bq->head);

    if (bq->n_elts >= L_DOT_BUFFER) {
        //R2U2_DEBUG_PRINT("Queue is full\n");
        //R2U2_DEBUG_PRINT("------------------------------------\n");
        // buffer is full, don't enter anything
        r2u2_errno = 1;
        return 1;
    }

    bq->n_elts++;
    bq->queue[bq->head].t_s = t_s;
    bq->queue[bq->head].t_e = t_e;

    nhead = bq->head + 1;
    // Check for buffer overflow
    if (nhead == L_DOT_BUFFER) {
        //R2U2_DEBUG_PRINT("Buffer overflow, reset head to 0\n");
        nhead = 0;
    }

    bq->head = nhead;
    //R2U2_DEBUG_PRINT("After Add, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("After Add, head of queue = %d\n", bq->head);
    //R2U2_DEBUG_PRINT("------------------------------------\n");
    return 0;
}

/*******************************************************************
Pops from the end of the box queue
*******************************************************************/
int remove_tail_queue_pt(pt_box_queue_t* bq, timestamp_t* t_s, timestamp_t* t_e)
{

    //R2U2_DEBUG_PRINT("----- Remove Tail from Box Queue -----\n");
    //R2U2_DEBUG_PRINT("Prior to removing tail, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("Prior to removal, tail of queue = %d\n",bq->tail);

    if (!bq->n_elts) {
        //R2U2_DEBUG_PRINT("Queue is empty\n");
        //R2U2_DEBUG_PRINT("------------------------------------\n");
        // queue empty
        *t_s = TL_INF;
        *t_e = TL_INF;
        r2u2_errno = 1;
        return 1;
    }

    *t_s = bq->queue[bq->tail].t_s;
    *t_e = bq->queue[bq->tail].t_e;

    bq->tail++;
    if (bq->tail >= L_DOT_BUFFER) {
        bq->tail = 0;
    }
    bq->n_elts--;
    //R2U2_DEBUG_PRINT("After removing tail, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("After removal, tail of queue = %d\n", bq->tail);
    //R2U2_DEBUG_PRINT("------------------------------------\n");
    return 0;
}

/*******************************************************************
Pops from the head of the box queue
*******************************************************************/
int remove_head_queue_pt(pt_box_queue_t* bq, timestamp_t* t_s, timestamp_t* t_e)
{

    //R2U2_DEBUG_PRINT("----- Remove Head from Box Queue -----\n");
    //R2U2_DEBUG_PRINT("Prior to removing head, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("Prior to removal, head of queue = %d\n",bq->head);

    if (!bq->n_elts) {
        //R2U2_DEBUG_PRINT("Queue is empty\n");
        //R2U2_DEBUG_PRINT("------------------------------------\n");
        // queue empty
        *t_s = TL_INF;
        *t_e = TL_INF;
        r2u2_errno = 1;
        return 1;
    }

    if (bq->head == 0) {
        bq->head = L_DOT_BUFFER - 1;
    } else {
        bq->head--;
    }
    *t_s = bq->queue[bq->head].t_s;
    *t_e = bq->queue[bq->head].t_e;

    bq->n_elts--;
    //R2U2_DEBUG_PRINT("After removing head, number of elements in queue = %d\n", bq->n_elts);
    //R2U2_DEBUG_PRINT("After removal, head of queue = %d\n", bq->head);
    //R2U2_DEBUG_PRINT("------------------------------------\n");
    return 0;
}

/*******************************************************************
Checks to see if 'n_elts' counter is zero
*******************************************************************/
bool isempty_queue_pt(pt_box_queue_t* bq)
{

    // R2U2_DEBUG_PRINT("isempty=%d\n", bq->n_elts);
    return !(bq->n_elts);
}

/*******************************************************************
Prints the contents of the queue to the terminal; for debug purposes
*******************************************************************/
void print_pt_queue(pt_box_queue_t* bq)
{

    int i;

    i = bq->head;

    printf("t=%u N=%d <", t_now, bq->n_elts);
    if (!isempty_queue_pt(bq)) {
        do {
            if (i == bq->tail)
                break;
            i--;
            if (i < 0) {
                i = L_DOT_BUFFER - 1;
            }
            printf("(%u,%u) ", bq->queue[i].t_s, bq->queue[i].t_e);
        } while (1);
    }
    printf(">\n");
}
