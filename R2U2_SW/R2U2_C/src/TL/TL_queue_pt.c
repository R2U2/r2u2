
#include <stdio.h>
#include "R2U2.h"
#include "TL_observers.h"
#include "TL_queue_pt.h"

/*******************************************************************
*******************************************************************/
void peek_queue_pt(pt_box_queue_t *bq, unsigned int *t_s, unsigned int * t_e){

DEBUG_PRINT("N_elts=%d\n",bq->n_elts);

int hd;

if (!(bq->n_elts)){
	//
	// queue empty
	//
	*t_s = TL_INF;
	*t_e = TL_INF;
	}
else
	{
	hd = bq->head -1;
	if (hd < 0){
		hd = L_DOT_BUFFER -1;
		}

	*t_s = bq->queue[hd].t_s;
	*t_e = bq->queue[hd].t_e;
	}
}

/*******************************************************************
*******************************************************************/
int add_queue_pt(pt_box_queue_t *bq, unsigned int t_s, unsigned int t_e){

unsigned int nhead;

DEBUG_PRINT("add(%d,%d)\n",t_s, t_e);
DEBUG_PRINT("%x\n",bq);
DEBUG_PRINT("N_elts=%d\n",bq->n_elts);

if (bq->n_elts >= L_DOT_BUFFER){
	DEBUG_PRINT("full\n");
	//
	// buffer is full
	// don't enter anything
	//
	r2u2_errno = 1;
	return 1;
	}

bq->n_elts++;
bq->queue[bq->head].t_s = t_s;
bq->queue[bq->head].t_e = t_e;

nhead = bq->head + 1;
if (nhead == L_DOT_BUFFER){
	nhead = 0;
	}

bq->head = nhead;

return 0;
}

/*******************************************************************
*******************************************************************/
int remove_tail_queue_pt(pt_box_queue_t *bq, unsigned int *t_s, unsigned int *t_e){

DEBUG_PRINT("remove-tail\n");
DEBUG_PRINT("N_elts=%d\n",bq->n_elts);

if (!bq->n_elts){
	//
	// queue empty
	//
	*t_s = TL_INF;
	*t_e = TL_INF;
	r2u2_errno = 1;
	return 1;
	}

*t_s = bq->queue[bq->tail].t_s;
*t_e = bq->queue[bq->tail].t_e;

bq->tail++;
if (bq->tail >= L_DOT_BUFFER){
	bq->tail = 0;
	}
bq->n_elts--;
return 0;
}

/*******************************************************************
*******************************************************************/
int remove_head_queue_pt(pt_box_queue_t *bq, unsigned int *t_s, unsigned int *t_e){

DEBUG_PRINT("remove-head\n");
DEBUG_PRINT("N_elts=%d\n",bq->n_elts);

if (!bq->n_elts){
	//
	// queue empty
	//
	*t_s = TL_INF;
	*t_e = TL_INF;
	r2u2_errno = 1;
	return 1;
	}


if (bq->head == 0){
	bq->head = L_DOT_BUFFER-1;
	}
else {
	bq->head--;
	}
*t_s = bq->queue[bq->head].t_s;
*t_e = bq->queue[bq->head].t_e;

bq->n_elts--;

return 0;
}

/*******************************************************************
*******************************************************************/
bool isempty_queue_pt(pt_box_queue_t *bq){

DEBUG_PRINT("isempty=%d\n",bq->n_elts);
return !(bq->n_elts);

}

/*******************************************************************
*******************************************************************/
void print_pt_queue(pt_box_queue_t *bq){

int i;

i=bq->head;

printf("t=%d N=%d <",t_now, bq->n_elts);
if (!isempty_queue_pt(bq)){
    do {
	if (i == bq->tail)
		break;
	i--;
	if (i < 0){
		i= L_DOT_BUFFER -1;
		}
	printf("(%d,%d) ", bq->queue[i].t_s, bq->queue[i].t_e);
	} while(1);
    }
printf(">\n");
}
