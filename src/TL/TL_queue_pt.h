#ifndef _TL_QUEUE_PT_H_
#define _TL_QUEUE_PT_H_

typedef struct {
	timestamp_t	t_s;
	timestamp_t	t_e;
	} elt_queue_t;

typedef struct {
	int		head;
	int		tail;
	int		n_elts;
	elt_queue_t	*queue;
	} pt_box_queue_t;

typedef elt_queue_t	box_queue_mem_pt_t[N_DOT_BUFFERS_TOTAL];

typedef pt_box_queue_t	box_queues_pt_t[N_INTERVAL];

extern box_queue_mem_pt_t	pt_box_queue_mem;
extern box_queues_pt_t		pt_box_queues;


void peek_queue_pt(pt_box_queue_t *bq, timestamp_t *t_s, timestamp_t * t_e);
int add_queue_pt(pt_box_queue_t *bq, timestamp_t t_s, timestamp_t t_e);
int remove_tail_queue_pt(pt_box_queue_t *bq, timestamp_t *t_s, timestamp_t *t_e);
int remove_head_queue_pt(pt_box_queue_t *bq, timestamp_t *t_s, timestamp_t *t_e);
bool isempty_queue_pt(pt_box_queue_t *bq);

void print_pt_queue(pt_box_queue_t *bq);


#endif
