#include <stdio.h>
#include "../../src/TL/TL_observers.h"
#include "../../src/TL/TL_queue_pt.h"
#include "../../src/TL/TL_queue_ft.h"
#include <stdbool.h>

#define PRINT_RET printf("return=%s\n", (ret==0)?"success":"error");
pt_box_queue_t	*bq_addr;

int	get_queue_addr_pt(int pc);

int main(void) {
//build using gcc main.c ../../src/TL/TL_formula_int_pt.c ../../src/TL/TL_queue_pt.c ../../src/TL/TL_globals.c
int i;
extern int n_queues_pt; //number of pt queues
extern int n_queues_ft; //number of ft queues
//synchronization queues for instructions
extern sync_queues_ft_t		ft_sync_queues;
//synchronization queues for atomics
extern sync_queues_atomics_ft_t	ft_sync_atomic_queues;


TL_init();

	//
	// initialize queues
	//


	printf("test ft queue\n");
		// get number of queues
int vpc = 0; //virtual program counter
int ret;



	ft_sync_queue_t *ft_q_addr;
	ft_sync_queue_t *ft_q_addr2;
	ft_sync_queue_t *ft_q_addr3;


	//subresults q
	vpc=0;
	ft_q_addr = &ft_sync_queues[vpc];
	ft_q_addr2 = &ft_sync_queues[1];

	//atomic q
	//ft_q_addr = &sync_queues_atomics_ft_t[vpc];
	bool v_q;
	unsigned int t_q;
#if 0
	printf("is empty=%s\n", (isempty_queue_ft(ft_q_addr)==true)?"true":"false");
	ret=add_queue_ft(ft_q_addr, true, 0);
	printf("is empty=%s\n", (isempty_queue_ft(ft_q_addr)==true)?"true":"false");
	print_ft_queue(ft_q_addr);

	ret=add_queue_ft(ft_q_addr, true, 6);
	PRINT_RET
	print_ft_queue(ft_q_addr);

	ret=add_queue_ft(ft_q_addr, true, 7);
	PRINT_RET
	print_ft_queue(ft_q_addr);

	ret=add_queue_ft(ft_q_addr, true, 8);
	PRINT_RET
	print_ft_queue(ft_q_addr);

	ret=add_queue_ft(ft_q_addr, false, 9);
	PRINT_RET
	print_ft_queue(ft_q_addr);


	peek_queue_ft_head(ft_q_addr, &v_q, &t_q);
	print_ft_queue(ft_q_addr);
	printf("peeked v_q=%d, t_q=%d\n", v_q, t_q);

	ret=add_queue_ft(ft_q_addr, false, 10);
	PRINT_RET
	print_ft_queue(ft_q_addr);
#endif
#if 0
	for (i=0;i<1;i++){
		ret=remove_tail_queue_ft(ft_q_addr, &v_q, &t_q);
		print_ft_queue(ft_q_addr);
		printf("return=%s, removed_tail v_q=%d, t_q=%d\n", (ret==0)?"success":"error", v_q, t_q);
		printf("is empty=%s\n", (isempty_queue_ft(ft_q_addr)==true)?"true":"false");

	}
#endif

	for (i=0;i<1;i++){
		ret=remove_head_queue_ft(ft_q_addr, &v_q, &t_q);
		print_ft_queue(ft_q_addr);
		printf("return=%s, removed_head v_q=%d, t_q=%d\n", (ret==0)?"success":"error", v_q, t_q);
		printf("is empty=%s\n", (isempty_queue_ft(ft_q_addr)==true)?"true":"false");

	}
	//Test aggregation

	printf("is empty=%s\n", (isempty_queue_ft(ft_q_addr2)==true)?"true":"false");
	printf("test aggregation\n*************************\n");
	bool val;
	for (i=0;i<14;i++){
		switch(i) {
			case 0 :
			case 1 :
			case 2 :
			case 5 :
			case 6 :
			case 7 :
			case 8 :
			case 9 :
			case 10 :
			case 11 :
			case 12 :
			case 13 :
				val = false;
				break;
			case 3 :
			case 4 :
				val = true;
				break;
			default:
				printf("error\n");
		}

		ret=add_and_aggregate_queue_ft(ft_q_addr2, val, i);
		PRINT_RET
		print_ft_queue(ft_q_addr2);
	}

//	for (i=0;i<=2;i++) {
		ret=dequeue(ft_q_addr2, i);
		printf("called dequeue(ftq,%d)",i);
		PRINT_RET
		print_ft_queue(ft_q_addr2);
//	}

	t_now++;


	ft_q_addr3 = &ft_sync_queues[N_INSTRUCTIONS-1];
//	typedef ft_sync_queue_t	sync_queues_ft_t[N_INSTRUCTIONS];
//	typedef ft_sync_queue_t	sync_queues_atomics_ft_t[N_ATOMICS];

	ret=add_and_aggregate_queue_ft(ft_q_addr3, true, 123);

	ft_q_addr3 =  &ft_sync_atomic_queues[127];
	//printf("sync start %02x end %02x\n atom start %02x end %02x\n", &ft_sync_queues[0], &ft_sync_queues[N_SUBFORMULA_SNYC_QUEUES], &ft_sync_atomic_queues[0], &ft_sync_atomic_queues[N_SUBFORMULA_SNYC_QUEUES]);
	//printf("ft_q_addr3=%02x", ft_q_addr3);
	print_ft_queue(ft_q_addr3);
	printf("alive?");




#if 0
printf("test pt queue\n");
	// get number of queues
n_queues_pt = l_interval_mem_pt;
printf("number of queues = %d\n", n_queues_pt);

if (n_queues_pt*L_DOT_BUFFER > N_DOT_BUFFERS_TOTAL){
	printf("not enough queue space\n");
	printf("r2u2_errno = 1");
	return 1;
	}


	// set up queues
for (i=0; i< n_queues_pt;i++){
	pt_box_queues[i].head = 0;
	pt_box_queues[i].tail = 0;
	pt_box_queues[i].n_elts = 0;
	pt_box_queues[i].queue = pt_box_queue_mem + i * L_DOT_BUFFER;
	}


	bq_addr = pt_box_queues + get_queue_addr_pt(0);

	print_pt_queue(bq_addr);
	printf("------------------------------\n");
	unsigned int t_s;
	unsigned int t_e;
	unsigned int t_temps;
	unsigned int t_tempe;

	t_s=15;
	t_e=20;
	add_queue_pt(bq_addr, t_s, t_e);
	print_pt_queue(bq_addr);
	printf("add 15,20 ------------------------------\n");

	t_s=16;
	t_e=21;
	add_queue_pt(bq_addr, t_s, t_e);
	print_pt_queue(bq_addr);
	printf("add 16,21 ------------------------------\n");


	t_s=17;
	t_e=22;
	add_queue_pt(bq_addr, t_s, t_e);
	print_pt_queue(bq_addr);
	printf("add 17,22 ------------------------------\n");

	t_s=18;
	t_e=23;
	add_queue_pt(bq_addr, t_s, t_e);
	print_pt_queue(bq_addr);
	printf("add 18,23 ------------------------------\n");

	t_s=19;
	t_e=24;
	add_queue_pt(bq_addr, t_s, t_e);
	print_pt_queue(bq_addr);
	printf("add 19,24 ------------------------------\n");


	peek_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("peek ------------------------------\n");

	t_temps=0;
	t_tempe=0;

	remove_tail_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("rm tail ------------------------------\n");

	t_temps=0;
	t_tempe=0;

	remove_head_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("rm head ------------------------------\n");

	printf("empty=%s\n", isempty_queue_pt(bq_addr)?"true":"false");

	t_temps=0;
	t_tempe=0;

	remove_tail_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("rm tail ------------------------------\n");

	printf("empty=%s\n", isempty_queue_pt(bq_addr)?"true":"false");

	t_temps=0;
	t_tempe=0;

	remove_tail_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("rm tail ------------------------------\n");

	printf("empty=%s\n", isempty_queue_pt(bq_addr)?"true":"false");

	t_temps=0;
	t_tempe=0;

	remove_tail_queue_pt(bq_addr, &t_temps, &t_tempe);
	printf("t_temps=%d, t_tempe=%d\n", t_temps, t_tempe);
	print_pt_queue(bq_addr);
	printf("rm tail ------------------------------\n");

	printf("empty=%s\n", isempty_queue_pt(bq_addr)?"true":"false");
	printf("done test pt queue\n\n\n");
#endif


return 0;
}


int	get_queue_addr_pt(int pc){

//TODO TEMP
//return instruction_mem_pt[pc].adr_interval;
	pc=0;
return pc;
}
