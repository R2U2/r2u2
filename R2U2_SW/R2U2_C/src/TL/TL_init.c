/*=======================================================================================
** File Name:  TL_init.c
**
** Title:  Initialization for the TL engine
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
** Functions Defined:
**	TL_init()
**
** Purpose:  
**	initalize memories, counters, and queues for the TL
**
** Limitations, Assumptions, External Events, and Notes:
**	NA
**
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**
**=====================================================================================*/

#include <stdio.h>
#include "TL_observers.h"
#include "TL_queue_pt.h"
#include "TL_queue_ft.h"


#define DEBUG(X)
#define INFO_BPATCH(X) X


/**
*
*/

static int set_max_time_horizon() ;



extern interval_t	interval_mem_pt[];

int TL_init(){

int i;
int j;
int n_queues_pt;
int n_queues_ft;

t_now = 0;
r2u2_errno = 0;

	//
	// reset execution engine (TBD)
	// initialize input and output vectors
	// and local memories
	//
for (i=0; i<N_INSTRUCTIONS;i++){
		//
		// initialize PT results
		//
	results_pt[i]= false;
	results_pt_prev[i]= false;
	results_pt_rising[i] = TL_INF;
		//
		// initialize FT results
		//
	results_ft[i].async_val = false;
	results_ft[i].async_val = false;
	results_ft[i].sync_val  = F;  //initialize to false due to edge detection
		
	ft_until_local_mem[i].m_pre = 0;
	ft_until_local_mem[i].m_pre_minus_infinity = false;
	ft_until_local_mem[i].m_rising_phi_last = 0;
	ft_until_local_mem[i].m_falling_phi_last = 0;
	ft_until_local_mem[i].m_falling_phi_last_minus_infinity = true;
	ft_until_local_mem[i].p_holds = false;
	ft_until_local_mem[i].phi_last_val = false;	/*todo is this an assumption?*/

}


	//
	// initialize atomics
	//
for (i=0; i<N_ATOMICS;i++){
	atomics_vector[i]=false;
	atomics_vector_prev[i]=false;
}

	//
	// initialize queues
	//

	// get number of pt queues
n_queues_pt = l_interval_mem_pt;

if (n_queues_pt*L_DOT_BUFFER > N_DOT_BUFFERS_TOTAL){
	printf("not enough pt-queue space\n");
	r2u2_errno = 1;
	return 1;
	}

	// set up pt queues
for (i=0; i< n_queues_pt;i++){
	pt_box_queues[i].head = 0;
	pt_box_queues[i].tail = 0;
	pt_box_queues[i].n_elts = 0;
	pt_box_queues[i].queue = pt_box_queue_mem + i * L_DOT_BUFFER;
	}

// Initialize ft-sync queues
for (i=0; i<N_SUBFORMULA_SNYC_QUEUES; i++) {
	ft_sync_queues[i].write_ptr = 0;
	ft_sync_queues[i].n_elts = 0;
	ft_sync_queues[i].read_ptr = 0;
	ft_sync_queues[i].read_ptr2 = 0;
	ft_sync_queues[i].tau_op = 0;

	t_rising_fi[i] = 0;
	t_tau_s[i] = 0;
	t_tau[i] = 0;


	for (j=0;j<L_FT_BUFFER;j++) {
		
		ft_sync_queues[i].ft_queue[j].t_q=-1;
		ft_sync_queues[i].ft_queue[j].v_q=0;
	}

}

// Initialize ft-backpatching queues
for (i=0; i<N_PATCH_SNYC_QUEUES; i++) {
	ft_patch_queues[i].write_ptr = 0;
	ft_patch_queues[i].read_ptr = 0;
	ft_patch_queues[i].n_elts = 0;

	for (j=0;j<L_FT_BUFFER;j++) {
		ft_patch_queues[i].ft_queue[j].t_q=0;
		ft_patch_queues[i].ft_queue[j].v_q=0;
	}

}

	//getting the maximum time horizon
	max_time_horizon = set_max_time_horizon();


return 0;

}


/**
* Discovering maximum time horizon of all forlumar.
* TODO : Please note this needs to consider nested  
* operators as well
*/
static int set_max_time_horizon() {

	int max = 0;
	int i;
	int lb,ub;
	
	for (i = 0; i<N_INSTRUCTIONS;i++){

		lb = get_interval_lb_ft(i);
		ub = get_interval_ub_ft(i);
	
	  if ( lb > max ) max = lb;
	  if ( ub > max ) max = ub;
	}	
	INFO_BPATCH(printf("[INFO]::set_max_time_horizon():: Discovered Maximum time horizon of [%d] \n",max);)
		
	return max;
}

