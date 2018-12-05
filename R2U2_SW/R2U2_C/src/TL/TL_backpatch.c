/*=======================================================================================
** File Name:  TL_update_ft.c
**
** Title:  One execution step for the FT logic engine
**
** $Author:    stefan jaksic
** $Revision:  $
** $Date:      2016-12-9
**
**
** Functions Defined:
**	TL_backpatch()
**
** Purpose:  
**	generate the correct asynchronous results vector, once 
**	the results become known
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
#include <string.h>
#include "TL_observers.h"
#include "TL_queue_ft.h"


//TURN DEBUG_FT_FT ON OFF
#define DEBUG_BPATCH(X) 







/**
* Function which produces the result_ft array, based
* on the information from (Timestamp, Value) pairs.
*/

void backpatch_async(unsigned int pc){

	unsigned int	t_e;
	bool v;

	if (t_now > max_time_horizon) {  //after a horizon has passed
		//peek_queue_ft_tail(pc, &, &ft_patch_queues[pc], &v, &t_e);

		DEBUG_BPATCH(printf("[TRC]::backpatch_async:: Producing result[%d] = %d\t%s\n",pc,v,"end");)

		DEBUG_BPATCH(printf("before dequeing:\n");)
		DEBUG_BPATCH(print_ft_queue(&ft_patch_queues[pc]);)
		
		//dispose irrelevant timestamps
		if (t_now - max_time_horizon >= t_e) {
			dequeue(&ft_patch_queues[pc], t_now - max_time_horizon);		
		}
		
		DEBUG_BPATCH(printf("after dequeing:\n");)
		DEBUG_BPATCH(print_ft_queue(&ft_patch_queues[pc]);)
	}
	else {
		//dont produce any result before max_time_horizon
	}

	

}





