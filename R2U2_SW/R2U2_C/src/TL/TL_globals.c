/*=======================================================================================
** File Name:  TL_globals.c
**
** Title:  global variables for the TL engine
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
** Purpose:
**	global variables for the TL engine
**
** Limitations, Assumptions, External Events, and Notes:
**	the global variables: instruction_mem and interval_mem
**	are located in auto-generated files TL_formula.c and TL_formula_int.c
**
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**
**=====================================================================================*/

#include "TL_observers.h"
#include "TL_queue_pt.h"
#include "TL_queue_ft.h"

int t_now;

int r2u2_errno = 0;
int max_time_horizon = 0;

atomics_vector_t	atomics_vector;
atomics_vector_t	atomics_vector_prev;

map_mem_t		map_mem_ft;
map_mem_t		map_mem_pt;

results_pt_t		results_pt;
results_pt_t		results_pt_prev;

results_rising_pt_t	results_pt_rising;

box_queue_mem_pt_t	pt_box_queue_mem;
box_queues_pt_t		pt_box_queues;

sync_queues_ft_t	ft_sync_queues;
SCQ_t SCQ;
