/*=======================================================================================
** File Name:  TL_update.c
**
** Title:  Update step for the TL engine
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
**
** Functions Defined:
**	TL_update()
**
** Purpose:
**	execute one time step for the PT and FT engined
**
** Limitations, Assumptions, External Events, and Notes:
**	Resets error before each update step
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


int TL_update(FILE *log_file){

	r2u2_errno = 0;

	TL_update_pt(log_file);
    //TL_update_ft(log_file);
    
	//
	// do temporal housekeeping:
	// data -> data_prev
	// increment time stamp

	//
	// put the current atomics into the previous one
	//
	// TODO: Would it be better to dubble flip buffers?
	memcpy(atomics_vector_prev, atomics_vector, sizeof(atomics_vector_t));

	//
	// increase time stamp
	//
	t_now++;

return 0;
}

