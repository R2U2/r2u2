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


int TL_update(FILE *fp, FILE *fp2){

r2u2_errno = 0;

if (t_now == 0){
	memcpy(atomics_vector_prev, atomics_vector, sizeof(atomics_vector_t));
	}

	//
	// run the PT engine
	//
TL_update_pt();


		
	//
	// run the FT engine
	//
TL_update_ft(fp, fp2);

	//
	// do temporal housekeeping:
	// data -> data_prev
	// increment time stamp

	//
	// put the current atomics into the previous one
	//
memcpy(atomics_vector_prev, atomics_vector, sizeof(atomics_vector_t));

	//
	// increase time stamp
	//
t_now++;

return 0;
}

