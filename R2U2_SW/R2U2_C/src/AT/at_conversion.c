#include <math.h>
#include "at_checkers.h"
#include "filter_fft.h"
#include "filter_filt.h"
#include "filter_rate.h"

#include "TL_observers.h"

#include "R2U2.h"
#include "R2U2Config.h"

/*****************************************************************
 * declaration of filters
******************************************************************/

/*****************************************************************/
/* initialization of interface                                   */
/*****************************************************************/
void at_checkers_init(){

}


/*****************************************************************/
/* update:                                                       */
/* 	* process incoming data                                  */
/*	* write into atomics vector				 */
/*****************************************************************/
void at_checkers_update(const r2u2_input_data_t *r2u2_input_data){

	DEBUG_PRINT("%s[%d]: %s\n",__FILE__,__LINE__,"at_checkers_update");
    // TODO: Do we only support 4 signals?
	for (int i=0; i< 4; i++){
		atomics_vector[i] = AT_COMP((r2u2_input_data[i]), > , 0.5);
	}
}

/*****************************************************************/
/* freeing of buffers                                            */
/*****************************************************************/
void at_checkers_free(){
}
