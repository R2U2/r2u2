/*
  R2U2: Matlab wrapper for R2U2 core algorithm

  usage:
     [atomics, results_pt, results_ft, results_BN] = r2u2(inputs);

  where:
     inputs=csvread('flight_data.csv');
     

  returns:

  MAKE:

  AUTHOR:
     Johann Schumann
	V0.0 4/13/2016

*/


#include <math.h>
#include "mex.h"

#include "TL_observers.h"
#include "at_checkers.h"

//void at_checkers_init(){};
//void at_checkers_update(double *input_data){};

/*----------------------------------------------
 * MATLAB INTERFACE FUNCTION
 *----------------------------------------------
*/

void mexFunction( int nlhs, mxArray *plhs[],
        int nrhs, const mxArray *prhs[])
{


////////////////////

double 		*input_data;
int 		out_dims[2];
int 		N_timestamps;
int 		N_signals;

uint32_t	*p_atomics;	
uint32_t	*p_results_pt;	

int i;
int k;
int ts;

if (nrhs != 1 || nlhs != 4 ){
  mexErrMsgTxt("usage: [at,pt_res,ft_res,BN_res=r2u2(input)\n");
  return;	
  }

   	/* get the data matrix */
N_signals = mxGetM(prhs[0]);
N_timestamps = mxGetN(prhs[0]);

	/*
	** this is ONLY for the dummy atomics preprocessing
	** for proper preprocessing this must be
	** the number of inputs to the at_checkers unit
	*/
if (N_signals != N_ATOMICS){
  mexErrMsgTxt("Wrong number of input signals (must be N_ATOMICS)\n");
  return;
  }

input_data = (double *)mxGetPr(prhs[0]);

	/* create outputs */
out_dims[0] = N_timestamps;
out_dims[1] = N_ATOMICS;
plhs[0] = mxCreateNumericArray(2,out_dims, mxUINT32_CLASS,
		mxREAL);
p_atomics = (uint32_t *)mxGetPr(plhs[0]);

	/* create outputs */
out_dims[0] = N_timestamps;
out_dims[1] = N_INSTRUCTIONS;
plhs[1] = mxCreateNumericArray(2,out_dims, mxUINT32_CLASS,
		mxREAL);
p_results_pt = (uint32_t *)mxGetPr(plhs[1]);


	/* NYI for ft and BN: return scalars for now */
plhs[2] = mxCreateDoubleMatrix(1, 1, mxREAL);
*(mxGetPr(plhs[2])) = -1;
plhs[3] = mxCreateDoubleMatrix(1, 1, mxREAL);
*(mxGetPr(plhs[3])) = -1;

	/* start the proper code */

TL_init();
at_checkers_init();


for (ts=0; ts< N_timestamps; ts++){

		//
		// work on the i-th signal vector
		//
	at_checkers_update(input_data+ts*N_signals);

		//
		// copy the generated atomics into the
		// atomics output
		//
	for (k=0; k<N_ATOMICS; k++){
		*(p_atomics + k*N_timestamps + ts) = atomics_vector[k];
		}

#	ifdef DEBUG
	for (k=0; k<N_ATOMICS; k++){
		printf("%1.1d",atomics_vector[k]);
		}
	printf("\n");
#	endif
	
		//
		// run the TL
		//
	TL_update();

		//
		// copy the results into the pt results
		//
	for (k=0; k<N_INSTRUCTIONS; k++){
		*(p_results_pt + k*N_timestamps + ts) = (uint32_t)results_pt[k];
		}
#	ifdef DEBUG
	for (k=0; k<N_INSTRUCTIONS; k++){
		printf("%1.1d",results_pt[k]);
		}
	printf("\n");
#	endif

	}

return;
}
