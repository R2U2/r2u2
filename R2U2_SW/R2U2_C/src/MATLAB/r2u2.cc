/*
  R2U2: Octave wrapper for R2U2 core algorithm

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

#define BOUNDS_CHECKING
#include <math.h>
#include <octave/config.h>
#include <iostream>
#include <octave/oct.h>
#include <octave/defun-dld.h>
#include <octave/error.h>
#include <octave/oct-obj.h>
#include <octave/pager.h>
#include <octave/symtab.h>
#include <octave/variables.h>
#include <octave/toplev.h>
//#include <octave/Array3.h>
#include <octave/Matrix.h>
#include <octave/parse.h>


#include "TL_observers.h"
#include "at_checkers.h"

	// compatible with matlab interface
	// i.e., the inputs are processed in fortran order
	// i.e., usually called: r2u2(in')
#define R2U2_MATLAB_COMPATIBLE

/*----------------------------------------------
 * OCTAVE INTERFACE FUNCTION
 *----------------------------------------------
*/
int time_unit = 0;

DEFUN_DLD(r2u2,input_args,output_args,
          "[atomics, results_pt, results_ft, results_a_ft, v_times_a_ft, results_BN] = r2u2(inputs)\nFT: sync and async\n"
         )
{
  octave_value_list retval;
  if (input_args.length () != 1 || output_args != 5 ){
    octave_stdout << "[atomics, results_pt, results_ft, results_a_ft, v_times_a_ft, results_BN] = r2u2(inputs)\n";
    return retval;
  }

  //-- Input declarations ----------------------------------------------------

 octave_value arg_sim_data = input_args(0);
 

  if (!arg_sim_data.is_real_matrix()){
    gripe_wrong_type_arg("inputs", (const std::string &)"Matrix expected");
    return retval;
  }
  Matrix inputs = (Matrix)(arg_sim_data.matrix_value());

time_unit++;

#ifdef R2U2_MATLAB_COMPATIBLE
int N_signals = inputs.rows();
int N_timestamps = inputs.columns();
#else
int N_signals = inputs.columns();
int N_timestamps = inputs.rows();
#endif

if (N_signals != N_ATOMICS){
	error("R2U2: Wrong number of input signals (must be N_ATOMICS)\n");
    	return retval;
  	}

Matrix v_atomics(N_timestamps,N_ATOMICS);
Matrix v_results_pt(N_timestamps,N_INSTRUCTIONS);
Matrix v_results_ft(N_timestamps,N_INSTRUCTIONS);
Matrix v_results_a_ft(N_timestamps, N_INSTRUCTIONS);
Matrix v_times_a_ft(N_timestamps, N_INSTRUCTIONS);
Matrix v_results_BN(1,1);

double *signals = new double[N_signals];

	/* start the proper code */

TL_init();
at_checkers_init();


//Writing Debug Output to File
FILE *fp;
if(DEBUG_FILE_OUTPUT == 1){
	fp = fopen("../_Results/testOutput.txt", "w+");
}

//Writing Observer Output to File
FILE *fp2;
fp2 = fopen("../_Results/observerOutput.txt", "w+");
fprintf(fp2, "**********RESULTS**********\n\n");


for (int ts=0; ts< N_timestamps; ts++){
  printf("\n");
  printf("***************************************");
  printf("**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****",ts+1); 
  //index shifted due to octave arrays starting index is 1
  printf("***************************************");
  printf("\n");

  fprintf(fp, "**********CURRENT TIME STEP: %d**********\n\n", ts+1);

  fprintf(fp2, "----------TIME STEP: %d----------\n", ts);

		//
		// work on the ts-th signal vector
		//

#ifdef R2U2_MATLAB_COMPATIBLE
	for (int k=0; k<N_signals; k++){
		signals[k] = inputs(k,ts);
		}
#else
	for (int k=0; k<N_signals; k++){
		signals[k] = inputs(ts,k);
		}
#endif

	at_checkers_update(signals);

		//
		// copy the generated atomics into the
		// atomics output
		//
	for (int k=0; k<N_ATOMICS; k++){
		v_atomics(ts,k) = atomics_vector[k];
		}

#	ifdef DEBUG
	printf("\n[DBG] t=%d; ATOMICS VECTOR:\n",ts);
	for (int k=0; k<N_signals; k++){
		printf("%1.1d",atomics_vector[k]);
      if (k%8 == 7)  printf(" ");
      if (k%32 == 31)  printf("\n");
		}
	printf("\n");
#	endif
	
		//
		// run the TL
		//
	TL_update(fp, fp2);


	fprintf(fp2, "\n");
	fprintf(fp,"\n\n");

		//
		// copy the results into the pt results
		//
	for (int k=0; k<N_INSTRUCTIONS; k++){
		v_results_pt(ts,k) = (double)results_pt[k];
		}

	for (int k=0; k<N_INSTRUCTIONS; k++){
		v_results_ft(ts,k)   = (double)results_ft[k].sync_val;
		}
  
  	for (int k=0; k<N_INSTRUCTIONS; k++){
		v_results_a_ft(ts,k) = (double)results_ft[k].async_val;

		if((double)results_ft[k].async_val != 0.0){
			//printf("NONZERO VALUE FOUND, K=%d\n", k);
		}
		v_times_a_ft(ts,k) = (double)results_ft[k].async_t;
		}
  


#	ifdef DEBUG
	printf("\n[DBG]::DEFUN_DLD: t=%d; RESULTS PT:\n",ts);
	for (int k=0; k<N_INSTRUCTIONS; k++){
		printf("%1.1d",results_pt[k]);
    if (k%8 == 7)  printf(" ");
    if (k%32 == 31)  printf("\n");
		}
	printf("\n[DBG]::DEFUN_DLD: t=%d; RESULTS FT(SYNC):\n",ts);
	for (int k=0; k<N_INSTRUCTIONS; k++){
		printf("%1.1d",results_ft[k].sync_val);
    if (k%8 == 7)  printf(" ");
    if (k%32 == 31)  printf("\n");
		}
	printf("\n[DBG]::DEFUN_DLD: t=%d; RESULTS FT(ASYNC):\n",ts);
	for (int k=0; k<N_INSTRUCTIONS; k++){
		printf("%1.1d",results_ft[k].async_val);
    if (k%8 == 7)  printf(" ");
    if (k%32 == 31)  printf("\n");
		}
	printf("\n");

#	endif

	}

	delete signals;

 	retval.resize(6);
  	retval(0) = v_atomics;
  	retval(1) = v_results_pt;
  	retval(2) = v_results_ft;
	  retval(3) = v_results_a_ft;
  	retval(4) = v_results_BN;
  	retval(5) = v_times_a_ft;



  	//Close the Output File if debugging
  	if(DEBUG_FILE_OUTPUT == 1){
  		fclose(fp);
	}

	fclose(fp2);

	return retval;
}
