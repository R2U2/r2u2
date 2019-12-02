/*=======================================================================================
** File Name: at_checkers.h
**
** Title: Macro Definitions for R2U2/AT filters
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2014
**
** Purpose:
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/

#ifndef AT_CHECKERS_H
#define AT_CHECKERS_H

//#define PROGNOSTICS
#ifdef PROGNOSTICS
#	undef PROGNOSTICS
#endif

#include "r2u2_input_types.h"


#include "filter_fft.h"
#include "filter_filt.h"
#include "filter_rate.h"
#include "filter_prognostics.h"
#include "filter_movavg.h"
#include "filter_abs_diff_angle.h"
#include "filter_regex.h"


#ifdef __cplusplus
extern "C" {
#endif
	//
	// top level routines for the entire translation process
	//
void at_checkers_init();
void at_checkers_update(const r2u2_input_data_t *p);
void at_checkers_free();

#ifdef __cplusplus
}
#endif

	//
	// macros for the individual filters and atCheckers
	//
	//	The ID is a unique filter identifier, name, or number
	//

	//-------------------------------------------------------
	//  FFT FILTER
	//-------------------------------------------------------
#define FILTER_FFT_DECL(ID, FFT_SIZE) \
	static fftw_plan filter## ID ##_fftw_plan; \
	static double *filter## ID ##_buf; \
	static fftw_complex *filter## ID ##_obuf;

#define FILTER_FFT_INIT(ID, FFT_SIZE) \
	filter## ID ##_fftw_plan = filter_fft_init(\
		FFT_SIZE, &filter## ID ##_buf, &filter## ID ##_obuf);

#define FILTER_FFT_UPDATE(ID, FFT_SIZE, DATA) \
	filter_fft_update_data(DATA, FFT_SIZE, filter## ID ##_buf, \
		filter## ID ##_obuf, filter## ID ##_fftw_plan);

#define FILTER_FFT_GET(ID, FFT_SIZE, FREQ_IDX) \
	filter_fft_get(filter## ID ##_obuf, FREQ_IDX)

#define FILTER_FFT_FREE(ID) \
	filter_fft_free(filter## ID ##_fftw_plan, \
		filter## ID ##_buf, filter## ID ##_obuf);

#define FILTER_FILT_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");

	//-------------------------------------------------------
	//  FILT FILTER: Lowpass
	//-------------------------------------------------------
#define FILTER_FILT_DECL(ID, FILT_SIZE) \
	static double *filter## ID ##_buf; \
	static double filter## ID ##_filtered_val;

#define FILTER_FILT_INIT(ID, FILT_SIZE) \
	filter_filt_init(FILT_SIZE, &filter## ID ##_buf);

#define FILTER_FILT_UPDATE(ID, FILT_SIZE, DATA) \
	filter## ID ##_filtered_val = \
	 filter_filt_update_data(DATA, FILT_SIZE, filter## ID ##_buf)/FILT_SIZE;

#define FILTER_FILT_GET(ID) \
	filter## ID ##_filtered_val

#define FILTER_FILT_FREE(ID) \
	filter_filt_free(filter## ID ##_buf);

#define FILTER_FILT_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");

	//-------------------------------------------------------
	//  FILT FILTER: Moving Average with Ringbuffer Impl.
	//-------------------------------------------------------
#define FILTER_MOVAVG_DECL(ID, FILT_SIZE) \
	int16_t filter##ID##_space[FILT_SIZE]; \
	circBuf_t filter##ID##_cb = { filter##ID##_space, 0, 0, FILT_SIZE}; \
	movAvg_t filter##ID##_avg = {&filter##ID##_cb, 0, 0, 0, FILT_SIZE};

#define FILTER_MOVAVG_UPDATE(ID, DATA) \
	filter_movavg_update_data(&filter##ID##_avg, DATA);

#define FILTER_MOVAVG_GET(ID) \
	filter_movavg_get(&filter##ID##_avg);
//TODO Implement free

	//-------------------------------------------------------
	//  FILT FILTER: RATE FILTER
	//-------------------------------------------------------
#define FILTER_RATE_DECL(ID, RATE_SIZE) \
	static double filter## ID ##_prev; \
	static double filter## ID ##_rate;

#define FILTER_RATE_INIT(ID, RATE_SIZE) \
	filter_rate_init(&filter## ID ##_prev);

#define FILTER_RATE_UPDATE(ID, RATE_SIZE, DATA) \
	filter## ID ##_rate = \
	 filter_rate_update_data(DATA, &filter## ID ##_prev);

#define FILTER_RATE_GET(ID) \
	filter## ID ##_rate

#define FILTER_RATE_FREE(ID) \
	;

#define FILTER_RATE_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");

	//-------------------------------------------------------
	//  FILT FILTER: RATE_ANGLE
	//	absolute value of RATE for an angle
	//-------------------------------------------------------
#define FILTER_RATE_ANGLE_DECL(ID,DUMMY) \
	static double filter## ID ##_prev; \
	static double filter## ID ##_anglerate;

#define FILTER_RATE_ANGLE_INIT(ID, DUMMY) \
	filter## ID ##_prev = INFINITY;

#define FILTER_RATE_ANGLE_UPDATE(ID, DUMMY, DATA) \
	filter## ID ##_anglerate = \
	  abs_diff_angle(DATA, (isinf(filter## ID ##_prev))?0.0:filter## ID ##_prev); \
	filter## ID ##_prev = DATA;

#define FILTER_RATE_ANGLE_GET(ID) \
	filter## ID ##_anglerate

#define FILTER_RATE_ANGLE_FREE(ID) \
	;

#define FILTER_RATE_ANGLE_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");


	//-------------------------------------------------------
	//  FILT FILTER: ABS_DIFF_ANGLE
	//-------------------------------------------------------
#define FILTER_ABS_DIFF_ANGLE_DECL(ID, DUMMY) \
	static double filter## ID ##_anglediff;

#define FILTER_ABS_DIFF_ANGLE_INIT(ID, DUMMY)

#define FILTER_ABS_DIFF_ANGLE_UPDATE(ID, DUMMY, DATA1, DATA2) \
	filter## ID ##_anglediff = abs_diff_angle(DATA1, DATA2);

#define FILTER_ABS_DIFF_ANGLE_GET(ID) \
	filter## ID ##_anglediff

#define FILTER_ABS_DIFF_ANGLE_FREE(ID) \
	;

#define FILTER_ABS_DIFF_ANGLE_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");

	//-------------------------------------------------------
	//  REGEX FILTER: Regular Expression FILTER
	//-------------------------------------------------------
#define FILTER_REGEX_DECL(ID, MATCHSTRING) \
	static regex_t filter## ID ##_RE; \
	static int filter## ID ##_match;

#define FILTER_REGEX_INIT(ID, MATCHSTRING) \
	filter_regex_init(&filter## ID ##_RE, MATCHSTRING);

#define FILTER_REGEX_UPDATE(ID, MATCHSTRING, DATA) \
	filter## ID ##_match = \
	 filter_regex_update_data(&filter## ID ##_RE, DATA, NULL);

#define FILTER_REGEX_GET(ID) \
	filter## ID ##_match

#define FILTER_REGEX_FREE(ID) \
	filter_regex_free(&filter## ID ##_RE);

#define FILTER_REGEX_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");

	//-------------------------------------------------------
	//  REGEX_BUF FILTER: Regular Expression FILTER for buffer
	//-------------------------------------------------------
#define FILTER_REGEX_PLEXIL_DECL(ID, MATCHSTRING) \
	static regex_t filter## ID ##_RE; \
	static int filter## ID ##_match;

#define FILTER_REGEX_PLEXIL_INIT(ID, MATCHSTRING) \
	filter_regex_init(&filter## ID ##_RE, MATCHSTRING);

#define FILTER_REGEX_PLEXIL_UPDATE(ID, MATCHSTRING, DATA) \
	filter## ID ##_match = \
	 filter_regex_plexil_update_data(&filter## ID ##_RE, DATA, NULL);

#define FILTER_REGEX_PLEXIL_GET(ID) \
	filter## ID ##_match

#define FILTER_REGEX_PLEXIL_FREE(ID) \
	filter_regex_free(&filter## ID ##_RE);

#define FILTER_REGEX_PLEXIL_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");


#ifdef PROGNOSTICS
	//-------------------------------------------------------
	//  PROGNOSTICS FILTER
	//-------------------------------------------------------
#define FILTER_PROGNOSTICS_DECL(ID,NUM) \
	static struct s_prognostics *filter## ID ##_prognostics;

#define FILTER_PROGNOSTICS_INIT(ID,NUM) \
	filter## ID ##_prognostics = filter_prognostics_init();

#define FILTER_PROGNOSTICS_UPDATE(ID, NUM, UBATT, IBATT) \
	filter_prognostics_update(UBATT, IBATT, filter## ID ##_prognostics);

#define FILTER_PROGNOSTICS_GET(ID) \
	filter_prognostics_get_SoC_mean(filter## ID ##_prognostics)

#define FILTER_PROGNOSTICS_GET_RUL(ID) \
	filter_prognostics_get_RUL_mean(filter## ID ##_prognostics)

#define FILTER_PROGNOSTICS_FREE(ID) \
	filter_prognostics_free(filter## ID ##_prognostics);

#define FILTER_FILT_LIST(ID,NAME) \
	fprintf(stderr,"'" #NAME "',\n");
#endif

	//-------------------------------------------------------
	//  COMPARER
	//-------------------------------------------------------
#define AT_COMP(X,OP,Y) \
	((X) OP (Y))?1:0

#define AT_RANGE_INCL(X,LB,UB) \
	(((X) >= (LB)) && ((X) <= (UB)))?1:0

	// this is a Boolean match (for REGEX):
	// match is "1"
#define AT_MATCH(X) \
	((X)?0:1)


	//-------------------------------------------------------
	//  LIST NAME
	//-------------------------------------------------------
#define LIST_CSV_COL_NAME(NAME) \
	fprintf(stderr,"'" #NAME ",\n");




#endif
