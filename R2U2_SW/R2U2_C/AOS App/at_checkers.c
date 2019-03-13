// auto-generated do not modify
// from specification file spec.txt

#define R2U2_AOS
#include <math.h>
#include "at_checkers.h"
#include "filter_fft.h"
#include "filter_filt.h"
#include "filter_rate.h"
#include "filter_regex.h"
#include "filter_prognostics.h"
#include "TL_observers.h"




//*****************************************************
// declaration of filters
//*****************************************************
FILTER_FILT_DECL(voltage_battery_smooth,2)
FILTER_FILT_DECL(current_battery_smooth,2)
FILTER_RATE_DECL(relative_alt_rate,0)
FILTER_RATE_ANGLE_DECL(nav_target_bearing_rate,0)
FILTER_ABS_DIFF_ANGLE_DECL(bearing_difference,0)
FILTER_REGEX_PLEXIL_DECL(cleared_alt_X,"^.*AOS: cleared for altitude [1-9][1-9]*")
FILTER_REGEX_PLEXIL_DECL(commanding_alt_X,"^.*UAV: commanding altitude [1-9][1-9]*")
FILTER_REGEX_PLEXIL_DECL(climbing_alt_X,"^.*AOS: climbing to [1-9][1-9]*")
FILTER_REGEX_PLEXIL_DECL(reached_alt_X,"^.*UAV: reached altitude [1-9][1-9]*")
FILTER_REGEX_PLEXIL_DECL(maintain_alt_X,"^.*AOS: maintaining altitude [1-9][1-9]*")
FILTER_REGEX_PLEXIL_DECL(maintain_alt_25,"^.*AOS: maintaining altitude 25")
FILTER_REGEX_PLEXIL_DECL(WP_in_progress,"^.*AOS: Waypoint [A-Z][A-Z]* in progress")
FILTER_REGEX_PLEXIL_DECL(WP_cleared,"^.*AOS: cleared for waypoint [A-Z][A-Z]*")
FILTER_REGEX_PLEXIL_DECL(WP_achieved,"^.*AOS: element achieved: Waypoint [A-Z][A-Z]*")



//*****************************************************
// initialization of filters
//*****************************************************
void at_checkers_init(){
	FILTER_FILT_INIT(voltage_battery_smooth,2);
	FILTER_FILT_INIT(current_battery_smooth,2);
	FILTER_RATE_INIT(relative_alt_rate,0);
	FILTER_RATE_ANGLE_INIT(nav_target_bearing_rate,0);
	FILTER_ABS_DIFF_ANGLE_INIT(bearing_difference,0);
	FILTER_REGEX_PLEXIL_INIT(cleared_alt_X,"^.*AOS: cleared for altitude [1-9][1-9]*");
	FILTER_REGEX_PLEXIL_INIT(commanding_alt_X,"^.*UAV: commanding altitude [1-9][1-9]*");
	FILTER_REGEX_PLEXIL_INIT(climbing_alt_X,"^.*AOS: climbing to [1-9][1-9]*");
	FILTER_REGEX_PLEXIL_INIT(reached_alt_X,"^.*UAV: reached altitude [1-9][1-9]*");
	FILTER_REGEX_PLEXIL_INIT(maintain_alt_X,"^.*AOS: maintaining altitude [1-9][1-9]*");
	FILTER_REGEX_PLEXIL_INIT(maintain_alt_25,"^.*AOS: maintaining altitude 25");
	FILTER_REGEX_PLEXIL_INIT(WP_in_progress,"^.*AOS: Waypoint [A-Z][A-Z]* in progress");
	FILTER_REGEX_PLEXIL_INIT(WP_cleared,"^.*AOS: cleared for waypoint [A-Z][A-Z]*");
	FILTER_REGEX_PLEXIL_INIT(WP_achieved,"^.*AOS: element achieved: Waypoint [A-Z][A-Z]*");
}




//*****************************************************
// clean up filters
//*****************************************************
void at_checkers_free(){
	FILTER_FILT_FREE(voltage_battery_smooth);
	FILTER_FILT_FREE(current_battery_smooth);
	FILTER_RATE_FREE(relative_alt_rate);
	FILTER_RATE_ANGLE_FREE(nav_target_bearing_rate);
	FILTER_ABS_DIFF_ANGLE_FREE(bearing_difference);
	FILTER_REGEX_PLEXIL_FREE(cleared_alt_X);
	FILTER_REGEX_PLEXIL_FREE(commanding_alt_X);
	FILTER_REGEX_PLEXIL_FREE(climbing_alt_X);
	FILTER_REGEX_PLEXIL_FREE(reached_alt_X);
	FILTER_REGEX_PLEXIL_FREE(maintain_alt_X);
	FILTER_REGEX_PLEXIL_FREE(maintain_alt_25);
	FILTER_REGEX_PLEXIL_FREE(WP_in_progress);
	FILTER_REGEX_PLEXIL_FREE(WP_cleared);
	FILTER_REGEX_PLEXIL_FREE(WP_achieved);
}




//*****************************************************
// update filters and set atomics
//*****************************************************
void at_checkers_update(const r2u2_input_data_t *r2u2_input_data){


double voltage_battery_smooth;
double current_battery_smooth;
double bearing_difference;
double nav_target_bearing_rate;
double relative_alt_rate;


	FILTER_FILT_UPDATE(voltage_battery_smooth,2,
		r2u2_input_data->mav_sys_status.voltage_battery);
	voltage_battery_smooth = FILTER_FILT_GET(voltage_battery_smooth);


	atomics_vector[0] = AT_COMP(voltage_battery_smooth,<,12000);


	atomics_vector[1] = AT_COMP(voltage_battery_smooth,>,14000);


	atomics_vector[2] = AT_RANGE_INCL(voltage_battery_smooth,12000,14000);


	FILTER_FILT_UPDATE(current_battery_smooth,2,
		r2u2_input_data->mav_sys_status.current_battery);
	current_battery_smooth = FILTER_FILT_GET(current_battery_smooth);


	atomics_vector[3] = AT_COMP(current_battery_smooth,<,0);


	atomics_vector[4] = AT_COMP(current_battery_smooth,>=,5000);


	atomics_vector[5] = AT_COMP(current_battery_smooth,>,2800);


	atomics_vector[6] = AT_COMP(current_battery_smooth,>,2500);


	atomics_vector[7] = AT_COMP(current_battery_smooth,<,2500);


	atomics_vector[8] = AT_COMP(r2u2_input_data->mav_global_position_int.vz,>,30);


	atomics_vector[9] = AT_COMP(r2u2_input_data->mav_global_position_int.vz,<,-30);


	atomics_vector[10] = AT_RANGE_INCL(r2u2_input_data->mav_global_position_int.vz,-30,30);


	FILTER_RATE_UPDATE(relative_alt_rate,0,
		r2u2_input_data->mav_global_position_int.relative_alt);
	relative_alt_rate = FILTER_RATE_GET(relative_alt_rate);


	atomics_vector[11] = AT_COMP(relative_alt_rate,>,500);


	atomics_vector[12] = AT_COMP(relative_alt_rate,<,-500);


	atomics_vector[13] = AT_RANGE_INCL(relative_alt_rate,-500,500);


	FILTER_RATE_ANGLE_UPDATE(nav_target_bearing_rate,0,
		r2u2_input_data->mav_nav_controller_output.target_bearing);
	nav_target_bearing_rate = FILTER_RATE_ANGLE_GET(nav_target_bearing_rate);


	atomics_vector[14] = AT_COMP(nav_target_bearing_rate,>,10);


	FILTER_ABS_DIFF_ANGLE_UPDATE(bearing_difference,0,
		r2u2_input_data->mav_nav_controller_output.nav_bearing, r2u2_input_data->mav_nav_controller_output.target_bearing);
	bearing_difference = FILTER_ABS_DIFF_ANGLE_GET(bearing_difference);


	atomics_vector[15] = AT_COMP(bearing_difference,<,10);


	FILTER_REGEX_PLEXIL_UPDATE(cleared_alt_X,"^.*AOS: cleared for altitude [1-9][1-9]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[16] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(cleared_alt_X));


	FILTER_REGEX_PLEXIL_UPDATE(commanding_alt_X,"^.*UAV: commanding altitude [1-9][1-9]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[17] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(commanding_alt_X));


	FILTER_REGEX_PLEXIL_UPDATE(climbing_alt_X,"^.*AOS: climbing to [1-9][1-9]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[18] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(climbing_alt_X));


	FILTER_REGEX_PLEXIL_UPDATE(reached_alt_X,"^.*UAV: reached altitude [1-9][1-9]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[19] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(reached_alt_X));


	FILTER_REGEX_PLEXIL_UPDATE(maintain_alt_X,"^.*AOS: maintaining altitude [1-9][1-9]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[20] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(maintain_alt_X));


	FILTER_REGEX_PLEXIL_UPDATE(maintain_alt_25,"^.*AOS: maintaining altitude 25",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[21] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(maintain_alt_25));


	FILTER_REGEX_PLEXIL_UPDATE(WP_in_progress,"^.*AOS: Waypoint [A-Z][A-Z]* in progress",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[22] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(WP_in_progress));


	FILTER_REGEX_PLEXIL_UPDATE(WP_cleared,"^.*AOS: cleared for waypoint [A-Z][A-Z]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[23] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(WP_cleared));


	FILTER_REGEX_PLEXIL_UPDATE(WP_achieved,"^.*AOS: element achieved: Waypoint [A-Z][A-Z]*",
		r2u2_input_data->plexil_r2u2_msgbuf);
	atomics_vector[24] = AT_MATCH(FILTER_REGEX_PLEXIL_GET(WP_achieved));
}

