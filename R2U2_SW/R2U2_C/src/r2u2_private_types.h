/*=======================================================================================
** File Name:  r2u2_private_types.h
**
** Title:  Type Header File for R2U2 Application
**
** $Author:    me
** $Revision:  $
** $Date:      2014-12-23
**
** Purpose:  This header file contains declarations and definitions of all R2U2's private
**           data structures and data types.
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**   2014-12-23 | me | Build #: Code Started
**
**=====================================================================================*/
    
#ifndef _R2U2_PRIVATE_TYPES_H_
#define _R2U2_PRIVATE_TYPES_H_

/* 
** For Trick compatibility, so that Trick can have visibility to internal variables 
*/
#ifdef __cplusplus
extern "C" {
#endif

/*
** Pragmas
*/

/*
** Include Files
**
** Be sure to include all .h files that define types used in this .h file.
** Trick requires this in order to get visibility into internal variables.
*/
#include "cfe.h"

#include "mavlink.h"

/*
** Local Defines
*/
#define R2U2_N_PLEXIL_MSG	10
#define R2U2_PLEXIL_MSG_LENGTH	256

/*
** Local Structure Declarations
*/

	//
	// data type for buffer for PLEXIL messages on AOS side
	//
typedef struct {
	CCSDS_TlmPkt_t tlmHdr;
	char	plexil_msg[R2U2_PLEXIL_MSG_LENGTH];
	} OS_PACK plexil_tlm_msg_t;


	//
	// data type for buffer for PLEXIL messages on R2U2 side
	//
typedef struct {
	char	plexil_msg[R2U2_N_PLEXIL_MSG][R2U2_PLEXIL_MSG_LENGTH];
	int	N;
	} plexil_r2u2_msgbuf_t;


	//
	// input buffer/structure for R2U2
	//
	// MAVLINK definitions in: sil/mavlink/mavlink/common
	//
	// PLEXIL events: TBD
	//
typedef struct { 
		// MAV-HEARTBEAT
	mavlink_heartbeat_t	mav_heartbeat;
	int			mav_heartbeat_exp;

		// MAV-SYS-STATUS MESSAGE
	mavlink_sys_status_t	mav_sys_status;
	int mav_sys_status_exp;

		// MAV-SYSTEM-TIME
	mavlink_system_time_t	mav_system_time;
	int			mav_system_time_exp;

		// MAV-GLOBAL-POSITION-INT MESSAGE
	mavlink_global_position_int_t	mav_global_position_int;
	int 				mav_global_position_int_exp;

		// MAV-MISSION-CURRENT
	mavlink_mission_current_t	mav_mission_current;
	int				mav_mission_current_exp;

		// MAV-MISSION-REACHED
	mavlink_mission_item_reached_t	mav_mission_item_reached;
	int				mav_mission_item_reached_exp;

		// MAV-NAV-CNTRL-OUT
	mavlink_nav_controller_output_t	mav_nav_controller_output;
	int 				mav_nav_controller_output_exp;


	plexil_r2u2_msgbuf_t		plexil_r2u2_msgbuf;
	int				plexil_r2u2_msgbuf_exp;

		// ...  [TODO: other relevant message data]

	} r2u2_input_data_t;

typedef struct
{
    uint32  counter;
   
    r2u2_input_data_t r2u2_input_data;

} R2U2_InData_t;




/*
** External Global Variables
*/

/*
** Global Variables
*/

/*
** Local Variables
*/

/*
** Local Function Prototypes
*/

/* 
** For Trick compatibility, so that Trick can have visibility to internal variables 
*/
#ifdef __cplusplus
}
#endif

#endif /* _R2U2_PRIVATE_TYPES_H_ */

/*=======================================================================================
** End of file r2u2_private_types.h
**=====================================================================================*/
    
