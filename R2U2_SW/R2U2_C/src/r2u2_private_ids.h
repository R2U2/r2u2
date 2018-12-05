/*=======================================================================================
** File Name:  r2u2_private_ids.h
**
** Title:  ID Header File for R2U2 Application
**
** $Author:    me
** $Revision:  $
** $Date:      2014-12-23
**
** Purpose:  This header file contains declarations and definitions of R2U2's private IDs.
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**   2014-12-23 | me | Build #: Code Started
**
**=====================================================================================*/
    
#ifndef _R2U2_PRIVATE_IDS_H_
#define _R2U2_PRIVATE_IDS_H_

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
*/

/*
** Local Defines
**
** Be sure to include all .h files that define types used in this .h file.
** Trick requires this in order to get visibility into internal variables.
*/

#define     R2U2_MAIN_TASK_PERF_ID      0x0082

/* Event IDs */
#define R2U2_RESERVED_EID  0

#define R2U2_INF_EID        1
#define R2U2_INIT_INF_EID   2
#define R2U2_ILOAD_INF_EID  3
#define R2U2_CDS_INF_EID    4
#define R2U2_CMD_INF_EID    5

#define R2U2_ERR_EID         51
#define R2U2_INIT_ERR_EID    52
#define R2U2_ILOAD_ERR_EID   53
#define R2U2_CDS_ERR_EID     54
#define R2U2_CMD_ERR_EID     55
#define R2U2_PIPE_ERR_EID    56
#define R2U2_MSGID_ERR_EID   57
#define R2U2_MSGLEN_ERR_EID  58

#define R2U2_EVT_CNT  14

#define R2U2_NOOP_CC			0
#define R2U2_RESET_CC			1

/*
** Local Structure Declarations
*/

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

#endif /* _R2U2_PRIVATE_IDS_H_ */

/*=======================================================================================
** End of file r2u2_private_ids.h
**=====================================================================================*/
    
