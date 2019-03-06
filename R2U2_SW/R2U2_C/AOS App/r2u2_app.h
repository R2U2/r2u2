/*=======================================================================================
** File Name:  r2u2_app.h
**
** Title:  Header File for R2U2 Application
**
** $Author:    jschuman
** $Revision:  $
** $Date:      2016-6-16
**
** Purpose:  To define R2U2's internal macros, data types, global variables and
**           function prototypes
**
** Modification History:
**   Date | Author | Description
**   ---------------------------
**   2014-12-23 | me | Build #: Code Started
**
**=====================================================================================*/
    
#ifndef _R2U2_APP_H_
#define _R2U2_APP_H_

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
#include <errno.h>
#include <string.h>
#include <unistd.h>

#include "osconfig.h"

#include "TL_observers.h" 

#include "r2u2_platform_cfg.h"
#include "r2u2_mission_cfg.h"
#include "r2u2_private_ids.h"

// #include "mav_bridge_msgids.h"

// #include "r2u2_msgids.h" 

#include "TMPMISSION_mav_bridge_types.h"



/*
** Local Defines
*/
#define R2U2_SCH_PIPE_DEPTH  10
#define R2U2_CMD_PIPE_DEPTH  10
#define R2U2_TLM_PIPE_DEPTH  32

/*
** Local Structure Declarations
*/
typedef struct
{
    /* CFE Event table */
    CFE_EVS_BinFilter_t  EventTbl[R2U2_EVT_CNT];

    /* CFE scheduling pipe */
    CFE_SB_PipeId_t  SchPipeId; 
    uint16           usSchPipeDepth;
    char             cSchPipeName[OS_MAX_API_NAME];

    /* CFE command pipe */
    CFE_SB_PipeId_t  CmdPipeId;
    uint16           usCmdPipeDepth;
    char             cCmdPipeName[OS_MAX_API_NAME];
    
    /* CFE telemetry pipe */
    CFE_SB_PipeId_t  TlmPipeId;
    uint16           usTlmPipeDepth;
    char             cTlmPipeName[OS_MAX_API_NAME];

    /* Task-related */
    uint32  uiRunStatus;
    
    /* Input data - from I/O devices or subscribed from other apps' output data.
       Data structure should be defined in r2u2/fsw/mission_inc/r2u2_private_types.h */
    R2U2_InData_t   InData;

    /* Output data - to be published at the end of a Wakeup cycle.
       Data structure should be defined in $MISSION_TMPMISSION/apps/inc/TMPMISSION_r2u2_types.h */
    R2U2_OutData_t  OutData;

    /* Housekeeping telemetry - for downlink only.
       Data structure should be defined in $MISSION_TMPMISSION/apps/inc/TMPMISSION_r2u2_types.h */
    R2U2_HkTlm_t  HkTlm;

    /* TODO:  Add declarations for additional private data here */
} R2U2_AppData_t;

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
int32  R2U2_AppInit(void);

int32  R2U2_InitEvent(void);
int32  R2U2_InitData(void);
int32  R2U2_InitPipe(void);

void  R2U2_AppMain(void);

void  R2U2_CleanupCallback(void);

int32  R2U2_RcvMsg(int32 iBlocking);

void  R2U2_ProcessNewData(void);
void  R2U2_ProcessNewCmds(void);
void  R2U2_ProcessNewAppCmds(CFE_SB_Msg_t*);

void  R2U2_ReportHousekeeping(void);
void  R2U2_SendOutData(void);

boolean  R2U2_VerifyCmdLength(CFE_SB_Msg_t*, uint16);

/* 
** For Trick compatibility, so that Trick can have visibility to internal variables 
*/
#ifdef __cplusplus
}
#endif

#endif /* _R2U2_APP_H_ */

/*=======================================================================================
** End of file r2u2_app.h
**=====================================================================================*/
    
