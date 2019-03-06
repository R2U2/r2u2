/*=======================================================================================
** File Name: r2u2_app.c
**
** Title: Function Definitions for R2U2 Application
**
** $Author:  me
** $Revision: $
** $Date:   2014-12-23
**
** Purpose: This source file contains all necessary function definitions to run R2U2
**      application.
**
** Functions Defined:
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**  2014-12-23 | me | Build #: Code Started
**
**=====================================================================================*/

/*
** Pragmas
*/

/*
** Include Files
*/
#include <string.h>

#include <time.h> 
#include <stdlib.h>


#include "cfe.h"

#include "r2u2_app.h"


/*
** Local Defines
*/

	/* R2U2 is running as an AOS app */
#define R2U2_AOS

	/* print R2U2 input and output vectors */
#define R2U2_VERBOSE

	/* print various DEBUGGING output */
// #define R2U2_DEBUG


#include "TL_observers.h"
#include "at_checkers.h"

/*
** Local Structure Declarations
*/
/*
** External Global Variables
*/

/*
** Global Variables
*/
R2U2_AppData_t g_R2U2_AppData;

/*
** Local Variables
*/

/*
** Local Function Definitions
*/
static	void OS_print_signals();
  
/*=====================================================================================
** Name: R2U2_InitEvent
**
** Purpose: To initialize and register event table for R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  int32 iStatus - Status of initialization
**
** Routines Called:
**  CFE_EVS_Register
**  CFE_ES_WriteToSysLog
**
** Called By:
**  R2U2_AppInit
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  g_R2U2_AppData.EventTbl
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
int32 R2U2_InitEvent()
{
  int32 iStatus=CFE_SUCCESS;

  /* Create the event table */
  memset((void*)g_R2U2_AppData.EventTbl, 0x00, sizeof(g_R2U2_AppData.EventTbl));

  g_R2U2_AppData.EventTbl[0].EventID = R2U2_RESERVED_EID;
  g_R2U2_AppData.EventTbl[1].EventID = R2U2_INF_EID;
  g_R2U2_AppData.EventTbl[2].EventID = R2U2_INIT_INF_EID;
  g_R2U2_AppData.EventTbl[3].EventID = R2U2_ILOAD_INF_EID;
  g_R2U2_AppData.EventTbl[4].EventID = R2U2_CDS_INF_EID;
  g_R2U2_AppData.EventTbl[5].EventID = R2U2_CMD_INF_EID;

  g_R2U2_AppData.EventTbl[ 6].EventID = R2U2_ERR_EID;
  g_R2U2_AppData.EventTbl[ 7].EventID = R2U2_INIT_ERR_EID;
  g_R2U2_AppData.EventTbl[ 8].EventID = R2U2_ILOAD_ERR_EID;
  g_R2U2_AppData.EventTbl[ 9].EventID = R2U2_CDS_ERR_EID;
  g_R2U2_AppData.EventTbl[10].EventID = R2U2_CMD_ERR_EID;
  g_R2U2_AppData.EventTbl[11].EventID = R2U2_PIPE_ERR_EID;
  g_R2U2_AppData.EventTbl[12].EventID = R2U2_MSGID_ERR_EID;
  g_R2U2_AppData.EventTbl[13].EventID = R2U2_MSGLEN_ERR_EID;

  /* Register the table with CFE */
  iStatus = CFE_EVS_Register(g_R2U2_AppData.EventTbl,
                R2U2_EVT_CNT, CFE_EVS_BINARY_FILTER);
  if (iStatus != CFE_SUCCESS)
  {
    CFE_ES_WriteToSysLog("R2U2 - Failed to register with EVS (0x%08X)\n", iStatus);
  }

  return (iStatus);
}
  
/*=====================================================================================
** Name: R2U2_InitPipe
**
** Purpose: To initialize all message pipes and subscribe to messages for R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  int32 iStatus - Status of initialization
**
** Routines Called:
**  CFE_SB_CreatePipe
**  CFE_SB_Subscribe
**  CFE_ES_WriteToSysLog
**
** Called By:
**  R2U2_AppInit
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  g_R2U2_AppData.usSchPipeDepth
**  g_R2U2_AppData.cSchPipeName
**  g_R2U2_AppData.SchPipeId
**  g_R2U2_AppData.usCmdPipeDepth
**  g_R2U2_AppData.cCmdPipeName
**  g_R2U2_AppData.CmdPipeId
**  g_R2U2_AppData.usTlmPipeDepth
**  g_R2U2_AppData.cTlmPipeName
**  g_R2U2_AppData.TlmPipeId
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
int32 R2U2_InitPipe()
{
  int32 iStatus=CFE_SUCCESS;

  /* Init schedule pipe */
  g_R2U2_AppData.usSchPipeDepth = R2U2_SCH_PIPE_DEPTH;
  memset((void*)g_R2U2_AppData.cSchPipeName, '\0', sizeof(g_R2U2_AppData.cSchPipeName));
  strncpy(g_R2U2_AppData.cSchPipeName, "R2U2_SCH_PIPE", OS_MAX_API_NAME-1);

  /* Subscribe to Wakeup messages */
  iStatus = CFE_SB_CreatePipe(&g_R2U2_AppData.SchPipeId,
                 g_R2U2_AppData.usSchPipeDepth,
                 g_R2U2_AppData.cSchPipeName);
  if (iStatus == CFE_SUCCESS)
  {
		//
		// JSC: subscribe to R2U2 wakeup
		//
    CFE_SB_Subscribe(R2U2_WAKEUP_MID, g_R2U2_AppData.SchPipeId);
  }
  else
  {
    CFE_ES_WriteToSysLog("R2U2 - Failed to create SCH pipe (0x%08X)\n", iStatus);
    goto R2U2_InitPipe_Exit_Tag;
  }

  /* Init command pipe */
  g_R2U2_AppData.usCmdPipeDepth = R2U2_CMD_PIPE_DEPTH ;
  memset((void*)g_R2U2_AppData.cCmdPipeName, '\0', sizeof(g_R2U2_AppData.cCmdPipeName));
  strncpy(g_R2U2_AppData.cCmdPipeName, "R2U2_CMD_PIPE", OS_MAX_API_NAME-1);

  /* Subscribe to command messages */
  iStatus = CFE_SB_CreatePipe(&g_R2U2_AppData.CmdPipeId,
                 g_R2U2_AppData.usCmdPipeDepth,
                 g_R2U2_AppData.cCmdPipeName);
  if (iStatus == CFE_SUCCESS)
  {
		//
		// JSC
		// these are sent by MAVBRIDGE to R2U2
		//
		// these are also R2U2
		//
    CFE_SB_Subscribe(R2U2_CMD_MID, g_R2U2_AppData.CmdPipeId);
    CFE_SB_Subscribe(R2U2_SEND_HK_MID, g_R2U2_AppData.CmdPipeId);
  }
  else
  {
    CFE_ES_WriteToSysLog("R2U2 - Failed to create CMD pipe (0x%08X)\n", iStatus);
    goto R2U2_InitPipe_Exit_Tag;
  }

  /* Init telemetry pipe */
  g_R2U2_AppData.usTlmPipeDepth = R2U2_TLM_PIPE_DEPTH;
  memset((void*)g_R2U2_AppData.cTlmPipeName, '\0', sizeof(g_R2U2_AppData.cTlmPipeName));
  strncpy(g_R2U2_AppData.cTlmPipeName, "R2U2_TLM_PIPE", OS_MAX_API_NAME-1);

  /* Subscribe to telemetry messages on the telemetry pipe */
  iStatus = CFE_SB_CreatePipe(&g_R2U2_AppData.TlmPipeId,
                 g_R2U2_AppData.usTlmPipeDepth,
                 g_R2U2_AppData.cTlmPipeName);
  if (iStatus == CFE_SUCCESS)
  {
    /* TODO: Add CFE_SB_Subscribe() calls for other apps' output data here.
    **
    ** Examples:
    **   CFE_SB_Subscribe(GNCEXEC_OUT_DATA_MID, g_R2U2_AppData.TlmPipeId);
    */
    
    /* subscribe to mav_bridge and other messages */
    /* MID defined in app_msgids.h */

	//
	// JSC 
	// subscribe to the appropriate messages
	// published by the MAVBRIDGE
	//
	// Messages published by PLEXIL would go here as well
	// see EXAMPLE
	//

    CFE_SB_Subscribe(MB_HEARTBEAT_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_SYS_STAT_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_SYS_TIME_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_GLOB_POSI_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_MIS_CUR_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_MIS_REACH_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(MB_NAV_CNTR_MID, g_R2U2_AppData.TlmPipeId);
    CFE_SB_Subscribe(PLEXIL_R2U2_TLM_MID, g_R2U2_AppData.TlmPipeId);

    //example:
    //  CFE_SB_Subscribe(PLEXIL_AIRPORT_MID, g_R2U2_AppData.TlmPipeId);

  }
  else
  {
    CFE_ES_WriteToSysLog("R2U2 - Failed to create TLM pipe (0x%08X)\n", iStatus);
    goto R2U2_InitPipe_Exit_Tag;
  }

R2U2_InitPipe_Exit_Tag:
  return (iStatus);
}
  
/*=====================================================================================
** Name: R2U2_InitData
**
** Purpose: To initialize global variables used by R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  int32 iStatus - Status of initialization
**
** Routines Called:
**  CFE_SB_InitMsg
**
** Called By:
**  R2U2_AppInit
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  g_R2U2_AppData.InData
**  g_R2U2_AppData.OutData
**  g_R2U2_AppData.HkTlm
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
int32 R2U2_InitData()
{
  int32 iStatus=CFE_SUCCESS;

  /* Init input data */
  memset((void*)&g_R2U2_AppData.InData, 0x00, sizeof(g_R2U2_AppData.InData));

  /* Init output data */
  memset((void*)&g_R2U2_AppData.OutData, 0x00, sizeof(g_R2U2_AppData.OutData));

  CFE_SB_InitMsg(&g_R2U2_AppData.OutData,
          R2U2_OUT_DATA_MID, sizeof(g_R2U2_AppData.OutData), TRUE);

  /* Init housekeeping packet */
  memset((void*)&g_R2U2_AppData.HkTlm, 0x00, sizeof(g_R2U2_AppData.HkTlm));
  CFE_SB_InitMsg(&g_R2U2_AppData.HkTlm,
          R2U2_HK_TLM_MID, sizeof(g_R2U2_AppData.HkTlm), TRUE);

  return (iStatus);
}
  
/*=====================================================================================
** Name: R2U2_AppInit
**
** Purpose: To initialize all data local to and used by R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  int32 iStatus - Status of initialization
**
** Routines Called:
**  CFE_ES_WriteToSysLog
**  CFE_EVS_SendEvent
**  OS_TaskInstallDeleteHandler
**  R2U2_InitEvent
**  R2U2_InitPipe
**  R2U2_InitData
**
** Called By:
**  R2U2_AppMain
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
int32 R2U2_AppInit()
{
  int32 iStatus=CFE_SUCCESS;

	//JSC: why
  srand(time(NULL)); /* added jpc for random number */

  g_R2U2_AppData.uiRunStatus = CFE_ES_APP_RUN;

  if ((R2U2_InitEvent() != CFE_SUCCESS) || 
    (R2U2_InitPipe() != CFE_SUCCESS) || 
    (R2U2_InitData() != CFE_SUCCESS))
  {
    iStatus = -1;
    goto R2U2_AppInit_Exit_Tag;
  }

  /* Install the cleanup callback */
  OS_TaskInstallDeleteHandler((void*)&R2U2_CleanupCallback);

	//
	// JSC: initialize the components of R2U2
	//
#ifdef R2U2_DEBUG
	OS_printf("JSC: R2U2: init...\n");
#endif
	at_checkers_init();
	TL_init();
#ifdef R2U2_DEBUG
	OS_printf("JSC: R2U2: init done\n");
#endif
	// handle possible start-up errors
	if (r2u2_errno != 0){
    		iStatus = -1;
		}

R2U2_AppInit_Exit_Tag:
  if (iStatus == CFE_SUCCESS)
  {
    CFE_EVS_SendEvent(R2U2_INIT_INF_EID, CFE_EVS_INFORMATION,
             "R2U2 - Application initialized");
  }
  else
  {
    CFE_ES_WriteToSysLog("R2U2 - Application failed to initialize\n");
  }

  return (iStatus);
}
  
/*=====================================================================================
** Name: R2U2_CleanupCallback
**
** Purpose: To handle any neccesary cleanup prior to application exit
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  TBD
**
** Called By:
**  TBD
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_CleanupCallback()
{
  /* TODO: Add code to cleanup memory and other cleanup here */

	//
	// JSC: clean up R2U2
	//
#ifdef R2U2_DEBUG
	OS_printf("JSC: R2U2: cleanup\n");
#endif
	at_checkers_free();
#ifdef R2U2_DEBUG
	OS_printf("JSC: R2U2: cleanup done\n");
#endif

}
  
/*=====================================================================================
** Name: R2U2_RcvMsg
**
** Purpose: To receive and process messages for R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  int32 iStatus - Status of initialization 
**
** Routines Called:
**  CFE_SB_RcvMsg
**  CFE_SB_GetMsgId
**  CFE_EVS_SendEvent
**  R2U2_ProcessNewCmds
**  R2U2_ProcessNewData
**  R2U2_SendOutData
**
** Called By:
**  R2U2_Main
**
** Global Inputs/Reads:
**  g_R2U2_AppData.SchPipeId
**
** Global Outputs/Writes:
**  g_R2U2_AppData.uiRunStatus
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
int32 R2U2_RcvMsg(int32 iBlocking)
{
  int32      iStatus=CFE_SUCCESS;
  CFE_SB_Msg_t*  MsgPtr=NULL;
  CFE_SB_MsgId_t MsgId;

	int i;
       
  /* Wait for WakeUp messages from scheduler */
  iStatus = CFE_SB_RcvMsg(&MsgPtr, g_R2U2_AppData.SchPipeId, iBlocking);
    
  if (iStatus == CFE_SUCCESS)
  {
    MsgId = CFE_SB_GetMsgId(MsgPtr);
    switch (MsgId)
    {
      case R2U2_WAKEUP_MID:
        R2U2_ProcessNewCmds();
        R2U2_ProcessNewData();

		//
		// JSC: 
		// Perform one R2U2 update: AT + TL + BN
		// data are in the r2u2_input_data structure
		//
		//

		// we increment the expiration counter for each wakeup
		// = timestamp
		//
		// This information can be used by the TL to deal with
		// old and stale data

	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_system_time_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_current_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_item_reached_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output_exp++;
	  g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf_exp++;


          		// EXAMPLE:
	  // g_R2U2_AppData.InData.r2u2_input_data.plexil_ap_exp++;


#ifdef R2U2_DEBUG
	  OS_printf("JSC: R2U2: TL_update\n");
#endif

#ifdef R2U2_VERBOSE
	  OS_print_signals();
#endif

		//
		// run the signal preprocessing
		//
	  at_checkers_update(&g_R2U2_AppData.InData.r2u2_input_data);

		//
		// clear the plexil message buffer
		//
	  g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf.N = 0;

#	  ifdef R2U2_VERBOSE
		//
		// print the discretized AT vector
		//
	    OS_printf("R2U2: AT=[");
	    for (i=0; i<128;i++){
		  OS_printf("%d ",atomics_vector[i]);
		  }
	    OS_printf("]\n");
#	   endif

		//
		// run the TL processor
	   TL_update();
		//
		// later: run the Bayes Net 
	   // BN_update();

#	  ifdef R2U2_VERBOSE
	    OS_printf("R2U2: Update: r2u2_errno=%d\n", r2u2_errno);
	    OS_printf("R2U2: PT_RES=[");
	    for (i=0; i<256;i++){
		  OS_printf("%d ",results_pt[i]);
		  }
	    OS_printf("]\n");
#	  endif

#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: TL_update done\n");
#endif

		//
		// assemble output package with R2U2 results
		// and send it

		// in case, an error occurred during the update,
		// the output message will contain that
		//

          R2U2_SendOutData();
        break;

      default:
        R2U2_ProcessNewData();
			//
			// JSC: UNCLEAR????
			//
    }
  }
  else if (iStatus == CFE_SB_NO_MESSAGE)
  {
    /* If there's no incoming message, you can do something here, or do nothing */
  }
  else
  {
    /* This is an example of exiting on an error.
    ** Note that a SB read error is not always going to result in an app quitting.
    */
    CFE_EVS_SendEvent(R2U2_PIPE_ERR_EID, CFE_EVS_ERROR,
             "R2U2: SB pipe read error (0x%08X), app will exit", iStatus);
    g_R2U2_AppData.uiRunStatus= CFE_ES_APP_ERROR;
  }
  
  return (iStatus);
}
  
/*=====================================================================================
** Name: R2U2_ProcessNewData
**
** Purpose: To process incoming data subscribed by R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  CFE_SB_RcvMsg
**  CFE_SB_GetMsgId
**  CFE_EVS_SendEvent
**
** Called By:
**  R2U2_RcvMsg
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  None
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_ProcessNewData()
{
  CFE_SB_Msg_t*  TlmMsgPtr=NULL;
  CFE_SB_MsgId_t TlmMsgId;
  boolean     bGotNewMsg=TRUE;
  int N;

  while (bGotNewMsg)
  {
    if (CFE_SB_RcvMsg(&TlmMsgPtr, g_R2U2_AppData.TlmPipeId, CFE_SB_POLL) == CFE_SUCCESS)
    {
      TlmMsgId = CFE_SB_GetMsgId(TlmMsgPtr);
		//
		// process each message in the pipeline
		// copy to local buffer
		// reset the "exp" timer
		//
      switch (TlmMsgId)
      {
        //----------------------------------------------------------------
#ifdef FIX_ME
		/* this is the HEARTBEAT-MID????? */
        case R2U2_WAKEUP_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: Heartbeat\n");
#endif
	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.mav_counter =
                ((mav_bridge_heartbeat_msg_t*)TlmMsgPtr)->mav_counter;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.sysid =
		((mav_bridge_heartbeat_msg_t*)TlmMsgPtr)->sysid;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.compid =
		((mav_bridge_heartbeat_msg_t*)TlmMsgPtr)->compid;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat_exp = 0;
          break;
#endif

        //----------------------------------------------------------------
        case MB_HEARTBEAT_MID:
#ifdef TODO
	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.compid =
		((mav_bridge_heartbeat_msg_t*)TlmMsgPtr)->compid;
#endif

	  g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat_exp = 0;
          break;

        //----------------------------------------------------------------
        case MB_SYS_STAT_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: SYS-STATUS\n");
#endif
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_present =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.onboard_control_sensors_present;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_enabled =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.onboard_control_sensors_enabled;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_health =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.onboard_control_sensors_health;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.load =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.load;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.voltage_battery =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.voltage_battery;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.current_battery =
		((mav_bridge_sys_status_msg_t*)TlmMsgPtr)->mav_status.current_battery;


	  g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status_exp = 0;
	  break;

        //----------------------------------------------------------------
        case MB_SYS_TIME_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: SYSTEM-TIME\n");
#endif
	  g_R2U2_AppData.InData.r2u2_input_data.mav_system_time.time_unix_usec =
		((mav_bridge_system_time_msg_t*)TlmMsgPtr)->mav_system_time.time_unix_usec;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_system_time.time_boot_ms =
		((mav_bridge_system_time_msg_t*)TlmMsgPtr)->mav_system_time.time_boot_ms;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_system_time_exp = 0;
	  break;

        //----------------------------------------------------------------
        case MB_GLOB_POSI_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: global-pos-int package received\n");
#endif

	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.lat =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.lat;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.lon =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.lon;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.alt =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.alt;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.relative_alt =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.relative_alt;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vx =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.vx;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vy =
		((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.vy;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vz =
			((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.vz;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.hdg =
			((mav_bridge_global_pos_int_msg_t*)TlmMsgPtr)->mav_global_pos_int.hdg;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int_exp = 0;

          break;

        //----------------------------------------------------------------
        case MB_MIS_CUR_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: MISSION-CURRENT\n");
#endif
	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_current.seq =
                  ((mav_bridge_mission_current_msg_t*)TlmMsgPtr)->mav_mission_curr.seq;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_current_exp = 0;
	  break;

        //----------------------------------------------------------------
        case MB_MIS_REACH_MID:
          OS_printf("JSC: R2U2: MISSION-ITEM_REACHED\n");
	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_item_reached.seq =
                  ((mav_bridge_mission_item_reached_msg_t*)TlmMsgPtr)->mav_mission_reached.seq;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_mission_item_reached_exp = 0;
	  break;

        //----------------------------------------------------------------
        case MB_NAV_CNTR_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: NAV_CONTROL package received\n");
#endif

	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_roll =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.nav_roll;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_pitch =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.nav_pitch;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.alt_error =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.alt_error;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.aspd_error =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.aspd_error;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.xtrack_error =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.xtrack_error;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_bearing =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.nav_bearing;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.target_bearing =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.target_bearing;
	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.wp_dist =
                  ((mav_bridge_nav_cntr_out_msg_t*)TlmMsgPtr)->mav_cntr_out.wp_dist;

	  g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output_exp = 0;

          break;

        //----------------------------------------------------------------
        case PLEXIL_R2U2_TLM_MID:
#ifdef R2U2_DEBUG
          OS_printf("JSC: R2U2: PLEXIL_R2U2\n");
#endif

	  N = g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf.N;
	  if (N == R2U2_N_PLEXIL_MSG){
			//
			// buffer is full
			// 
          	CFE_EVS_SendEvent(R2U2_MSGID_ERR_EID, CFE_EVS_ERROR,
                   "R2U2 - Plexil-r2u2 buffer overflow");
		break;
		}
#ifdef R2U2_DEBUG
	  OS_printf("R2U2: PLEXIL->R2U2: >>%s<<\n",((plexil_tlm_msg_t *)TlmMsgPtr)->plexil_msg);
#endif
	  strncpy(g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf.plexil_msg[N],((plexil_tlm_msg_t *)TlmMsgPtr)->plexil_msg, R2U2_PLEXIL_MSG_LENGTH);
	  g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf.N++;

	  g_R2U2_AppData.InData.r2u2_input_data.plexil_r2u2_msgbuf_exp = 0;
	  break;

        //-----------EXAMPLE----------------------------------------------
        // case PLEXIL_AIRPORT_MID:
	//   g_R2U2_AppData.InData.r2u2_input_data.plexil_ap.current_callsign =
        //    ((plexil_ap_current_t*)TlmMsgPtr)->current_callsign;
	//
	//  g_R2U2_AppData.InData.r2u2_input_data.plexil_ap_exp = 0;
	//
	//  break;

        //----------------------------------------------------------------
        //----------------------------------------------------------------
        default:
          CFE_EVS_SendEvent(R2U2_MSGID_ERR_EID, CFE_EVS_ERROR,
                   "R2U2 - Recvd invalid TLM msgId (0x%08X)", TlmMsgId);
          break;
      }
    }
    else
    {
      bGotNewMsg = FALSE;
    }
  }
}
  
/*=====================================================================================
** Name: R2U2_ProcessNewCmds
**
** Purpose: To process incoming command messages for R2U2 application
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  CFE_SB_RcvMsg
**  CFE_SB_GetMsgId
**  CFE_EVS_SendEvent
**  R2U2_ProcessNewAppCmds
**
** Called By:
**  R2U2_RcvMsg
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  None
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_ProcessNewCmds()
{
  CFE_SB_Msg_t*  CmdMsgPtr=NULL;
  CFE_SB_MsgId_t CmdMsgId;
  boolean     bGotNewMsg=TRUE;

  while (bGotNewMsg)
  {
    if (CFE_SB_RcvMsg(&CmdMsgPtr, g_R2U2_AppData.CmdPipeId, CFE_SB_POLL) == CFE_SUCCESS)
    {
      CmdMsgId = CFE_SB_GetMsgId(CmdMsgPtr);
      switch (CmdMsgId)
      {
        case R2U2_CMD_MID:
          R2U2_ProcessNewAppCmds(CmdMsgPtr);
          break;

        case R2U2_SEND_HK_MID:
          R2U2_ReportHousekeeping();
          break;

        /* TODO: Add code to process other subscribed commands here
        **
        ** Example:
        **   case CFE_TIME_DATA_CMD_MID:
        **     R2U2_ProcessTimeDataCmd(CmdMsgPtr);
        **     break;
        */

        default:
          CFE_EVS_SendEvent(R2U2_MSGID_ERR_EID, CFE_EVS_ERROR,
                   "R2U2 - Recvd invalid CMD msgId (0x%08X)", CmdMsgId);
          break;
      }
    }
    else
    {
      bGotNewMsg = FALSE;
    }
  }
}
  
/*=====================================================================================
** Name: R2U2_ProcessNewAppCmds
**
** Purpose: To process command messages targeting R2U2 application
**
** Arguments:
**  CFE_SB_Msg_t* MsgPtr - new command message pointer
**
** Returns:
**  None
**
** Routines Called:
**  CFE_SB_GetCmdCode
**  CFE_EVS_SendEvent
**
** Called By:
**  R2U2_ProcessNewCmds
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  g_R2U2_AppData.HkTlm.usCmdCnt
**  g_R2U2_AppData.HkTlm.usCmdErrCnt
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_ProcessNewAppCmds(CFE_SB_Msg_t* MsgPtr)
{
  uint32 uiCmdCode=0;

  if (MsgPtr != NULL)
  {
    uiCmdCode = CFE_SB_GetCmdCode(MsgPtr);
    switch (uiCmdCode)
    {
      case R2U2_NOOP_CC:
        g_R2U2_AppData.HkTlm.usCmdCnt++;
        CFE_EVS_SendEvent(R2U2_CMD_INF_EID, CFE_EVS_INFORMATION,
                 "R2U2 - Recvd NOOP cmd (%d)", uiCmdCode);
        break;

      case R2U2_RESET_CC:
        g_R2U2_AppData.HkTlm.usCmdCnt = 0;
        g_R2U2_AppData.HkTlm.usCmdErrCnt = 0;
        CFE_EVS_SendEvent(R2U2_CMD_INF_EID, CFE_EVS_INFORMATION,
                 "R2U2 - Recvd RESET cmd (%d)", uiCmdCode);

		//
		// JSC: TODO:
		// TL_reset ?
		//
        break;

      default:
        g_R2U2_AppData.HkTlm.usCmdErrCnt++;
        CFE_EVS_SendEvent(R2U2_MSGID_ERR_EID, CFE_EVS_ERROR,
                 "R2U2 - Recvd invalid cmdId (%d)", uiCmdCode);
        break;
    }
  }
}
  
/*=====================================================================================
** Name: R2U2_ReportHousekeeping
**
** Purpose: To send housekeeping message
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  TBD
**
** Called By:
**  R2U2_ProcessNewCmds
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): GSFC, me
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_ReportHousekeeping()
{
  /* TODO: Add code to update housekeeping data, if needed, here. */

  CFE_SB_TimeStampMsg((CFE_SB_Msg_t*)&g_R2U2_AppData.HkTlm);
  CFE_SB_SendMsg((CFE_SB_Msg_t*)&g_R2U2_AppData.HkTlm);
}
  
/*=====================================================================================
** Name: R2U2_SendOutData
**
** Purpose: To publish 1-Wakeup cycle output data
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  TBD
**
** Called By:
**  R2U2_RcvMsg
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_SendOutData()
{
	//
	// JSC: assemble results package 
	// in g_R2U2_AppData.OutData.*

#ifdef R2U2_DEBUG
  OS_printf("JSC: R2U2: assemble output package\n");
#endif
  memcpy(g_R2U2_AppData.OutData.atomics_vector, atomics_vector,sizeof(atomics_vector));
  memcpy(g_R2U2_AppData.OutData.results_pt, results_pt,sizeof(results_pt));
#ifdef R2U2_DEBUG
  OS_printf("JSC: R2U2: assembled output package\n");
#endif

  CFE_SB_TimeStampMsg((CFE_SB_Msg_t*)&g_R2U2_AppData.OutData);
  CFE_SB_SendMsg((CFE_SB_Msg_t*)&g_R2U2_AppData.OutData);

}
  
/*=====================================================================================
** Name: R2U2_VerifyCmdLength
**
** Purpose: To verify command length for a particular command message
**
** Arguments:
**  CFE_SB_Msg_t* MsgPtr   - command message pointer
**  uint16     usExpLength - expected command length
**
** Returns:
**  boolean bResult - result of verification
**
** Routines Called:
**  CFE_EVS_SendEvent
**  CFE_SB_GetTotalMsgLength
**  CFE_SB_GetMsgId
**  CFE_SB_GetCmdCode
**
** Called By:
**  R2U2_ProcessNewCmds
**
** Global Inputs/Reads:
**  None
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
boolean R2U2_VerifyCmdLength(CFE_SB_Msg_t* MsgPtr,
              uint16 usExpectedLen)
{
  boolean bResult=FALSE;
  uint16 usMsgLen=0;

  if (MsgPtr != NULL)
  {
    usMsgLen = CFE_SB_GetTotalMsgLength(MsgPtr);

    if (usExpectedLen == usMsgLen)
    {
      bResult = TRUE;
    }
    else
    {
      CFE_SB_MsgId_t MsgId = CFE_SB_GetMsgId(MsgPtr);
      uint16 usCmdCode = CFE_SB_GetCmdCode(MsgPtr);

      CFE_EVS_SendEvent(R2U2_MSGLEN_ERR_EID, CFE_EVS_ERROR,
               "R2U2 - Rcvd invalid msgLen: msgId=0x%08X, cmdCode=%d, "
               "msgLen=%d, expectedLen=%d",
               MsgId, usCmdCode, usMsgLen, usExpectedLen);
               
      g_R2U2_AppData.HkTlm.usCmdErrCnt++;
    }
  }

  return (bResult);
}
  
/*=====================================================================================
** Name: R2U2_AppMain
**
** Purpose: To define R2U2 application's entry point and main process loop
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**  CFE_ES_RegisterApp
**  CFE_ES_PerfLogEntry
**  CFE_ES_PerfLogExit
**  CFE_ES_RunLoop
**  CFE_ES_ExitApp
**  R2U2_AppInit
**  R2U2_RcvMsg
**
** Called By:
**  TBD
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
void R2U2_AppMain()
{
  int32 iStatus=CFE_SUCCESS;
  
  /* Register the Application with Executive Services */
  iStatus = CFE_ES_RegisterApp();
  if (iStatus != CFE_SUCCESS)
  {
    CFE_ES_WriteToSysLog("R2U2 - Failed to register the app (0x%08X)\n", iStatus);
    goto R2U2_AppMain_Exit_Tag;
  }

  /* Performance Log Entry stamp - #1 */
  CFE_ES_PerfLogEntry(R2U2_MAIN_TASK_PERF_ID);
  
  /* Perform Application initializations */
  if (R2U2_AppInit() != CFE_SUCCESS)
  {
    g_R2U2_AppData.uiRunStatus = CFE_ES_APP_ERROR;
  }

  /* Application Main Loop. Call CFE_ES_RunLoop() to check for changes in the
  ** Application's status. If there is a request to kill this Application, it will
  ** be passed in through the RunLoop call.
  */
  while (CFE_ES_RunLoop(&g_R2U2_AppData.uiRunStatus) == TRUE)
  {
    /* Performance Log Exit stamp - #1 */
    CFE_ES_PerfLogExit(R2U2_MAIN_TASK_PERF_ID);
    
    iStatus = R2U2_RcvMsg(CFE_SB_PEND_FOREVER); 
    
    /* Performance Log Entry stamp - #2 */
    CFE_ES_PerfLogEntry(R2U2_MAIN_TASK_PERF_ID); 
  }

  /* Performance Log Exit stamp - #2 */
  CFE_ES_PerfLogExit(R2U2_MAIN_TASK_PERF_ID);
  
R2U2_AppMain_Exit_Tag:
  /* Exit the application */
  CFE_ES_ExitApp(g_R2U2_AppData.uiRunStatus);
} 




/*=====================================================================================
** Name: OS_print_signals
**
** Purpose: Debugging: print all signals on STDOUT in CSV format
**
** Arguments:
**  None
**
** Returns:
**  None
**
** Routines Called:
**
** Called By:
**  TBD
**
** Global Inputs/Reads:
**  TBD
**
** Global Outputs/Writes:
**  TBD
**
** Limitations, Assumptions, External Events, and Notes:
**  1. List assumptions that are made that apply to this function.
**  2. List the external source(s) and event(s) that can cause this function to execute.
**  3. List known limitations that apply to this function.
**  4. If there are no assumptions, external events, or notes then enter NONE.
**    Do not omit the section.
**
** Algorithm:
**  Psuedo-code or description of basic algorithm
**
** Author(s): me 
**
** History: Date Written 2014-12-23
**      Unit Tested  yyyy-mm-dd
**=====================================================================================*/
#ifdef R2U2_VERBOSE
static void OS_print_signals(){

OS_printf("R2U2-signals: ");
//OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.mav_counter);
// OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.sysid);
// OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat.compid);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_heartbeat_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_present);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_enabled);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.onboard_control_sensors_health);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.load);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.voltage_battery);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status.current_battery);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_sys_status_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_system_time.time_unix_usec);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_system_time.time_boot_ms);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_system_time_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.lat);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.lon);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.alt);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.relative_alt);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vx);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vy);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.vz);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int.hdg);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_global_position_int_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_mission_current.seq);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_mission_current_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_mission_item_reached.seq);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_mission_item_reached_exp);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_roll);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_pitch);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.alt_error);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.aspd_error);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.xtrack_error);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.nav_bearing);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.target_bearing);
OS_printf("%f,", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output.wp_dist);
OS_printf("%f", (double)g_R2U2_AppData.InData.r2u2_input_data.mav_nav_controller_output_exp);

OS_printf("\n");

}
#endif

  
/*=======================================================================================
** End of file r2u2_app.c
**=====================================================================================*/
  
