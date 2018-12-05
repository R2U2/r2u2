/*=======================================================================================
** File Name: circbuffer.c
**
** Title: Circular buffer for R2U2/AT
**
** $Author:  P. Moosbrugger
** $Revision: $
** $Date:   2015
**
** Purpose: circukar buffer for moving average filter
**
** Functions Defined:
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/

#include <stdio.h>
#include "circbuffer.h"

//-----------------------------------------------------------------
int circBufPush(circBuf_t *c, int16_t data)
{
    int next = c->head + 1;
    if (next >= c->maxLen)
        next = 0;
 
    // Cicular buffer is full
    if (next == c->tail)
        return -1;  // quit with an error
 
    c->buffer[c->head] = data;
    c->head = next;
    return 0;
}
 
//-----------------------------------------------------------------
int circBufPop(circBuf_t *c, int16_t *data)
{
    // if the head isn't ahead of the tail, we don't have any characters
    if (c->head == c->tail) {
		*data = 0;	// write 0 back
        return -1;  // quit with an error
	}
 
    *data = c->buffer[c->tail];
    c->buffer[c->tail] = 0;  // clear the data (optional)
 
    int next = c->tail + 1;
    if(next >= c->maxLen)
        next = 0;
 
    c->tail = next;
 
    return 0;
}
