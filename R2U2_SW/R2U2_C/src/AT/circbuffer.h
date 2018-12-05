/*=======================================================================================
** File Name: circbuffer.h
**
** Title: circular buffer
**
** $Author:  P. Moosbrugger
** $Revision: $
** $Date:   2015
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

#ifndef _CIRCBUFFER_H_
#define _CIRCBUFFER_H_

#include <stdint.h>

#define CIRCBUF_DEF(x,y) int16_t x##_space[y+1]; circBuf_t x = { x##_space, 0, 0, y+1};

typedef struct
{
	int16_t * const buffer;
	int head;
	int tail;
	const int maxLen;
} circBuf_t;

int circBufPush(circBuf_t *c, int16_t data);
int circBufPop(circBuf_t *c, int16_t *data);

#endif
