/*=======================================================================================
** File Name: filter_regex.c
**
** Title: Rate filter for R2U2/AT
**
** $Author:  J. Schumann
** $Revision: $
** $Date:   2014
**
** Purpose:  Regexp filter for strings
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
#include <stdlib.h>
#include <regex.h>
#include "filter_regex.h"
#include <math.h>

//-----------------------------------------------------------------
//	initialize
//-----------------------------------------------------------------
void filter_regex_init(regex_t *RE, char *RS){

int reti;

reti = regcomp(RE, RS, 0);

if (reti){
//	OS_printf("could not compile RE: %s\n", RS);
	}

}

//-----------------------------------------------------------------
//	free memory: NA
//-----------------------------------------------------------------
void filter_regex_free(regex_t *RE){

regfree(RE);

}


//-----------------------------------------------------------------
//	update regex filter and return current regex
//-----------------------------------------------------------------
int filter_regex_update_data(regex_t *RE, const char *s, char **matches ){

int reti;

reti = regexec(RE, s, 0, NULL, 0);

// pull out matches

return reti;
}
