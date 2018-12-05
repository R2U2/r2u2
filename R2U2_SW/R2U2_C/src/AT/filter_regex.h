/*=======================================================================================
** File Name: filter_rate.h
**
** Title: header for rate filter
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
#include <regex.h>

#ifndef R2U2_STANDALONE
#define R2U2_AOS
#endif


#ifdef R2U2_AOS
#include "r2u2_private_types.h"
#endif 
void filter_regex_init(regex_t *RE, char *RS);
void filter_regex_free(regex_t *RE);
int filter_regex_update_data(regex_t *RE, const char *s, char **matches);

#ifdef R2U2_AOS
int filter_regex_plexil_update_data(regex_t *RE, plexil_r2u2_msgbuf_t mb , char **matches);
#endif
