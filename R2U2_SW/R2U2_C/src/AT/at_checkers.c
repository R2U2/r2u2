#include "at_checkers.h"
#include "at_operations.h"
#include "at_globals.h"

#include <stdlib.h>

#include "filters/filter_rate.h"
#include "filters/filter_movavg.h"
#include "parse.h"

void at_checkers_config(char *f)
{
		parse_at(f);
}

void at_checkers_init()
{
	return;
}

void at_checkers_update()
{
	uint8_t i;
	DEBUG_PRINT("\n	AT Update\n");
	for(i = 0; i < num_instr; i++) {
		decode[at_instructions[i].filter](at_instructions[i]);
	}
}

void at_checkers_free()
{
	return;
}
