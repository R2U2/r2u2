#include "TL_observers.h"

void decode_inst(char* bool_vec, instruction_t* inst);
void decode_interval(char* bool_vec, interval_t* interval);
int parse_inst(char* filename);
void parse_interval(char* filename);
