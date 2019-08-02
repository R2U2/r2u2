// #include "r2u2_input_types.h"
#include "R2U2Config.h"

void count_signals(const char* data_file, int* NUM_SIG, int* MAX_TIME);
void load_signals(const char* data_file, int NUM_SIG, int MAX_TIME, r2u2_in_type** in_dat);
void decodeCSV(const char* csv_file, r2u2_in_type*** in_dat, r2u2_in_type** cur_sigs, int* MAX_TIME, int* NUM_SIG);