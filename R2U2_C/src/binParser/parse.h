#ifndef PARSE_H
#define PARSE_H

#include <stdint.h>
#include "TL_observers.h"

typedef enum {
	P_FTI = 0b000,
	P_FTM = 0b001,
  P_SCQ = 0b010,
	P_PTM = 0b011,
	P_PTI = 0b100,
	P_AT  = 0b101
} parser_t;

void parse_inst_ft_file(const char*);
void parse_inst_ft_bin(const char*);
void parse_inst_pt_file(const char*);
void parse_inst_pt_bin(const char*);

void parse_interval_ft_file(const char*);
void parse_interval_ft_bin(const char*);
void parse_interval_pt_file(const char*);
void parse_interval_pt_bin(const char*);

void parse_scq_size_file(const char*);
void parse_scq_size_bin(const char*);

void parse_at_file(const char*);
void parse_at_bin(const char*);

#endif
