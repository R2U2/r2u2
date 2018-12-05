FORMULAS = t1
FORMULAS-DIR = ../../src/MATLAB
OBJS=main.o TL_queue_pt.o TL_queue_ft.o TL_globals.o TL_init.o TL_formula_pt.o TL_formula_ft.o TL_formula_int_pt.o TL_formula_int_ft.o 
SRC-DIR = ../../src/TL
BIN = main



all: main

debug: CFLAGS += -g -O0 -Wall -Wextra
debug: $(BIN)

TL_formula_pt.o : ${FORMULAS-DIR}/${FORMULAS}_pt.c ${SRC-DIR}/TL_observers.h
	cp -f ${FORMULAS-DIR}/${FORMULAS}_pt.c ${SRC-DIR}/TL_formula_pt.c;
	cc $(CFLAGS) -c ${SRC-DIR}/TL_formula_pt.c

TL_formula_int_pt.o : ${FORMULAS-DIR}/${FORMULAS}_pti.c ${SRC-DIR}/TL_observers.h
	cp -f ${FORMULAS-DIR}/${FORMULAS}_pti.c ${SRC-DIR}/TL_formula_int_pt.c;
	cc $(CFLAGS) -c ${SRC-DIR}/TL_formula_int_pt.c

TL_formula_ft.o : ${FORMULAS-DIR}/${FORMULAS}_ft.c ${SRC-DIR}/TL_observers.h
	cp -f ${FORMULAS-DIR}/${FORMULAS}_ft.c ${SRC-DIR}/TL_formula_ft.c;
	cc $(CFLAGS) -c ${SRC-DIR}/TL_formula_ft.c

TL_formula_int_ft.o : ${FORMULAS-DIR}/${FORMULAS}_fti.c ${SRC-DIR}/TL_observers.h
	cp -f ${FORMULAS-DIR}/${FORMULAS}_fti.c ${SRC-DIR}/TL_formula_int_ft.c;
	cc $(CFLAGS) -c ${SRC-DIR}/TL_formula_int_ft.c

TL_init.o : ${SRC-DIR}/TL_init.c ${SRC-DIR}/TL_observers.h
	cc $(CFLAGS) -c ${SRC-DIR}/TL_init.c
	
TL_queue_pt.o: ${SRC-DIR}/TL_queue_pt.c ${SRC-DIR}/TL_observers.h ${SRC-DIR}/TL_queue_pt.h
	cc $(CFLAGS) -c ${SRC-DIR}/TL_queue_pt.c 

TL_queue_ft.o: ${SRC-DIR}/TL_queue_ft.c ${SRC-DIR}/TL_observers.h ${SRC-DIR}/TL_queue_ft.h
	cc $(CFLAGS) -c ${SRC-DIR}/TL_queue_ft.c

TL_globals.o: ${SRC-DIR}/TL_globals.c ${SRC-DIR}/TL_observers.h ${SRC-DIR}/TL_queue_pt.h
	cc $(CFLAGS) -c ${SRC-DIR}/TL_globals.c

main.o: main.c ${SRC-DIR}/TL_globals.h
	cc $(CFLAGS) -c main.c -g -O0 -Wall -Wextra

main: $(OBJS)
	cc $(CFLAGS) -o $(BIN) $(OBJS) 

${SRC-DIR}/TL_globals.h:

.PHONY: all debug clean
clean:
	rm -rf $(BIN) $(OBJS)
