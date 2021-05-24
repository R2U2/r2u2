OBJS = at_globals.o at_compare.o at_operations.o at_checkers.o circbuffer.o filter_abs_diff_angle.o filter_movavg.o filter_rate.o at_conversion_test.o #filter_regex.o filter_fft.o filter_filt.o filter_prognostics.o
SRC_DIR = ../../src/AT
BIN = main 

all: $(BIN)

CC = cc
CFLAGS = -Wall

at_compare.o: at_compare.c 
	$(CC) $(CFLAGS)	-c at_compare.c

at_operations.o: at_operations.c
	$(CC) $(CFLAGS)	-c at_operations.c

at_globals.o: at_globals.c
	$(CC) $(CFLAGS)	-c at_globals.c

at_checkers.o: at_checkers.c
	$(CC) $(CFLAGS)	-c at_checkers.c

circbuffer.o: $(SRC_DIR)/circbuffer.c
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/circbuffer.c

filter_abs_diff_angle.o: $(SRC_DIR)/filter_abs_diff_angle.c
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_abs_diff_angle.c

filter_movavg.o: $(SRC_DIR)/filter_movavg.c 
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_movavg.c

filter_rate.o: $(SRC_DIR)/filter_rate.c 
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_rate.c

at_conversion_test.o: at_conversion_test.c
	$(CC) $(CFLAGS) -c at_conversion_test.c

main: $(OBJS)
	$(CC) $(CFLAGS) -o $(BIN) $(OBJS) 

.PHONY: all debug clean
clean:
	rm -rf $(BIN) $(OBJS)
