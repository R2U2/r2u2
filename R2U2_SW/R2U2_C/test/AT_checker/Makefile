OBJS =  compare.o circbuffer.o filter_abs_diff_angle.o filter_movavg.o filter_rate.o at_conversion_test.o #filter_regex.o filter_fft.o filter_filt.o filter_prognostics.o
SRC_DIR = ../../src/AT
BIN = main 

all: $(BIN)

CC = cc
CFLAGS = -Wall

compare.o: compare.c compare.h
	$(CC) $(CFLAGS)	-c compare.c

circbuffer.o: $(SRC_DIR)/circbuffer.c $(SRC_DIR)/circbuffer.h
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/circbuffer.c

filter_abs_diff_angle.o: $(SRC_DIR)/filter_abs_diff_angle.c $(SRC_DIR)/filter_abs_diff_angle.h
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_abs_diff_angle.c

filter_movavg.o: $(SRC_DIR)/filter_movavg.c $(SRC_DIR)/filter_movavg.h
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_movavg.c

filter_rate.o: $(SRC_DIR)/filter_rate.c $(SRC_DIR)/filter_rate.h
	$(CC) $(CFLAGS)	-c $(SRC_DIR)/filter_rate.c

at_conversion_test.o: at_conversion_test.c 
	cc $(CFLAGS) -c at_conversion_test.c

main: $(OBJS)
	cc $(CFLAGS) -o $(BIN) $(OBJS) 

.PHONY: all debug clean
clean:
	rm -rf $(BIN) $(OBJS)
