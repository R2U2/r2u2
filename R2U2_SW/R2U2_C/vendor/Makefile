# OBJ_PATH := ../target/release
# DBG_PATH := ../target/debug

# VDR_DIRS := CsvParser
# SRC_DIRS := $(VDR_DIRS)
# OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))


# # non-phony targets
# .PHONY: all
# all: $(OBJ) | $(BIN_PATH)
# 	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $?

# $(OBJ_PATH)/%.o: src/%.c* | $(OBJ_PATH) | $(VDR_PATH)
# 	cd $(VDR_PATH) && $(MAKE) all
# 	$(CC) $(CCOBJFLAG) -o $@ $<

# .PHONY: debug
# debug: $(OBJ_DEBUG) | $(DBG_PATH)
# 	$(CC) $(CFLAGS) $(LDFLAGS) $(DBGFLAG) -o $@ $?

# $(DBG_PATH)/%.o: %.c* | $(DBG_PATH) | $(VDR_PATH)
# 	cd $(VDR_PATH) && $(MAKE) debug
# 	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

all:
	mkdir -p ../target/release/CsvParser/
	gcc -c -I CsvParser/include/ CsvParser/src/csvparser.c -o ../target/release/CsvParser/csvparser.o
	mkdir -p lib
	ar rs lib/libcsv.a ../target/release/CsvParser/csvparser.o
	mkdir -p include
	cp CsvParser/include/csvparser.h include/csvparser.h

# clean files list
DISTCLEAN_LIST := ../target/release/CsvParser \
				  ../target/debug/CsvParser
CLEAN_LIST := lib/libcsv.a \
			  include/csvparser.h \
			  $(DISTCLEAN_LIST)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)