# tool macros
CC := gcc

# path macros
BIN_PATH := bin
OBJ_PATH := target/release
SRC_PATH := src
DBG_PATH := target/debug

# Feature Flags
ifdef R2U2_AT_Extra_Filters
# Add Extra Filters
CFLAGS := $(CFLAGS) -DR2U2_AT_Extra_Filters
SRC_DIRS := $(SRC_DIRS) $(SRC_PATH)/AT/extra_filters
$(info    R2U2 Extra Filters Enabled)
endif

ifdef R2U2_TL_Formula_Names
CFLAGS := $(CFLAGS) -DR2U2_TL_Formula_Names
$(info    R2U2 Formula Naming Enabled)
endif

ifdef R2U2_TL_Contract_Status
CFLAGS := $(CFLAGS) -DR2U2_TL_Contract_Status
$(info    R2U2 AG Contract Status Enabled)
endif

ifdef R2U2_CSV_Header_Mapping
CFLAGS := $(CFLAGS) -DR2U2_CSV_Header_Mapping
$(info    R2U2 CSV Header Mapping Enabled)
endif

ifdef R2U2_AT_Signal_Sets
# Add Signal Sets Filters
CFLAGS := $(CFLAGS) -DR2U2_AT_Signal_Sets #-D_GNU_SOURCE
SRC_DIRS := $(SRC_DIRS) $(SRC_PATH)/AT/signal_set_filters
$(info    R2U2 Signal Sets Enabled)
endif

# ifdef R2U2_AT_Prognostics
# # Add prognostics module
# CFLAGS := $(CFLAGS) -DR2U2_AT_Prognostics
# SRC_DIRS := $(SRC_DIRS) $(SRC_PATH)/AT/prognostic_filter
# $(info    R2U2 Prognostics Enabled)
# endif

ifdef R2U2_AT_FFT_Filter
# Enable the discrete Fourier transform filter
CFLAGS := $(CFLAGS) -DR2U2_AT_FFT_Filter
SRC_DIRS := $(SRC_DIRS) $(SRC_PATH)/AT/fft_filter
LIBS := $(LIBS) fftw3
$(info    R2U2 FFT Filter Enabled)
endif

SRC_DIRS := $(SRC_PATH) $(SRC_PATH)/TL $(SRC_PATH)/parse $(SRC_PATH)/bz $(SRC_DIRS)
IDIR=$(SRC_DIRS)
OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))
OBJ_DBG_DIRS := $(DBG_PATH) $(addprefix $(DBG_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))

# Search paths and libs
ifdef LIBS
# Distribution agnostic library locations via pkg-config
IN_LIBS=$(shell pkg-config --cflags $(LIBS))
LD_LIBS=$(shell pkg-config --libs $(LIBS))
endif
LD_LIBS := $(LD_LIBS) -lm

CFLAGS :=-std=c99 -D_POSIX_C_SOURCE=200112L $(CFLAGS) $(IDIR:%=-I%) $(IN_LIBS)
DBGFLAG := -g -O0 \
-fdata-sections -ffunction-sections -fno-common \
-fsanitize=undefined -fsanitize=address\
-pedantic -Waggregate-return -Wall -Wbad-function-cast -Wcast-align -Wcast-qual -Wconversion -Wctor-dtor-privacy -Wdisabled-optimization -Wdouble-promotion -Wduplicated-branches -Wduplicated-cond -Wextra -Wfloat-equal -Wformat-nonliteral -Wformat-security -Wformat-truncation -Wformat-y2k -Wformat=2 -Wimplicit -Wimport -Winit-self -Winline -Winvalid-pch -Wlogical-op -Wlong-long -Wmisleading-indentation -Wmissing-declarations -Wmissing-field-initializers -Wmissing-format-attribute -Wmissing-include-dirs -Wmissing-noreturn -Wmissing-prototypes -Wnested-externs -Wnoexcept -Wnon-virtual-dtor -Wnull-dereference -Wodr -Wold-style-cast -Woverloaded-virtual -Wpacked -Wpedantic -Wpointer-arith -Wredundant-decls -Wshadow -Wsign-conversion -Wsign-promo -Wstack-protector -Wstrict-aliasing=2 -Wstrict-null-sentinel -Wstrict-overflow=5 -Wstrict-prototypes -Wswitch-default -Wundef -Wundef -Wunreachable-code -Wunused -Wunused-parameter -Wuseless-cast -Wvariadic-macros -Wwrite-strings -Wzero-as-null-pointer-constant -Wall -Wextra -pedantic -Wshadow -Wpointer-arith -Wcast-qual -Wstrict-prototypes -Wmissing-prototypes \
-Wno-switch-enum -Wno-unknown-warning-option -Wno-gnu-binary-literal \
--coverage\
-DR2U2_DEBUG
CCOBJFLAG := $(CFLAGS) -c
LDFLAGS := $(LD_LIBS)

# compile macros
TARGET_NAME := r2u2
TARGET_RELES := $(BIN_PATH)/$(TARGET_NAME)
TARGET_DEBUG := $(BIN_PATH)/$(TARGET_NAME)_debug
ifeq ($(OS),Windows_NT)
	TARGET_RELES := $(addsuffix .exe,$(TARGET_RELES))
	TARGET_DEBUG := $(addsuffix .exe,$(TARGET_DEBUG))
endif
MAIN_SRC := src/$(TARGET_NAME).c

# src files & obj files
SRC := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*)))
OBJ_RELES := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(SRC)))))
OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(SRC)))))

# Testing
TST_SRC_PATH := test
TST_LIB_PATH := $(TST_SRC_PATH)/munit
TST_OBJ_PATH := target/$(TST_SRC_PATH)
TST_BIN_PATH := $(BIN_PATH)/$(TST_SRC_PATH)
TST_RPT_PATH := report

TSTFLAGS :=  $(CFLAGS) $(DBGFLAG) -I$(TST_LIB_PATH)
TSTOBJFLAGS := $(TSTFLAGS) -c
TSTLNKFLAGS := $(LDFLAGS) --coverage

TST := $(wildcard $(TST_SRC_PATH)/test_*.c)
OBJ_TEST := $(addprefix $(TST_OBJ_PATH)/, $(addsuffix .o, $(basename $(subst $(TST_SRC_PATH)/,,$(TST)))))
OBJ_NO_MAIN :=  $(filter-out $(DBG_PATH)/R2U2.o,$(OBJ_DEBUG)) # TODO: This is the worst hack in here, please remove
TARGET_TEST := $(addprefix $(TST_BIN_PATH)/,$(basename $(subst $(TST_SRC_PATH)/,,$(TST))))

# clean files list
DISTCLEAN_LIST := $(OBJ_PATH) \
				  $(DBG_PATH) \
				  $(TST_OBJ_PATH)
CLEAN_LIST := $(TARGET_RELES) \
			  $(TARGET_DEBUG) \
			  $(TARGET_TEST) \
			  $(TST_RPT_PATH) \
			  $(DISTCLEAN_LIST) \
				src/binParser/config.c

# default rule
default: all

# non-phony targets
$(TARGET_RELES): $(OBJ_RELES) | $(BIN_PATH)
	$(CC) $(CFLAGS) -O3 -o $@ $? $(LDFLAGS)

$(OBJ_PATH)/%.o: src/%.c* | $(OBJ_PATH)
	$(CC) $(CCOBJFLAG) -o $@ $<

$(TARGET_DEBUG): $(OBJ_DEBUG) | $(DBG_PATH)
	$(CC) $(CFLAGS) $(DBGFLAG) -o $@ $? $(LDFLAGS)

$(DBG_PATH)/%.o: src/%.c* | $(DBG_PATH)
	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

$(TST_BIN_PATH)/%: $(TST_OBJ_PATH)/%.o $(TST_OBJ_PATH)/test_lib.o $(OBJ_NO_MAIN) | $(TST_BIN_PATH)
	$(CC) $(TSTFLAGS)  -o $@ $? $(TSTLNKFLAGS)

$(TST_OBJ_PATH)/%.o: $(TST_SRC_PATH)/%.c* | $(TST_OBJ_PATH)
	$(CC) $(TSTOBJFLAGS) -o $@ $<

$(TST_OBJ_PATH)/test_lib.o: | $(TST_OBJ_PATH)
	$(CC) $(TSTOBJFLAGS) -o $@ $(TST_LIB_PATH)/munit.c

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_DIRS)

$(DBG_PATH):
	mkdir -p $(OBJ_DBG_DIRS)

$(TST_BIN_PATH):
	mkdir -p $(TST_BIN_PATH)

$(TST_OBJ_PATH):
	mkdir -p $(TST_OBJ_PATH)

$(TST_RPT_PATH):
	mkdir -p $(TST_RPT_PATH)

# Shell functions
run_all_tests = (find ./bin/test -maxdepth 1 -type f -name 'test_*' -exec {} \;)
coverage_proc = (find $(DBG_PATH) -name "*.gcno" -exec gcov -b -l -p -c {} \; && mv *.gcov $(TST_RPT_PATH))
coverage_html = (gcovr -g -k -r $(SRC_PATH) -e '.*_pt\.c' $(TST_RPT_PATH) --html --html-details -o $(TST_RPT_PATH)/index.html)

# phony rules
.PHONY: all
all: $(TARGET_RELES)

.PHONY: debug
debug: $(TARGET_DEBUG)

.PHONY: test
test: $(TARGET_TEST)

.PHONY: coverage
coverage: $(TARGET_TEST) | $(TST_RPT_PATH)
	$(call coverage_proc)
	$(call coverage_html)

.PHONY: check
check: $(TARGET_TEST) | $(TST_RPT_PATH)
	$(call run_all_tests)
	$(call coverage_proc)
	$(call coverage_html)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo CLEAN $(DISTCLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)

# Variable debug printer
# Call as `make print-VARIABLE`
# From: https://www.cmcrossroads.com/article/printing-value-makefile-variable
print-%  : ; @echo $* = $($*)

# List all concrete targets
# From: https://stackoverflow.com/a/26339924
.PHONY: list
list:
	@LC_ALL=C $(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$'

#doxygen documentation setup
doc: ./Doxyfile
	doxygen ./Doxyfile

