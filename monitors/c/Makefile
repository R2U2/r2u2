# Makefile
#
#
#
# Layout:
#     - Section ...

# tool macros
CC := gcc
AR := ar

# path macros
SRC_PATH := src
BIN_PATH := build
OBJ_PATH := build/release
DBG_PATH := build/debug
EXT_PATH := external
TST_PATH := test
RPT_PATH := report
DOC_PATH := doc

SRC_DIRS := $(SRC_PATH) $(SRC_PATH)/engines $(SRC_PATH)/engines/booleanizer $(SRC_PATH)/engines/mltl $(SRC_PATH)/memory
INC_DIRS := $(SRC_DIRS)
OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))
DBG_DIRS := $(DBG_PATH) $(addprefix $(DBG_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))

# Search paths and libs
ifdef DIST_LIBS
# Distribution agnostic library locations via pkg-config
INC_LIBS=$(shell pkg-config --cflags $(DIST_LIBS))
LNK_LIBS=$(shell pkg-config --libs $(DIST_LIBS))
endif

# Link std math library
LNK_LIBS := $(LNK_LIBS) -lm

# Compiler Flag Sets
CFLAGS :=-std=c99 -D_POSIX_C_SOURCE=200112L $(CFLAGS) $(INC_DIRS:%=-I%) $(INC_LIBS)
DBGFLAG := -g -O0 \
-fdata-sections -ffunction-sections -fno-common \
-fsanitize=undefined -fsanitize=address\
-pedantic -Waggregate-return -Wall -Wbad-function-cast -Wcast-align -Wcast-qual -Wconversion -Wctor-dtor-privacy -Wdisabled-optimization -Wdouble-promotion -Wduplicated-branches -Wduplicated-cond -Wextra -Wfloat-equal -Wformat-nonliteral -Wformat-security -Wformat-truncation -Wformat-y2k -Wformat=2 -Wimplicit -Wimport -Winit-self -Winline -Winvalid-pch -Wlogical-op -Wlong-long -Wmisleading-indentation -Wmissing-declarations -Wmissing-field-initializers -Wmissing-format-attribute -Wmissing-include-dirs -Wmissing-noreturn -Wmissing-prototypes -Wnested-externs -Wnoexcept -Wnon-virtual-dtor -Wnull-dereference -Wodr -Wold-style-cast -Woverloaded-virtual -Wpacked -Wpedantic -Wpointer-arith -Wredundant-decls -Wshadow -Wsign-conversion -Wsign-promo -Wstack-protector -Wstrict-aliasing=2 -Wstrict-null-sentinel -Wstrict-overflow=5 -Wstrict-prototypes -Wswitch-default -Wundef -Wundef -Wunreachable-code -Wunused -Wunused-parameter -Wuseless-cast -Wvariadic-macros -Wwrite-strings -Wzero-as-null-pointer-constant -Wall -Wextra -pedantic -Wshadow -Wpointer-arith -Wcast-qual -Wstrict-prototypes -Wmissing-prototypes \
-Wno-switch-enum -Wno-unknown-warning-option -Wno-gnu-binary-literal \
--coverage\
-DR2U2_DEBUG
CCOBJFLAG := $(CFLAGS) -c
ARFLAGS := -rcus
LDFLAGS := $(LNK_LIBS)

# Target Lib
LIB_NAME := libr2u2
LIB_MAIN := $(SRC_PATH)/lib.c
LIB_RELS := $(BIN_PATH)/$(LIB_NAME)
LIB_DBUG := $(BIN_PATH)/$(LIB_NAME)_debug

# Target Bin
BIN_NAME := r2u2
BIN_MAIN := $(SRC_PATH)/main.c
BIN_RELS := $(BIN_PATH)/$(BIN_NAME)
BIN_DBUG := $(BIN_PATH)/$(BIN_NAME)_debug
ifeq ($(OS),Windows_NT)
	BIN_RELS := $(addsuffix .exe,$(BIN_RELS))
	BIN_DBUG := $(addsuffix .exe,$(BIN_DBUG))
endif

# Lib files and objects
LIB_SRC_FILES := $(foreach x, $(SRC_DIRS), $(filter-out $(BIN_MAIN), $(wildcard $(addprefix $(x)/*,.c*))))
LIB_OBJ_RELES := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(LIB_SRC_FILES)))))
LIB_OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(LIB_SRC_FILES)))))

# Bin files and objects
BIN_SRC_FILES := $(foreach x, $(SRC_DIRS), $(filter-out $(LIB_SRC_FILES), $(wildcard $(addprefix $(x)/*,.c*))))
BIN_OBJ_RELES := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(BIN_SRC_FILES)))))
BIN_OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(BIN_SRC_FILES)))))

# Testing Paths
TST_SRC_PATH := $(TST_PATH)
TST_LIB_PATH := $(EXT_PATH)/munit
TST_OBJ_PATH := $(DBG_PATH)/$(TST_SRC_PATH)
TST_BIN_PATH := $(BIN_PATH)/$(TST_SRC_PATH)
TST_RPT_PATH := $(RPT_PATH)

# Test flags
TSTFLAGS :=  $(CFLAGS) $(DBGFLAG) -I$(TST_LIB_PATH)
TSTOBJFLAGS := $(TSTFLAGS) -c
TSTLNKFLAGS := $(LDFLAGS) --coverage

TST_SRC_FILES := $(wildcard $(TST_SRC_PATH)/test_*.c)
TST_OBJ_DEBUG := $(addprefix $(TST_OBJ_PATH)/, $(addsuffix .o, $(basename $(subst $(TST_SRC_PATH)/,,$(TST_SRC_FILES)))))
TST_BIN_TRGT := $(addprefix $(TST_BIN_PATH)/,$(basename $(subst $(TST_SRC_PATH)/,,$(TST_SRC_FILES))))

# clean files list
DISTCLEAN_LIST := $(OBJ_PATH) \
				  $(DBG_PATH) \
				  $(TST_OBJ_PATH)
CLEAN_LIST := $(LIB_RELS).* $(LIB_DBUG).* \
			  $(BIN_RELS) $(BIN_DBUG) \
			  $(TST_BIN_PATH) $(TST_RPT_PATH) \
			  $(DISTCLEAN_LIST)

# default rule
default: all

# Release Target Rules
$(LIB_RELS).a: $(LIB_OBJ_RELES) | $(BIN_PATH)
	$(AR) $(ARFLAGS) $@ $?

$(LIB_RELS).so: $(LIB_OBJ_RELES) | $(BIN_PATH)
	$(CC) $(CFLAGS) -shared -O3 -o $@ $? $(LDFLAGS)

$(BIN_RELS): $(BIN_OBJ_RELES) $(LIB_RELS).a | $(BIN_PATH)
	$(CC) $(CFLAGS) -O3 -o $@ $? $(LDFLAGS)

# Debug Target Rules
$(LIB_DBUG).a: $(LIB_OBJ_DEBUG) | $(BIN_PATH)
	$(AR) $(ARFLAGS) $@ $?

$(LIB_DBUG).so: $(LIB_OBJ_DEBUG) | $(BIN_PATH)
	$(CC) $(CFLAGS) $(DBGFLAG) -shared -O3 -o $@ $? $(LDFLAGS)

$(BIN_DBUG): $(BIN_OBJ_DEBUG) $(LIB_DBUG).a | $(BIN_PATH)
	$(CC) $(CFLAGS) $(DBGFLAG) -O3 -o $@ $? $(LDFLAGS)

# Object Build Rules
$(OBJ_PATH)/%.o: src/%.c* | $(OBJ_PATH)
	$(CC) $(CCOBJFLAG) -o $@ $<

$(DBG_PATH)/%.o: src/%.c* | $(DBG_PATH)
	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

# Test Target Rules
$(TST_BIN_PATH)/%: $(TST_OBJ_PATH)/%.o $(TST_OBJ_PATH)/munit.o $(LIB_DBUG).a | $(TST_BIN_PATH)
	$(CC) $(TSTFLAGS)  -o $@ $? $(TSTLNKFLAGS)

$(TST_OBJ_PATH)/%.o: $(TST_SRC_PATH)/%.c* | $(TST_OBJ_PATH)
	$(CC) $(TSTOBJFLAGS) -o $@ $<

$(TST_OBJ_PATH)/munit.o: | $(TST_OBJ_PATH)
	# Note: We disable all warnings since this is a vendored dependnecy
	$(CC) $(TSTOBJFLAGS) -w -o $@ $(TST_LIB_PATH)/munit.c

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_DIRS)

$(DBG_PATH):
	mkdir -p $(DBG_DIRS)

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
all: static bin ## Build r2u2 binary and static library for release [Default]

.PHONY: bin
bin: $(BIN_RELS) ## Build r2u2 binary for release

.PHONY: static
static: $(LIB_RELS).a ## Build statically linked r2u2 library for release

.PHONY: shared
shared: $(LIB_RELS).so ## Build dynamically linked r2u2 library for release

.PHONY: debug
debug: $(BIN_DBUG) ## Build r2u2 binary with debug logging and runtime checks enabled

.PHONY: test
test: $(TST_BIN_TRGT) ## Build r2u2 unit tests

.PHONY: coverage
coverage: $(TST_BIN_TRGT) | $(TST_RPT_PATH) ## Process all in-tree coverage output into report
	$(call coverage_proc)
	$(call coverage_html)

.PHONY: check
check: $(TST_BIN_TRGT) | $(TST_RPT_PATH) ## Run all tests and process coverage report
	$(call run_all_tests)
	$(call coverage_proc)
	$(call coverage_html)

.PHONY: clean
clean: ## Remove all build artifacts
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)

.PHONY: distclean
distclean: ## Remove intermediate build objects, leaving final targets
	@echo CLEAN $(DISTCLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)

# Variable debug printer
# Call as `make print-VARIABLE`
# From: https://www.cmcrossroads.com/article/printing-value-makefile-variable
print-%  : ; @echo $* = $($*)

# List all concrete targets
# From: https://stackoverflow.com/a/26339924
.PHONY: list
list: ## List all concrete targets
	@LC_ALL=C $(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$'

# List common targets with descriptions
# Only lists targets with "## <Description>" at the end of their declaration
# From: https://marmelab.com/blog/2016/02/29/auto-documented-makefile.html
.PHONY: help
help: ## List common targets with descriptions
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-15s\033[0m %s\n", $$1, $$2}'

# Doxygen API Documentation
# TODO - make this rebuild on source changes, not just Doxyfile changes
#doc: $(DOC_PATH)/Doxyfile ## Build API Documentation with Doxygen
#	doxygen $(DOC_PATH)/Doxyfile
