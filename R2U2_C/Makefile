# tool macros
CC := gcc

# path macros
BIN_PATH := bin
OBJ_PATH := target/release
SRC_PATH := src
DBG_PATH := target/debug

SRC_DIRS := $(SRC_PATH) $(SRC_PATH)/TL $(SRC_PATH)/binParser $(SRC_PATH)/AT \
	$(SRC_PATH)/AT/filters $(SRC_PATH)/prognostics
OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))
OBJ_DBG_DIRS := $(DBG_PATH) $(addprefix $(DBG_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))

# Search paths and libs
IDIR=$(SRC_DIRS)
LIBS := fftw3
IN_LIBS=$(shell pkg-config --cflags $(LIBS))
LD_LIBS=$(shell pkg-config --libs $(LIBS)) -lm

CFLAGS :=-std=c99 $(IDIR:%=-I%) $(IN_LIBS) -DR2U2_STANDALONE
ifdef R2U2_AT
	CFLAGS := $(CFLAGS) -DR2U2_AT
endif
DBGFLAG := -g -Wall -Wextra -pedantic -Wno-gnu-binary-literal -DR2U2_DEBUG
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

# clean files list
DISTCLEAN_LIST := $(OBJ_PATH) \
				  $(DBG_PATH)
CLEAN_LIST := $(TARGET_RELES) \
			  $(TARGET_DEBUG) \
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

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_DIRS)

$(DBG_PATH):
	mkdir -p $(OBJ_DBG_DIRS)

# phony rules
.PHONY: all
all: $(TARGET_RELES)

.PHONY: debug
debug: $(TARGET_DEBUG)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo CLEAN $(DISTCLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)

print-%  : ; @echo $* = $($*)

#doxygen documentation setup
doc: ./Doxyfile
	doxygen ./Doxyfile

