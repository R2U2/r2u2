# tool marcros
CC := gcc

# path marcros
BIN_PATH := bin
OBJ_PATH := target/release
SRC_PATH := src
DBG_PATH := target/debug
VDR_PATH := vendor

SRC_DIRS := $(SRC_PATH) $(SRC_PATH)/AT $(SRC_PATH)/TL $(SRC_PATH)/inputs $(SRC_PATH)/prognostics $(SRC_PATH)/binParser $(SRC_PATH)/CSVProcess
OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))

# Search paths and libs
IDIR=$(SRC_DIRS) $(VDR_PATH)/include
LIBS := fftw3
IN_LIBS=$(shell pkg-config --cflags $(LIBS))
LD_LIBS=$(shell pkg-config --libs $(LIBS)) -lm -L $(VDR_PATH)/lib -lcsv

CFLAGS :=-std=c99 $(IDIR:%=-I%) $(IN_LIBS) -DR2U2_STANDALONE
DBGFLAG := -g -Wall -Wextra -pendantic
CCOBJFLAG := $(CFLAGS) -c
LDFLAGS := $(LD_LIBS)

# compile marcros
TARGET_NAME := r2u2
ifeq ($(OS),Windows_NT)
	TARGET_NAME := $(addsuffix .exe,$(TARGET_NAME))
endif
TARGET := $(BIN_PATH)/$(TARGET_NAME)
TARGET_DEBUG := $(DBG_PATH)/$(TARGET_NAME)
MAIN_SRC := src/$(TARGET_NAME).c

# src files & obj files
SRC := $(foreach x, $(SRC_DIRS), $(wildcard $(addprefix $(x)/*,.c*)))
OBJ := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(SRC)))))
OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(basename $(subst src/,,$(SRC)))))

# clean files list
DISTCLEAN_LIST := $(OBJ_PATH) \
				  $(DBG_PATH)
CLEAN_LIST := $(TARGET) \
			  $(TARGET_DEBUG) \
			  $(DISTCLEAN_LIST)

# default rule
default: all

# non-phony targets
$(TARGET): $(OBJ) | $(BIN_PATH)
	$(CC) $(CFLAGS) -o $@ $? $(LDFLAGS)

$(OBJ_PATH)/%.o: src/%.c* | $(OBJ_PATH)
	cd $(VDR_PATH) && $(MAKE) all
	$(CC) $(CCOBJFLAG) -o $@ $<

$(TARGET_DEBUG): $(OBJ_DEBUG) | $(DBG_PATH)
	$(CC) $(CFLAGS) $(LDFLAGS) $(DBGFLAG) -o $@ $?

$(DBG_PATH)/%.o: %.c* | $(DBG_PATH)
	cd $(VDR_PATH) && $(MAKE) debug
	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_DIRS)

$(DBG_PATH):
	mkdir -p $(DBG_PATH)

$(VDR_PATH):
	mkdir -p $(VDR_PATH)/include $(VDR_PATH)/lib

# phony rules
.PHONY: all
all: $(TARGET)

.PHONY: debug
debug: $(TARGET_DEBUG)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(CLEAN_LIST)
	cd $(VDR_PATH) && $(MAKE) clean

.PHONY: distclean
distclean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -rf $(DISTCLEAN_LIST)
	cd $(VDR_PATH) && $(MAKE) distclean

print-%  : ; @echo $* = $($*)