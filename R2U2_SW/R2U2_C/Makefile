# tool marcros
CC := gcc

# path marcros
BIN_PATH := bin
OBJ_PATH := target/release
SRC_PATH := src
DBG_PATH := target/debug

SRC_DIRS := $(SRC_PATH) $(SRC_PATH)/AT $(SRC_PATH)/TL $(SRC_PATH)/prognostics
OBJ_DIRS := $(OBJ_PATH) $(addprefix $(OBJ_PATH), $(subst $(SRC_PATH),,$(SRC_DIRS)))

# Search paths and libs
IDIR =$(SRC_DIRS)
LDIR =../lib
LIBS=-lm

CFLAGS :=$(IDIR:%=-I%) -DR2U2_STANDALONE
DBGFLAG := -g -Wall -Wextra -pendantic
CCOBJFLAG := $(CFLAGS) -c

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
DISTCLEAN_LIST := $(OBJ) \
				  $(OBJ_DEBUG)
CLEAN_LIST := $(TARGET) \
			  $(TARGET_DEBUG) \
			  $(DISTCLEAN_LIST)

# default rule
default: all
	@echo SRC_PATH: $(SRC_PATH)
	@echo OBJ_PATH: $(OBJ_PATH)
	@echo SRC_DIRS: $(SRC_DIRS)
	@echo OBJ_DIRS: $(OBJ_DIRS)
	@echo SRC: $(SRC)
	@echo OBJ: $(OBJ)

# non-phony targets
$(TARGET): $(OBJ) | $(BIN_PATH)
	$(CC) $(CFLAGS) -o $@ $?

$(OBJ_PATH)/%.o: src/%.c* | $(OBJ_PATH)
	$(CC) $(CCOBJFLAG) -o $@ $<

$(TARGET_DEBUG): $(OBJ_DEBUG) | $(DBG_PATH)
	$(CC) $(CFLAGS) $(DBGFLAG) -o $@ $?

$(DBG_PATH)/%.o: %.c* | $(DBG_PATH)
	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_DIRS)

$(DBG_PATH):
	mkdir -p $(DBG_PATH)

# phony rules
.PHONY: all
all: $(TARGET)

.PHONY: debug
debug: $(TARGET_DEBUG)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -f $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -f $(DISTCLEAN_LIST)