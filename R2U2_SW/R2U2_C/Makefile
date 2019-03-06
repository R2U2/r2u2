# tool marcros
CC := gcc
CFLAGS :=
DBGFLAG := -g
CCOBJFLAG := $(CFLAGS) -c

# path marcros
BIN_PATH := bin
OBJ_PATH := target/release
SRC_PATH := src
DBG_PATH := target/debug

# compile marcros
TARGET_NAME := r2u2
ifeq ($(OS),Windows_NT)
	TARGET_NAME := $(addsuffix .exe,$(TARGET_NAME))
endif
TARGET := $(BIN_PATH)/$(TARGET_NAME)
TARGET_DEBUG := $(DBG_PATH)/$(TARGET_NAME)
MAIN_SRC := src/$(TARGET_NAME).c

# src files & obj files
SRC := $(foreach x, $(SRC_PATH), $(wildcard $(addprefix $(x)/*,.c*)))
OBJ := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(notdir $(basename $(SRC)))))
OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(notdir $(basename $(SRC)))))

# clean files list
DISTCLEAN_LIST := $(OBJ) \
				  $(OBJ_DEBUG)
CLEAN_LIST := $(TARGET) \
			  $(TARGET_DEBUG) \
			  $(DISTCLEAN_LIST)

# default rule
default: all

# non-phony targets
$(TARGET): $(OBJ) | $(BIN_PATH)
	$(CC) $(CFLAGS) -o $@ $?

$(OBJ_PATH)/%.o: $(SRC_PATH)/%.c* | $(OBJ_PATH)
	$(CC) $(CCOBJFLAG) -o $@ $<

$(TARGET_DEBUG): $(OBJ_DEBUG) | $(DBG_PATH)
	$(CC) $(CFLAGS) $(DBGFLAG) -o $@ $?

$(DBG_PATH)/%.o: $(SRC_PATH)/%.c* | $(DBG_PATH)
	$(CC) $(CCOBJFLAG) $(DBGFLAG) -o $@ $<

# Path rules
$(BIN_PATH):
	mkdir -p $(BIN_PATH)

$(OBJ_PATH):
	mkdir -p $(OBJ_PATH)

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