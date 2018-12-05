###########################################################################
## Makefile generated for MATLAB file/project 'BHM'. 
## 
## Makefile     : BHM_rtw.mk
## Generated on : Thu Apr 02 17:30:49 2015
## MATLAB Coder version: 2.7 (R2014b)
## 
## Build Info:
## 
## Final product: $(RELATIVE_PATH_TO_ANCHOR)/BHM.lib
## Product type : static-library
## 
###########################################################################

###########################################################################
## MACROS
###########################################################################

# Macro Descriptions:
# PRODUCT_NAME            Name of the system to build
# MAKEFILE                Name of this makefile
# COMPUTER                Computer type. See the MATLAB "computer" command.
# PERL                    PERL Tool
# GEN_LNK_SCRIPT          Perl script to generate the command file
# CMD_FILE                Command file

PRODUCT_NAME              = BHM
MAKEFILE                  = BHM_rtw.mk
COMPUTER                  = PCWIN64
MATLAB_ROOT               = C:/PROGRA~1/MATLAB/R2014b
MATLAB_BIN                = C:/PROGRA~1/MATLAB/R2014b/bin
MATLAB_ARCH_BIN           = C:/PROGRA~1/MATLAB/R2014b/bin/win64
MASTER_ANCHOR_DIR         = 
START_DIR                 = C:/Users/iroychou/Documents/Projects/rt-R2U2/Battery
ARCH                      = win64
RELATIVE_PATH_TO_ANCHOR   = .
PERL                      = $(MATLAB_ROOT)/sys/perl/win32/bin/perl.exe
GEN_LNK_SCRIPT            = $(MATLAB_ROOT)/rtw/c/tools/mkvc_lnk.pl
CMD_FILE                  = $(PRODUCT_NAME).lnk

###########################################################################
## TOOLCHAIN SPECIFICATIONS
###########################################################################

# Toolchain Name:          LCC-win64 v2.4.1 | gmake (64-bit Windows)
# Supported Version(s):    2.4.1
# ToolchainInfo Version:   R2014b
# Specification Revision:  1.0
# 

#-----------
# MACROS
#-----------

SHELL              = cmd
LCC_ROOT           = $(MATLAB_ROOT)/sys/lcc64/lcc64
LCC_BUILDLIB       = $(LCC_ROOT)/bin/buildlib
LCC_LIB            = $(LCC_ROOT)/lib64
MW_EXTERNLIB_DIR   = $(MATLAB_ROOT)/extern/lib/win64/microsoft
MW_LIB_DIR         = $(MATLAB_ROOT)/lib/win64
TOOLCHAIN_INCLUDES = -I$(LCC_ROOT)/include64
MEX_OPTS_FILE      = $(MATLAB_ROOT/rtw/c/tools/lcc-win64.xml

TOOLCHAIN_SRCS = 
TOOLCHAIN_INCS = 
TOOLCHAIN_LIBS = 

#------------------------
# BUILD TOOL COMMANDS
#------------------------

# C Compiler: Lcc-win64 C Compiler
CC_PATH = $(LCC_ROOT)/bin
CC = $(CC_PATH)/lcc64

# Linker: Lcc-win64 Linker
LD_PATH = $(LCC_ROOT)/bin
LD = $(LD_PATH)/lcclnk64

# Archiver: Lcc-win64 Archiver
AR_PATH = $(LCC_ROOT)/bin
AR = $(AR_PATH)/lcclib64

# MEX Tool: MEX Tool
MEX_PATH = $(MATLAB_BIN)
MEX = $(MEX_PATH)/mex

# Download: Download
DOWNLOAD =

# Execute: Execute
EXECUTE = $(PRODUCT)

# Builder: GMAKE Utility
MAKE_PATH = %MATLAB%\bin\win64
MAKE = $(MAKE_PATH)/gmake


#-------------------------
# Directives/Utilities
#-------------------------

CDEBUG              = -g
C_OUTPUT_FLAG       = -Fo
LDDEBUG             =
OUTPUT_FLAG         = -o
ARDEBUG             =
STATICLIB_OUTPUT_FLAG = /out:
MEX_DEBUG           = -g
RM                  = @del /F
ECHO                = @echo
MV                  = @move
RUN                 =

#--------------------------------------
# "Faster Runs" Build Configuration
#--------------------------------------

ARFLAGS              =
CFLAGS               = -c -w -noregistrylookup -nodeclspec -I$(LCC_ROOT)/include64
DOWNLOAD_FLAGS       =
EXECUTE_FLAGS        =
LDFLAGS              = -s -L$(LCC_LIB) $(LDFLAGS_ADDITIONAL)
MEX_CFLAGS           = -win64 $(MEX_SRC) $(MEX_OPT_FILE)$(INCLUDES) -outdir $(RELATIVE_PATH_TO_ANCHOR)
MEX_LDFLAGS          = LINKFLAGS="$$LINKFLAGS $(LDFLAGS_ADDITIONAL)"
MAKE_FLAGS           = -f $(MAKEFILE)
SHAREDLIB_LDFLAGS    = -dll -entry LibMain -s -L$(LCC_LIB) $(LDFLAGS_ADDITIONAL) $(DEF_FILE)

#--------------------
# File extensions
#--------------------

H_EXT               = .h
OBJ_EXT             = .obj
C_EXT               = .c
EXE_EXT             = .exe
SHAREDLIB_EXT       = .dll
STATICLIB_EXT       = .lib
MEX_EXT             = .mexw64
MAKE_EXT            = .mk


###########################################################################
## OUTPUT INFO
###########################################################################

PRODUCT = $(RELATIVE_PATH_TO_ANCHOR)/BHM.lib
PRODUCT_TYPE = "static-library"
BUILD_TYPE = "Static Library"

###########################################################################
## INCLUDE PATHS
###########################################################################

INCLUDES_BUILDINFO = -I$(START_DIR) -I$(START_DIR)/src -I$(MATLAB_ROOT)/extern/include -I$(MATLAB_ROOT)/simulink/include -I$(MATLAB_ROOT)/rtw/c/src -I$(MATLAB_ROOT)/rtw/c/src/ext_mode/common -I$(MATLAB_ROOT)/rtw/c/ert

INCLUDES = $(INCLUDES_BUILDINFO)

###########################################################################
## DEFINES
###########################################################################

DEFINES_STANDARD = -DMODEL=BHM -DHAVESTDIO -DUSE_RTMODEL

DEFINES = $(DEFINES_STANDARD)

###########################################################################
## SOURCE FILES
###########################################################################

SRCS = $(START_DIR)/src/BHM_rtwutil.c $(START_DIR)/src/BHM_initialize.c $(START_DIR)/src/BHM_terminate.c $(START_DIR)/src/CellConstantInputPredict.c $(START_DIR)/src/CellConstantInputPredictLookup.c $(START_DIR)/src/computeSOCEstimate.c $(START_DIR)/src/getInitialBatteryState.c $(START_DIR)/src/UKFInitialize.c $(START_DIR)/src/UKFStep.c $(START_DIR)/src/rdivide.c $(START_DIR)/src/repmat.c $(START_DIR)/src/ThresholdEqnResistance.c $(START_DIR)/src/power.c $(START_DIR)/src/log.c $(START_DIR)/src/ThresholdEqnCurrent.c $(START_DIR)/src/ThresholdEqnPower.c $(START_DIR)/src/StateEqnResistance.c $(START_DIR)/src/asinh.c $(START_DIR)/src/StateEqnCurrent.c $(START_DIR)/src/StateEqnPower.c $(START_DIR)/src/fprintf.c $(START_DIR)/src/colon.c $(START_DIR)/src/fileManager.c $(START_DIR)/src/computeSigmaPoints.c $(START_DIR)/src/wmean.c $(START_DIR)/src/wcov.c $(START_DIR)/src/OutputEqnUKF.c $(START_DIR)/src/StateEqnUKF.c $(START_DIR)/src/BHM_emxutil.c $(START_DIR)/src/BHM_emxAPI.c $(START_DIR)/src/rt_nonfinite.c $(START_DIR)/src/rtGetNaN.c $(START_DIR)/src/rtGetInf.c

ALL_SRCS = $(SRCS)

###########################################################################
## OBJECTS
###########################################################################

OBJS = BHM_rtwutil.obj BHM_initialize.obj BHM_terminate.obj CellConstantInputPredict.obj CellConstantInputPredictLookup.obj computeSOCEstimate.obj getInitialBatteryState.obj UKFInitialize.obj UKFStep.obj rdivide.obj repmat.obj ThresholdEqnResistance.obj power.obj log.obj ThresholdEqnCurrent.obj ThresholdEqnPower.obj StateEqnResistance.obj asinh.obj StateEqnCurrent.obj StateEqnPower.obj fprintf.obj colon.obj fileManager.obj computeSigmaPoints.obj wmean.obj wcov.obj OutputEqnUKF.obj StateEqnUKF.obj BHM_emxutil.obj BHM_emxAPI.obj rt_nonfinite.obj rtGetNaN.obj rtGetInf.obj

ALL_OBJS = $(OBJS)

###########################################################################
## PREBUILT OBJECT FILES
###########################################################################

PREBUILT_OBJS = 

###########################################################################
## LIBRARIES
###########################################################################

LIBS = 

###########################################################################
## SYSTEM LIBRARIES
###########################################################################

SYSTEM_LIBS = 

###########################################################################
## ADDITIONAL TOOLCHAIN FLAGS
###########################################################################

#---------------
# C Compiler
#---------------

CFLAGS_BASIC = $(DEFINES) $(INCLUDES)

CFLAGS += $(CFLAGS_BASIC)

###########################################################################
## PHONY TARGETS
###########################################################################

.PHONY : all build clean info prebuild download execute


all : build
	@echo "### Successfully generated all binary outputs."


build : prebuild $(PRODUCT)


prebuild : 


download : build


execute : download


###########################################################################
## FINAL TARGET
###########################################################################

#---------------------------------
# Create a static library         
#---------------------------------

$(PRODUCT) : $(OBJS) $(PREBUILT_OBJS)
	$(PERL) $(GEN_LNK_SCRIPT) $(CMD_FILE) $(subst /,\,$(OBJS))
	@echo "### Creating static library "$(PRODUCT)" ..."
	$(AR) $(ARFLAGS) /out:$(PRODUCT) @$(CMD_FILE)
	@echo "### Created: $(PRODUCT)"
	$(RM) $(CMD_FILE)


###########################################################################
## INTERMEDIATE TARGETS
###########################################################################

#---------------------
# SOURCE-TO-OBJECT
#---------------------

%.obj : $(RELATIVE_PATH_TO_ANCHOR)/%.c
	$(CC) $(CFLAGS) -Fo"$@" $(subst /,\,"$<")


%.obj : $(MATLAB_ROOT)/rtw/c/src/%.c
	$(CC) $(CFLAGS) -Fo"$@" $(subst /,\,"$<")


%.obj : $(START_DIR)/%.c
	$(CC) $(CFLAGS) -Fo"$@" $(subst /,\,"$<")


%.obj : $(START_DIR)/src/%.c
	$(CC) $(CFLAGS) -Fo"$@" $(subst /,\,"$<")


###########################################################################
## DEPENDENCIES
###########################################################################

$(ALL_OBJS) : $(MAKEFILE) rtw_proj.tmw


###########################################################################
## MISCELLANEOUS TARGETS
###########################################################################

info : 
	@echo "### PRODUCT = $(PRODUCT)"
	@echo "### PRODUCT_TYPE = $(PRODUCT_TYPE)"
	@echo "### BUILD_TYPE = $(BUILD_TYPE)"
	@echo "### INCLUDES = $(INCLUDES)"
	@echo "### DEFINES = $(DEFINES)"
	@echo "### ALL_SRCS = $(ALL_SRCS)"
	@echo "### ALL_OBJS = $(ALL_OBJS)"
	@echo "### LIBS = $(LIBS)"
	@echo "### MODELREF_LIBS = $(MODELREF_LIBS)"
	@echo "### SYSTEM_LIBS = $(SYSTEM_LIBS)"
	@echo "### TOOLCHAIN_LIBS = $(TOOLCHAIN_LIBS)"
	@echo "### CFLAGS = $(CFLAGS)"
	@echo "### LDFLAGS = $(LDFLAGS)"
	@echo "### SHAREDLIB_LDFLAGS = $(SHAREDLIB_LDFLAGS)"
	@echo "### ARFLAGS = $(ARFLAGS)"
	@echo "### MEX_CFLAGS = $(MEX_CFLAGS)"
	@echo "### MEX_LDFLAGS = $(MEX_LDFLAGS)"
	@echo "### DOWNLOAD_FLAGS = $(DOWNLOAD_FLAGS)"
	@echo "### EXECUTE_FLAGS = $(EXECUTE_FLAGS)"
	@echo "### MAKE_FLAGS = $(MAKE_FLAGS)"


clean : 
	$(ECHO) "### Deleting all derived files..."
	$(RM) $(subst /,\,$(PRODUCT))
	$(RM) $(subst /,\,$(ALL_OBJS))
	$(ECHO) "### Deleted all derived files."


