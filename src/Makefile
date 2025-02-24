
TOP=..

include $(TOP)/configure/CONFIG
#----------------------------------------
#  ADD MACRO DEFINITIONS AFTER THIS LINE
#=============================

LIBRARY += feed
DBD += feed.dbd

LIB_LIBS += $(EPICS_BASE_IOC_LIBS)
LIB_SYS_LIBS += z

SRC_DIRS += $(TOP)/src/util
LIB_SRCS += jblob.cpp
LIB_SRCS += zpp.cpp
LIB_SRCS += rom.cpp
LIB_SRCS += utils.cpp

SRC_DIRS += $(TOP)/src/sim
LIB_SRCS += simulator.cpp
LIB_SRCS += simulator_rfs.cpp
LIB_SRCS += simulator_hires.cpp

SRC_DIRS += $(TOP)/src/driver
LIB_SRCS += device.cpp
LIB_SRCS += devmain.cpp
LIB_SRCS += devutil.cpp
LIB_SRCS += devreg.cpp
LIB_SRCS += devsignal.cpp
LIB_SRCS += devwatch.cpp
LIB_SRCS += devhack.cpp
LIB_SRCS += iocsh.cpp

SRC_DIRS += $(TOP)/src/rf
LIB_SRCS += asub.c
LIB_SRCS += asub_setamp.c
LIB_SRCS += calc.c

ifeq ($(USE_FFTW),YES)
LIB_LIBS += fftw3 
LIB_SRCS += fftmain.c
LIB_SRCS += fftdev.c
else ifeq ($(USE_SYS_FFTW),YES)
LIB_SYS_LIBS += fftw3 
LIB_SRCS += fftmain.c
LIB_SRCS += fftdev.c
else ifeq ($(USE_PKG_FFTW),YES)
# define FFTW_LIB in CONFIG_SITE
USR_INCLUDES += $(addprefix -I,$(FFTW_INCLUDE))
fftw3_DIR = $(FFTW_LIB)
LIB_LIBS += fftw3 
LIB_SRCS += fftmain.c
LIB_SRCS += fftdev.c
else
LIB_SRCS += fftnoop.c
endif

#===========================

include $(TOP)/configure/RULES
#----------------------------------------
#  ADD RULES AFTER THIS LINE

ifeq ($(OS_CLASS),Linux)
cppcheck:
	cppcheck \
 --std=posix --std=c99 --std=c++03 --enable=all \
 -D__GNUC__ \
 $(filter -D%,$(CPPFLAGS)) \
 $(filter -U%,$(CPPFLAGS)) \
 $(INCLUDES) \
 ../driver ../util ../sim ../../tests

else
cppcheck:
	echo "no configuration to use cppcheck for $(OS_CLASS) targets.  (not run in O.<arch> sub-dir?)"
endif

.PHONY: cppcheck
