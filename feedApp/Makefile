TOP=..

include $(TOP)/configure/CONFIG
ifneq ($(PYDEVSUP),)
include $(PYDEVSUP)/configure/CONFIG_PY
endif
#----------------------------------------
#  ADD MACRO DEFINITIONS AFTER THIS LINE
#=============================

#=============================
# Build the IOC application

PROD_IOC += feedioc

DBD += feedioc.dbd

feedioc_DBD += base.dbd
feedioc_DBD += system.dbd
feedioc_DBD += feed.dbd

feedioc_SRCS += feedMain.cpp
feedioc_SRCS += feedioc_registerRecordDeviceDriver.cpp

ifneq ($(BUSY),)
feedioc_DBD += busySupport.dbd
feedioc_LIBS += busy asyn
endif

ifneq ($(AUTOSAVE),)
feedioc_DBD += asSupport.dbd
feedioc_LIBS += autosave

DB_INSTALLS += $(firstword $(wildcard $(AUTOSAVE)/asApp/Db/save_restoreStatus.db $(AUTOSAVE)/db/save_restoreStatus.db))
endif

ifneq ($(PYDEVSUP),)
feedioc_DBD += pyDevSup.dbd
feedioc_LIBS += pyDevSup$(PY_LD_VER)
endif

ifneq ($(ASYN),)
feedioc_DBD += asyn.dbd
feedioc_LIBS += asyn
endif

feedioc_LIBS += feed

ifeq ($(USE_FFTW),YES)
feedioc_LIBS += fftw3 
else ifeq ($(USE_SYS_FFTW),YES)
feedioc_SYS_LIBS += fftw3 
else ifeq ($(USE_PKG_FFTW),YES)
fftw3_DIR = $(FFTW_LIB)
feedioc_LIBS += fftw3 
endif

feedioc_LIBS += $(EPICS_BASE_IOC_LIBS)
feedioc_SYS_LIBS += z

#===========================

include $(TOP)/configure/RULES
ifneq ($(PYDEVSUP),)
include $(PYDEVSUP)/configure/RULES_PY
endif
#----------------------------------------
#  ADD RULES AFTER THIS LINE
