TOP = .
include $(TOP)/configure/CONFIG

DIRS += configure

DIRS += src
src_DEPEND_DIRS = configure

DIRS += src/Db
DIRS += src/opi

DIRS += sim
sim_DEPEND_DIRS = configure src

DIRS += common/wf/Db
common/wf/Db_DEPEND_DIRS = configure

DIRS += common/wf/opi
common/wf/opi_DEPEND_DIRS = configure

DIRS += feedApp
feedApp_DEPEND_DIRS = configure src

DIRS += tests
tests_DEPEND_DIRS = configure src src/Db

DIRS += iocBoot

UNINSTALL_DIRS += $(INSTALL_LOCATION)/opi

include $(TOP)/configure/RULES_TOP

sphinx:
	$(MAKE) -C documentation html

sphinx-clean:
	$(MAKE) -C documentation html clean

sphinx-commit: sphinx
	touch documentation/_build/html/.nojekyll
	./commit-gh.sh documentation/_build/html

.PHONY: sphinx sphinx-commit sphinx-clean
