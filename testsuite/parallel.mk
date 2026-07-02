include $(CONFDIR)/suitemake.mk

include $(CONFDIR)/all_tests.mk

.PHONY: $(ALL_TESTS)
$(ALL_TESTS):
	cd $(dir $@) && BSC_VERILATOR_BUILD_JOBS=1 $(RUNTESTENV) $(RUNTEST) $(RUNTESTFLAGS) $(PARALLEL_FLAGS) $(notdir $@)


.PHONY: run-tests
run-tests: $(ALL_TESTS)
