
P4TAPP := ./libs/p4tapp.sh
PROG := sampler
MAKEFLAGS += -s
# If the first argument is "test"...
ifeq (test,$(firstword $(MAKECMDGOALS)))
  # use the rest as arguments for "test"
  RUN_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  # ...and turn them into do-nothing targets
   $(eval $(RUN_ARGS):dummy)
endif
.PHONY: test
build: $(PROG).p4 $(PROG).py
	$(P4TAPP) build_quiet $(PROG).p4
hw:
	$(P4TAPP) hw $(PROG).p4
test:
	$(P4TAPP) test $(PROG).p4 1025_test.json
sim:
	$(P4TAPP) sim $(PROG).p4
dummy: