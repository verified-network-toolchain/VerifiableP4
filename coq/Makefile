# ########## Configuration ##########

# See the file BUILD_ORGANIZATION.md
# for explanations of why this is the way it is.

-include CONFIGURE

# ##### Configure Coq #####

# ANNOTATE=true   # label chatty output from coqc with file name
ANNOTATE=silent   # suppress chatty output from coqc
# ANNOTATE=false  # leave chatty output of coqc unchanged
# ANNOTATE=echo   # like false, but in addition echo commands

# DO NOT DISABLE coqc WARNINGS!  That would hinder the Coq team's continuous integration.
COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep -vos
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)
COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')

# Check Coq version

# COQVERSION= 8.11.0 or-else 8.11.1 or-else 8.11.2 or-else 8.12+beta1 or-else 8.12.0

# COQV=$(shell $(COQC) -v)
# ifneq ($(IGNORECOQVERSION),true)
#   ifeq ("$(filter $(COQVERSION),$(COQV))","")
#     $(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
#   endif
# endif

# ########## File Lists ##########

FILES = \
  Info.v Types.v Typed.v Prog.v


# ########## Rules ##########

COQFLAGS=-R . ProD3

%.vo: COQF=$(COQFLAGS)

%.vo: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQF) $*.v; date +'%s.%N after' >>timings" 2>>timings
	echo true timings
	@bash -c "/usr/bin/time --output=TIMINGS -a -f '%e real, %U user, %S sys %M mem, '\"$(shell wc $*.v)\" $(COQC) $(COQF) $*.v"
#	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQF) $*.v"
else ifeq ($(TIMINGS), simple)
	@/usr/bin/time -f 'TIMINGS %e real, %U user, %S sys %M kbytes: '"$*.v" $(COQC) $(COQF) $*.v
else ifeq ($(strip $(ANNOTATE)), true)
	@$(COQC) $(COQF) $*.v | awk '{printf "%s: %s\n", "'$*.v'", $$0}'
else ifeq ($(strip $(ANNOTATE)), silent)
	@$(COQC) $(COQF) $*.v >/dev/null
else ifeq ($(strip $(ANNOTATE)), echo)
	$(COQC) $(COQF) $*.v >/dev/null
else
	@$(COQC) $(COQF) $*.v
#	@util/annotate $(COQC) $(COQF) $*.v
endif


# ########## Targets ##########

default_target: extraction

extraction: extraction/STAMP

extraction/STAMP: files extraction/extraction.v
	@rm -f extraction/*.ml extraction/*.mli
	@$(COQBIN)coqtop $(COQFLAGS) -batch -load-vernac-source extraction/extraction.v
#	@$(COQC) $(COQFLAGS) extraction/extraction.v
	@touch extraction/STAMP

files: _CoqProject $(FILES:.v=.vo)

clean:
	@rm *.vo *.vos *.vok .*.aux _CoqProject

_CoqProject: Makefile
	@echo $(COQFLAGS) > _CoqProject

.depend depend:
	@echo 'coqdep ... >.depend'
	@$(COQDEP) $(COQFLAGS) 2>&1 >.depend $(FILES) | grep -v 'Warning:.*found in the loadpath' || true

include .depend

