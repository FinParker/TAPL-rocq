# Wrapper Makefile for TAPL Rocq Project
# Following Rocq documentation best practices

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := all

CoqMakefile: Makefile _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                    Common targets                              ##
####################################################################

all: invoke-coqmakefile

clean: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile clean

cleanall: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile cleanall
	rm -f CoqMakefile CoqMakefile.conf

install: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile install

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true

-include CoqMakefile.local
