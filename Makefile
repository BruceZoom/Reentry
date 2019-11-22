CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = WithCall WithoutCall

INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Reentry.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) Reentry
DEP_FLAG = $(DEP_DEMO)

Derivation_FILES = DenotationalSemantics.v FineGrainedSemantics.v DerivationTheorem.v

WithoutCall_FILES = $(Derivation_FILES)

WithCall_FILES = $(Derivation_FILES) CoarseGrainedLogic.v

FILES = \
	$(WithoutCall_FILES:%.v=WithoutCall/%.v) \
	$(WithCall_FILES:%.v=WithCall/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

WithoutCall: \
	.depend clean $(WithoutCall_FILES:%.v=WithoutCall/%.vo)

WithCall: \
	.depend clean $(WithCall_FILES:%.v=WithCall/%.vo)

all: $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f */.*.aux */*.vo */*.glob

.DEFAULT_GOAL := WithCall

include .depend	
