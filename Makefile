CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

Reentry_PREFIX = AST ASTLc Hoare HoareLc

WithoutCall_FILES = \
	$(foreach prefix, $(Reentry_PREFIX), $(prefix)_woc.v)

WithCall_FILES = \
	$(foreach prefix, $(Reentry_PREFIX), $(prefix)_wc.v)

Relation_PREFIX = \
	DSRelation HRelation

Unified_FILES = \
	AST.v Label.v ASTLc.v Hoare.v HoareLc.v \
	$(foreach prefix, $(Relation_PREFIX), $(prefix)_woc.v $(prefix)_wc.v)

FILES = \
	$(WithoutCall_FILES) $(WithCall_FILES) $(Unified_FILES)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CURRENT_DIR)/$*.v
#	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

WithoutCall: \
	.depend $(WithoutCall_FILES:%.v=%.vo)

WithCall: \
	.depend $(WithCall_FILES:%.v=%.vo)

Unified: \
	.depend $(Unified_FILES:%.v=%.vo)

all: $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(FILES) > .depend
#	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(FILES) > .depend
#	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob .*.aux

.DEFAULT_GOAL := WithoutCall

include .depend
	
	