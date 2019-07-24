COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." Casper

SOURCE := preamble.v ListExtras.v ListSetExtras.v RealsExtras.v sorted_lists.v protocol.v protocol_eq.v fullnode.v fullnode_eq.v lightnode_eq.v
VO_FILE := $(shell find "." -type f -name '*.vo')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
AUX_FILE := $(shell find "." -type f -name '*.vo.aux')

$(SOURCE:%.v=%.vo): %.vo: %.v
			@echo COQC $*.v
			@$(COQC) $(COQ_FLAG) $*.v

dep:
	@$(COQDEP) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)
	
clean:
	@rm $(VO_FILE) $(GLOB_FILE) $(AUX_FILE)

.DEFAULT_GOAL := all

include .depend

