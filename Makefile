PYTHON=python2.7

all: coq_build

coq_build: Makefile.coq
	+$(MAKE) -f Makefile.coq all


graph.dpd: coq_build
	coqtop -Q theories Casper < dependency_graph.v

%.dot: %.dpd
	dpd2dot $<

%.svg: %.dot
	dot -Tsvg $< > $@

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf *.dot *.svg *.dpd

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean coq_build
