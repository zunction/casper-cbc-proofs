PYTHON=python2.7

results: \
    theories/FullStates/common_futures.vo \
    theories/FullStates/consistent_decisions_prop_protocol_states.vo \
    theories/LightStates/common_futures.vo \
    theories/LightStates/consistent_decisions_prop_protocol_states.vo \
    theories/LightStates/non_triviality_decisions_prop_protocol_states.vo

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all


graph.dpd: theories/dependency_graph.v
	+$(MAKE) -f Makefile.coq theories/dependency_graph.vo


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

%.vo: %.v Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean results
