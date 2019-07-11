PYTHON=python2.7

results: theories/FullStates/common_futures.vo \
    theories/FullStates/consistent_decisions_prop_protocol_states.vo \
    theories/FullStates/consistent_decisions_prop_consensus_values.vo \
    theories/FullStates/non_triviality_decisions_prop_protocol_states.vo \
    theories/FullStates/binary_consensus_protocol.vo \
    theories/LightStates/common_futures.vo \
    theories/LightStates/consistent_decisions_prop_protocol_states.vo \
    theories/LightStates/consistent_decisions_prop_consensus_values.vo \
    theories/LightStates/non_triviality_decisions_prop_protocol_states.vo \
    theories/LightStates/binary_consensus_protocol.vo  

theories/ListExtras.vo : \
    theories/preamble.vo

theories/ListSetExtras.vo : \
    theories/ListExtras.vo \
    theories/preamble.vo

theories/sorted_lists.vo : \
    theories/preamble.vo \
    theories/ListSetExtras.vo

theories/FullStates/consensus_values.vo : \
    theories/preamble.vo \

theories/FullStates/validators.vo : \
    theories/preamble.vo \

theories/FullStates/states.vo : \
    theories/preamble.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo

theories/FullStates/estimator.vo : \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/states.vo

theories/FullStates/locally_sorted.vo : \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo

theories/FullStates/fault_weights.vo : \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/states.vo \
    theories/FullStates/locally_sorted.vo

theories/FullStates/threshold.vo : \
    theories/preamble.vo \
    theories/RealsExtras.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/fault_weights.vo

theories/FullStates/protocol_states.vo : \
    theories/preamble.vo \
    theories/ListSetExtras.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/threshold.vo \
    theories/FullStates/states.vo \
    theories/FullStates/locally_sorted.vo \
    theories/FullStates/fault_weights.vo

theories/FullStates/common_futures.vo : \
    theories/preamble.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo \
    theories/FullStates/fault_weights.vo \
    theories/FullStates/threshold.vo \
    theories/FullStates/protocol_states.vo 
    
theories/FullStates/consistent_decisions_prop_protocol_states.vo: \
    theories/preamble.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo \
    theories/FullStates/fault_weights.vo \
    theories/FullStates/threshold.vo \
     theories/FullStates/common_futures.vo

theories/FullStates/consistent_decisions_prop_consensus_values.vo: \
    theories/preamble.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo \
    theories/FullStates/fault_weights.vo \
    theories/FullStates/threshold.vo \
    theories/FullStates/consistent_decisions_prop_protocol_states.vo

theories/FullStates/non_triviality_decisions_prop_protocol_states.vo: \
    theories/preamble.vo \
    theories/ListSetExtras.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo \
    theories/FullStates/fault_weights.vo \
    theories/FullStates/threshold.vo \
    theories/FullStates/consistent_decisions_prop_protocol_states.vo

theories/FullStates/binary_consensus_protocol.vo: \
    theories/preamble.vo \
    theories/FullStates/consensus_values.vo \
    theories/FullStates/validators.vo \
    theories/FullStates/estimator.vo \
    theories/FullStates/fault_weights.vo \
    theories/FullStates/threshold.vo \
    theories/FullStates/consistent_decisions_prop_protocol_states.vo

theories/LightStates/hashes.vo: \
    theories/preamble.vo

theories/LightStates/justifications.vo: \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/sorted_lists.vo \
    theories/LightStates/hashes.vo

theories/LightStates/messages.vo: \
    theories/preamble.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/justifications.vo

theories/LightStates/hash_function.vo: \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/messages.vo

theories/LightStates/states.vo: \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/messages.vo

theories/LightStates/hash_state.vo : \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/states.vo 

theories/LightStates/estimator.vo : \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/states.vo 

theories/LightStates/fault_weights.vo : \
    theories/ListSetExtras.vo \
    theories/ListExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/states.vo

theories/LightStates/threshold.vo : \
    theories/preamble.vo \
    theories/RealsExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/fault_weights.vo

theories/LightStates/protocol_states.vo : \
    theories/preamble.vo \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/states.vo \
    theories/LightStates/hash_state.vo 
    
theories/LightStates/common_futures.vo : \
    theories/preamble.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/protocol_states.vo \
    theories/LightStates/hash_state.vo 

theories/LightStates/consistent_decisions_prop_protocol_states.vo: \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/protocol_states.vo \
    theories/LightStates/hash_state.vo \
    theories/LightStates/common_futures.vo

theories/LightStates/consistent_decisions_prop_consensus_values.vo: \
    theories/ListExtras.vo \
    theories/ListSetExtras.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/protocol_states.vo \
    theories/LightStates/hash_state.vo \
    theories/LightStates/consistent_decisions_prop_protocol_states.vo

theories/LightStates/non_triviality_decisions_prop_protocol_states.vo: \
    theories/preamble.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/protocol_states.vo \
    theories/LightStates/hash_state.vo \
    theories/LightStates/consistent_decisions_prop_protocol_states.vo

theories/LightStates/binary_consensus_protocol.vo: \
    theories/preamble.vo \
    theories/LightStates/consensus_values.vo \
    theories/LightStates/validators.vo \
    theories/LightStates/threshold.vo \
    theories/LightStates/estimator.vo \
    theories/LightStates/hashes.vo \
    theories/LightStates/hash_function.vo \
    theories/LightStates/fault_weights.vo \
    theories/LightStates/protocol_states.vo \
    theories/LightStates/hash_state.vo \
    theories/LightStates/consistent_decisions_prop_consensus_values.vo

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

.PHONY: all clean results Makefile
