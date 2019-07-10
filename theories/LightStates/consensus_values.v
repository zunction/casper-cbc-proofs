(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Module Type Consensus_Values.

Parameter C : Set .

Axiom c_non_empty : exists c : C, True.

Axiom c_eq_dec : forall (c1 c2 : C), {c1 = c2} + {c1 <> c2}.

End Consensus_Values.