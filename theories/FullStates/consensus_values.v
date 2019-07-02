Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.

(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Module Type Consensus_Values.

Parameter C : Set .

(** Comparison function on consensus values **)
Parameter c_compare : C -> C -> comparison.

(** C totally ordered **)
Axiom c_compare_strict_order : CompareStrictOrder c_compare.

Axiom c_non_empty : exists c : C, True.

End Consensus_Values.


(************************************)
(** Properties of consensus values **)
(************************************)

Module Consensus_Values_Properties 
        (PCons : Consensus_Values) 

(* import the Module parameters in order to have access to 
   its parameters without having to use the DotNotation. *)            .
Import PCons.

Lemma c_compare_refl : forall c, c_compare c c = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 c_compare_strict_order).
Qed.

Definition c_lt : C -> C -> Prop := compare_lt c_compare.

Definition c_lt_strict_order: StrictOrder c_lt :=
  compare_lt_strict_order C c_compare c_compare_strict_order.

Definition c_lt_total_order: TotalOrder c_lt :=
  compare_lt_total_order C c_compare c_compare_strict_order.

Definition c_eq_dec : forall x y : C, {x = y} + {x <> y} :=
  compare_eq_dec C c_compare c_compare_strict_order.

Definition c_eq_fn  (x y : C) : bool :=
  match c_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

End Consensus_Values_Properties.