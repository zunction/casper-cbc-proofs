Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.

(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Parameter C : Set .

Parameter c_non_empty : exists c : C, True.

(** comparison function on consensus values **)

Parameter c_compare : C -> C -> comparison.

(** C totally ordered **)

Parameter c_compare_strict_order : CompareStrictOrder c_compare.

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
