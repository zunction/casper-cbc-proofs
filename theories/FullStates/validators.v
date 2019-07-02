Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Reals.

Require Import Casper.preamble.


Module Type Validators.

(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Parameter V : Set .

(** Comparison function on validator names **)
Parameter v_compare : V -> V -> comparison.

(** V totally ordered **)
Parameter v_compare_strict_order : CompareStrictOrder v_compare.

Axiom v_non_empty : exists v : V, True.

(***********************)
(** Validator weights **)
(***********************)

Parameter weight : V -> R.

Axiom weight_positive : forall v : V, (0 < weight v)%R.


(****************)
(** Properties **)
(****************)

Lemma v_compare_refl : forall v, v_compare v v = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 v_compare_strict_order).
Qed.

Definition v_lt : V -> V -> Prop := compare_lt v_compare.

Definition v_lt_strict_order: StrictOrder v_lt :=
  compare_lt_strict_order V v_compare v_compare_strict_order.

Definition v_lt_total_order: TotalOrder v_lt :=
  compare_lt_total_order V v_compare v_compare_strict_order.

Definition v_eq_dec : forall x y : V, {x = y} + {x <> y} :=
  compare_eq_dec V v_compare v_compare_strict_order.

Definition v_eq_fn  (x y : V) : bool :=
  match v_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

End Validators.