Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Reals.

Require Import Casper.preamble.

(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Parameter V : Set .

Parameter v_non_empty : exists v : V, True.

(** Less than order on validator names **)

Parameter v_lt : V -> V -> Prop.

Parameter v_lt_strict_order: StrictOrder v_lt.

(** V totally ordered **)

Parameter v_lt_total_order: TotalOrder v_lt.

Parameter v_ltb : V -> V -> bool.

Parameter v_lt_ltb : RelationFn v_lt v_ltb.

Corollary v_eq_dec : forall x y : V, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with v_lt.
  - apply v_lt_strict_order.
  - apply v_lt_total_order.
Qed.

Parameter v_eqb : V -> V -> bool.

Parameter v_eqb_eq : EqualityFn v_eqb.

(***********************)
(** Validator weights **)
(***********************)

Parameter weight : V -> R.

Parameter weight_positive : forall v : V, (0 < weight v)%R.
