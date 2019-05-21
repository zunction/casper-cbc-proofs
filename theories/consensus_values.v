Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.

(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Parameter C : Set .

Parameter c_non_empty : exists c : C, True.

(** Less than order on consensus values **)

Parameter c_lt : C -> C -> Prop.

Parameter c_lt_strict_order: StrictOrder c_lt.

(** C totally ordered **)

Parameter c_lt_total_order: TotalOrder c_lt.

Corollary c_eq_dec : forall x y : C, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with c_lt.
  - apply c_lt_strict_order.
  - apply c_lt_total_order.
Qed.
