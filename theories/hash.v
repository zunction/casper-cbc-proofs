Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.
Require Import Casper.sorted_lists.

(*******************)
(** Hash universe **)
(*******************)

Parameter hash : Set .

(** Comparison function on hashes **)

Parameter hash_compare : hash -> hash -> comparison.

(** V totally ordered **)

Parameter hash_compare_strict_order : CompareStrictOrder hash_compare.

Definition hash_lt : hash -> hash -> Prop := compare_lt hash_compare.

Definition hash_lt_strict_order: StrictOrder hash_lt :=
  compare_lt_strict_order hash hash_compare hash_compare_strict_order.

Definition hash_lt_total_order: TotalOrder hash_lt :=
  compare_lt_total_order hash hash_compare hash_compare_strict_order.

Corollary hash_eq_dec : forall x y : hash, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with hash_lt.
  - apply hash_lt_strict_order.
  - apply hash_lt_total_order.
Qed.

(** Hash sets **)
Definition hash_lex := @list_lex hash (compare_lt hash_compare).

Definition hash_lex_strict_order : StrictOrder hash_lex :=
  list_lex_strict_order hash hash_compare hash_compare_strict_order.

Definition hash_lex_total_order : TotalOrder hash_lex :=
  list_lex_total_order hash hash_compare hash_compare_strict_order.

Definition add_in_hash_set := @add_in_sorted hash hash_lt.

(** TODO: hash_eq_dec **)

