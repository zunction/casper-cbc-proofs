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

Lemma hash_compare_refl : forall h, hash_compare h h = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 hash_compare_strict_order).
Qed.

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

Definition hash_list_compare := list_compare hash_compare.

Definition hash_list_compare_strict_order : CompareStrictOrder hash_list_compare :=
  list_compare_strict_order hash hash_compare hash_compare_strict_order.

Lemma hash_list_compare_refl : forall hs, hash_list_compare hs hs = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 hash_list_compare_strict_order).
Qed.

Definition hash_list_lt := compare_lt hash_list_compare.

Definition hash_list_lt_strict_order : StrictOrder hash_list_lt :=
  compare_lt_strict_order (list hash) hash_list_compare hash_list_compare_strict_order.

Definition hash_list_lt_total_order : TotalOrder hash_list_lt :=
  compare_lt_total_order (list hash) hash_list_compare hash_list_compare_strict_order.

Definition add_in_hash_set := @add_in_sorted hash hash_lt.

(** TODO: hash_eq_dec **)

