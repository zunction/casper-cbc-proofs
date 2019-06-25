Require Import List.
Require Import Coq.Sorting.Sorted.

Require Import Casper.preamble.
Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.
Require Import Casper.sorted_lists.

Require Import Casper.LightStates.hashes.

Definition justification_type := list hash.

Definition justification_add := add_in_sorted_list_fn hash_compare.

Definition justification_add_iff := add_in_sorted_list_iff hash_compare hash_compare_strict_order.

Definition justification_add_head := add_in_sorted_list_head hash_compare hash_compare_strict_order.

Definition justification_add_tail := add_in_sorted_list_tail hash_compare hash_compare_strict_order.

Definition justification_add_sorted := add_in_sorted_list_sorted hash_compare hash_compare_strict_order.

Definition justification_add_all : list hash -> justification_type := fold_right justification_add nil.

Lemma justification_sorted : forall j : list hash,
  LocallySorted hash_lt (justification_add_all j).
Proof.
  induction j.
  -  simpl. constructor.
  - apply justification_add_sorted. assumption.
Qed.

Lemma justification_set_eq : forall hs,
  set_eq hs (justification_add_all hs).
Proof.
  induction hs; simpl.
  - apply set_eq_refl.
  - split; intros x Hin
    ;  rewrite justification_add_iff || apply justification_add_iff in Hin
    ;  destruct Hin as [Heq | Hin]
    ; try (subst; left; reflexivity)
    ; right; apply IHhs; assumption.
Qed.

Lemma justification_add_all_injective : forall hs1 hs2,
  justification_add_all hs1 = justification_add_all hs2 ->
  set_eq hs1 hs2.
Proof.
  intros.
  apply (set_equality_predicate (compare_lt hash_compare) hash_lt_strict_order) in H
  ; try apply justification_sorted.
  apply set_eq_tran with (justification_add_all hs1); try apply justification_set_eq.
  apply set_eq_tran with (justification_add_all hs2); try assumption.
  apply set_eq_comm. apply justification_set_eq.
Qed.

Definition justification_in := inb hash_eq_dec.

Definition justification_compare := list_compare hash_compare.

Definition justification_compare_strict_order :=
  list_compare_strict_order hash hash_compare hash_compare_strict_order.

Definition justification_eq_dec :=
  list_compare_eq_dec hash hash_compare hash_compare_strict_order.

