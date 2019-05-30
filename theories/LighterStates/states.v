Require Import Coq.Classes.RelationClasses.
Require Import List.

Require Import Casper.preamble.

Require Import Casper.sorted_lists.
Require Import Casper.LightStates.messages.

(** Hash sets **)

Definition state : Set := list message.

Definition state_in := Inb message_compare.

Definition state_compare := list_compare message_compare.

Definition state_compare_strict_order : CompareStrictOrder state_compare :=
  list_compare_strict_order message message_compare message_compare_strict_order.

Lemma state_compare_refl : forall sigma, state_compare sigma sigma = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 state_compare_strict_order).
Qed.

Definition state_lt := compare_lt state_compare.

Definition state_lt_strict_order : StrictOrder state_lt :=
  compare_lt_strict_order state state_compare state_compare_strict_order.

Definition state_lt_total_order : TotalOrder state_lt :=
  compare_lt_total_order state state_compare state_compare_strict_order.

Definition state_eq_dec : EqualityDec state :=
  compare_eq_dec state state_compare state_compare_strict_order.

Definition state_union : state -> state -> state := SortMessages.merge.