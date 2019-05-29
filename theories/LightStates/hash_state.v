Require Import List.
Import ListNotations.
Require Import Coq.Sorting.Sorted.

Require Import Casper.sorted_lists.
Require Import Casper.hash.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.

Inductive hash_state : state -> list hash -> Prop :=
  | hash_state_nil :  hash_state [] []
  | hash_state_cons : forall msg sigma hs hs',
       hash_state sigma hs ->
       add_in_hash_set (Hash msg) hs hs' ->
       hash_state (msg :: sigma) hs'.

Theorem hash_state_sorted : forall sigma hs,
  hash_state sigma hs -> LocallySorted hash_lt hs.
Proof.
  induction sigma; intros.
  - inversion H; subst. constructor.
  - inversion H; subst. apply IHsigma in H2.
    apply (add_in_sorted_list_sorted hash_lt (Hash a) hs0); try assumption.
    apply hash_lt_strict_order.
Qed.

