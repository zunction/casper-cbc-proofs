Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.

Definition hash_state : state -> justification :=
  set_map hash_eq_dec Hash.

Lemma hash_state_injective : forall sigma1 sigma2,
  set_eq (hash_state sigma1) (hash_state sigma2) ->
  set_eq sigma1 sigma2.
Proof.
  intros. apply set_map_injective with hash_eq_dec Hash; try assumption.
  apply hash_injective.
Qed.
