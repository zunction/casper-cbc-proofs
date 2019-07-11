Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.hash_function.
Require Import Casper.LightStates.states.

Module Hash_States 
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PHash : Hash)
        (PHash_function : Hash_function PCons PVal PHash)
        .

Import PCons.
Import PVal.
Import PHash.
Import PHash_function.

Module PStates := States PCons PVal PHash.
Import PStates.

Definition hash_state (sigma : state) : justification_type :=
  justification_add_all (map Hash sigma).

Lemma hash_state_sorted : forall sigma,
  LocallySorted hash_lt (hash_state sigma).
Proof.
  intros.
  apply justification_sorted.
Qed.

Lemma hash_state_injective : forall sigma1 sigma2,
  hash_state sigma1 = hash_state sigma2 ->
  set_eq sigma1 sigma2.
Proof.
  intros. apply justification_add_all_injective in H.
  destruct H as [H12 H21].
  split; intros x Hin
  ; apply (in_map Hash) in Hin
  ; apply H12 in Hin || apply H21 in Hin
  ; apply in_map_iff in Hin
  ; destruct Hin as [x' [Heq Hin]]
  ; apply hash_injective in Heq
  ; subst; assumption
  .
Qed.

End Hash_States.
