(************************************************************)
(** Consistent Decisions on Properties of Protocol States  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.protocol_states.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.

Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.state_union.

Require Import Casper.FullStates.common_futures.


(* Decided properties of protocol states *)

Definition decided (q : state -> Prop) (sigma : state) : Prop := forall sigma',
  sigma' in_Futures sigma ->
  q sigma'.

(* Forward consistency *)
Lemma forward_consistency : forall sigma sigma' q,
  sigma' in_Futures sigma ->
  decided q sigma ->
  decided q sigma'.
Proof.
  unfold decided in *. intros.
  apply H0. apply in_Futures_trans with sigma'; assumption.
Qed.


(* TODO: Maybe introduce Consistent back; what about finiteness.
   NOTE: the Consistent predicate is unrolled.
 *)


(* n-party consensus safety for properties of protocol states  *)
Theorem n_party_consensus_safety_for_properties_of_protocol_states : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  exists sigma',
    protocol_state(sigma') /\
    forall (q : state -> Prop),
      Exists (decided q) sigmas ->
      q sigma'
  .
Proof.
  intros.
  destruct (n_party_common_futures _ H H0) as [sigma' [Hps' HinFutures]].
  exists sigma'.
  split; try assumption.
  intros.
  apply Exists_exists in H1.
  destruct H1 as [sigma0 [Hin Hdecided]].
  apply Hdecided.
  rewrite Forall_forall in HinFutures.
  apply HinFutures.
  assumption.
Qed.
