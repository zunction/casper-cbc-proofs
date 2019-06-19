(************************************************************)
(** Consistent Decisions on Properties of Consensus Values  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.states.
Require Import Casper.LightStates.messages.

Require Import Casper.LightStates.common_futures.
Require Import Casper.LightStates.consistent_decisions_prop_protocol_states.


(* Corresponding property of protocol states for a property of consensus values *)
Definition H (p : C -> Prop) : state -> Prop :=
  fun sigma => forall c : C,
                estimator sigma c ->
                p c
  .

(* Decided on properties of consensus values *)
Definition decided_consensus_value (p : C -> Prop) (sigma : state) : Prop := 
  decided_state (H p) sigma.

(* Decisions on properties of consensus values for a state *)
Definition decisions_consensus_value_state (sigma : state) (p : C -> Prop) : Prop :=
  decided_state (H p) sigma.

(* Decisions on properties of consensus values for a finite set of states *)
Definition decisions_consensus_value_states (sigmas : list state) (p : C -> Prop) : Prop :=
  Exists (decided_state (H p)) sigmas.

(* Consistency of decisions on properties of consensus values for a state *)
Definition consistent_decisions_value_state (sigma : state) : Prop :=
  exists c,
    forall (p : C -> Prop),
      decisions_consensus_value_state sigma p ->
      p c
  .

(* Consistency of decisions on properties of consensus values for a finite set of states *)

Definition consistent_decisions_consensus_states (sigmas : list state) : Prop :=
  exists c,
    forall (p : C -> Prop),
      decisions_consensus_value_states sigmas p ->
      p c
  .

Definition consistent_decisions_states_H (sigmas : list state) : Prop :=
  exists sigma',
    forall (q : C -> Prop),
      decisions_states sigmas (H q) ->
      (H q) sigma'
  .

Lemma consistent_decisions_states_H_subset : forall sigmas,
  consistent_decisions_states sigmas ->
  consistent_decisions_states_H sigmas
  .
Proof.
  intros.
  unfold consistent_decisions_states in H0.
  destruct H0 as [sigma' [HPsigma' HCsigma']].
  unfold consistent_decisions_states_H.
  exists sigma'.
  intros. apply HCsigma'. apply H0.
Qed.


Lemma consistent_decisions_states_H_backwards : forall sigmas,
  consistent_decisions_states_H sigmas ->
  consistent_decisions_consensus_states sigmas
  .
Proof.
  intros.
  unfold consistent_decisions_states_H in H0.
  destruct H0 as [sigma' HCsigma'].
  unfold consistent_decisions_consensus_states.
  destruct (estimator_total sigma') as [c Hc].
  exists c.
  intros.
  apply HCsigma'; try assumption.
Qed.

(* n-party consensus safety for properties of consensus values  *)
Theorem n_party_consensus_safety_for_properties_of_the_consensus : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  consistent_decisions_consensus_states(sigmas)
  .
Proof.
  intros.
  destruct (n_party_consensus_safety_for_properties_of_protocol_states _ H0 H1) as [sigma' [HPsigma' HCsigma']].
  destruct (consistent_decisions_states_H_subset sigmas) as [Hsigma HCHsigma].
    { unfold consistent_decisions_states. exists sigma'. split; try assumption. }
  destruct (consistent_decisions_states_H_backwards sigmas) as [Hsigma' HCHsigma'].
    { unfold consistent_decisions_states_H. exists Hsigma. assumption. }
  unfold consistent_decisions_consensus_states.
  exists Hsigma'. assumption.
Qed.

