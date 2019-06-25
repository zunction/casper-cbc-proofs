(************************************************************)
(** Consistent Decisions on Properties of Consensus Values  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.protocol_states.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.consensus_values.

Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.state_union.

Require Import Casper.FullStates.common_futures.
Require Import Casper.FullStates.consistent_decisions_prop_protocol_states.

(* Corresponding property of protocol states for a property of consensus values *)
Definition H_lift (p : C -> Prop) : state -> Prop :=
  fun sigma => forall c : C,
                estimator sigma c ->
                p c
  .

(* Decided on properties of consensus values *)
Definition decided_consensus_value (p : C -> Prop) (sigma : state) : Prop := 
  decided_state (H_lift p) sigma.

(* Decisions on properties of consensus values for a finite set of states *)
Definition decisions_consensus_value_states (sigmas : list state) (p : C -> Prop) : Prop :=
  Exists (decided_state (H_lift p)) sigmas.

(* Consistency of decisions on properties of consensus values 
   for a finite set of states *)
Definition consistent_decisions_consensus_value_states (sigmas : list state) : Prop :=
  exists c,
    forall (p : C -> Prop),
      decisions_consensus_value_states sigmas p ->
      p c
  .

(* Consistency of decisions on properties of protocol states lifted from 
   properties on consensus values for a finite set of states *)
Definition consistent_decisions_states_H_lift (sigmas : list state) : Prop :=
  exists sigma',
    forall (q : C -> Prop),
      decisions_states sigmas (H_lift q) ->
      (H_lift q) sigma'
  .

Lemma consistent_decisions_states_H_lift_subset : forall sigmas,
  consistent_decisions_states sigmas ->
  consistent_decisions_states_H_lift sigmas
  .
Proof.
  intros sigmas Hsigmas.
  unfold consistent_decisions_states in Hsigmas.
  destruct Hsigmas as [sigma' [HPsigma' HCsigma']].
  unfold consistent_decisions_states_H_lift.
  exists sigma'.
  intros q H. apply HCsigma'. apply H.
Qed.


Lemma consistent_decisions_states_H_lift_backwards : forall sigmas,
  consistent_decisions_states_H_lift sigmas ->
  consistent_decisions_consensus_value_states sigmas
  .
Proof.
  intros sigmas Hsigmas.
  unfold consistent_decisions_states_H_lift in Hsigmas.
  destruct Hsigmas as [sigma' HCsigma'].
  unfold consistent_decisions_consensus_value_states.
  destruct (estimator_total sigma') as [c Hc].
  exists c.
  intros.
  apply HCsigma'; try assumption.
Qed.

(* n-party consensus safety for properties of consensus values  *)
Theorem n_party_consensus_safety_for_properties_of_the_consensus : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  consistent_decisions_consensus_value_states(sigmas)
  .
Proof.
  intros sigmas Hp Hf.
  destruct (n_party_consensus_safety_for_properties_of_protocol_states _ Hp Hf) as [sigma' [HPsigma' HCsigma']].
  destruct (consistent_decisions_states_H_lift_subset sigmas) as [Hsigma HCHsigma].
    { unfold consistent_decisions_states. exists sigma'. split; try assumption. }
  destruct (consistent_decisions_states_H_lift_backwards sigmas) as [Hsigma' HCHsigma'].
    { unfold consistent_decisions_states_H_lift. exists Hsigma. assumption. }
  unfold consistent_decisions_consensus_value_states.
  exists Hsigma'. assumption.
Qed.

