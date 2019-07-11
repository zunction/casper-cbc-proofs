(************************************************************)
(** Consistent Decisions on Properties of Consensus Values  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.estimator.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.hash_function.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.hash_state.
Require Import Casper.LightStates.consistent_decisions_prop_protocol_states.

Module Properties_Consensus_Values
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        (PHash_function : Hash_function PCons PVal PHash)
        (PEstimator : Estimator PCons PVal PVal_Weights PHash)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PHash.
Import PHash_function.
Import PEstimator.
Import PThreshold.

Module PProperties_Protocol_States := Properties_Protocol_States PCons PVal PVal_Weights 
                                           PHash PHash_function 
                                           PEstimator PThreshold.

Export PProperties_Protocol_States.

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
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
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

End Properties_Consensus_Values.