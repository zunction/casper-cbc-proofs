(************************************************************)
(** Consistent Decisions on Properties of Protocol States  **)
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
Require Import Casper.LightStates.common_futures.

Module Properties_Protocol_States
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        (PHash_function : Hash_function PCons PVal PHash)
        (PEstimator : Estimator PCons PVal PVal_Weights PHash PHash_function)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PHash.
Import PHash_function.
Import PEstimator.
Import PThreshold.

Module PCommon_Futures := Common_Futures PCons PVal PVal_Weights 
                                           PHash PHash_function 
                                           PEstimator PThreshold.

Export PCommon_Futures.


(* Decided properties of protocol states *)
Definition decided_state (p : state -> Prop) (sigma : state) : Prop := forall sigma',
  sigma' in_Futures sigma ->
  p sigma'.

(* Forward consistency *)
Lemma forward_consistency : forall sigma sigma' p,
  sigma' in_Futures sigma ->
  decided_state p sigma ->
  decided_state p sigma'.
Proof.
  unfold decided_state in *. intros sigma sigma' p Hin Hp sigma0' Hsigma0'.
  apply Hp. apply in_Futures_trans with sigma'; assumption.
Qed.

(* Decisions on properties of protocol states for a finite set of states *)
Definition decisions_states (sigmas : list state) (p : state -> Prop) : Prop :=
  Exists (decided_state p) sigmas.

(* Consistency of decisions on properties of protocol states for a finite set of states *)
Definition consistent_decisions_states (sigmas : list state) : Prop :=
  exists sigma',
    protocol_state(sigma') /\
    forall (p : state -> Prop),
      decisions_states sigmas p ->
      p sigma'
  .

(* n-party consensus safety for properties of protocol states  *)
Theorem n_party_consensus_safety_for_properties_of_protocol_states : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  consistent_decisions_states(sigmas)
  .
Proof.
  intros sigmas Hp Hf.
  destruct (n_party_common_futures _ Hp Hf) as [sigma' [Hps' HinFutures]].
  exists sigma'.
  split; try assumption.
  intros p HPp.
  apply Exists_exists in HPp.
  destruct HPp as [sigma0 [Hin Hdecided]].
  apply Hdecided.
  rewrite Forall_forall in HinFutures.
  apply HinFutures.
  assumption.
Qed.

End Properties_Protocol_States.