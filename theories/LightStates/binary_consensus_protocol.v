(*******************************)
(** Binary consensus protocol **)
(*******************************)

Require Import Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.estimator.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.hash_function.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.states.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.hash_state.
Require Import Casper.LightStates.consistent_decisions_prop_consensus_values.

(** The Friendly Binary Consensus Protocol **)

(** The Friendly Binary Consensus Protocol - Consensus Values **)

Module BinaryCV <: Consensus_Values.

Inductive binC : Set := 
  | zero : binC 
  | one : binC
  .

Definition C := binC.

Lemma c_non_empty : exists c : C, True.
Proof.
  exists one. reflexivity.
Qed.

Lemma c_eq_dec : forall (c1 c2 : C), {c1 = c2} + {c1 <> c2}.
Proof.
  intros.
  destruct c1
; destruct c2
; try (left; reflexivity)
; try (right; unfold not; intros; inversion H)
  .
Qed.

End BinaryCV.


(** The Friendly Binary Consensus Protocol - Estimator **)

Module BinaryEstimator 
        (PVal : Validators) 
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        (PHash_function : Hash_function BinaryCV PVal PHash)
        <: Estimator BinaryCV PVal PVal_Weights PHash PHash_function.

Import BinaryCV.
Import PVal.
Import PVal_Weights.
Import PHash.
Import PHash_function.

Module PStates := States BinaryCV PVal PHash PHash_function.
Export PStates.

Definition score (c:C) (sigma:state) : R :=
  fold_right Rplus R0
  (map weight (validators_latest_estimates c sigma))
  .

Inductive binEstimator : state -> C -> Prop :=
  | estimator_one : forall sigma,
        ((score zero sigma) < (score one sigma))%R ->
        binEstimator sigma one
  | estimator_zero : forall sigma,
        ((score zero sigma) > (score one sigma))%R ->
        binEstimator sigma zero
  | estimator_both_zero : forall sigma,
        ((score zero sigma) = (score one sigma))%R ->
        binEstimator sigma zero
  | estimator_both_one : forall sigma,
        ((score zero sigma) = (score one sigma))%R ->
        binEstimator sigma one
  .

Definition estimator := binEstimator.

Lemma estimator_total : forall s : state, exists c : C, estimator s c.
Proof.
  intros sigma.
  destruct (total_order_T (score zero sigma) (score one sigma)) as [[HLT | HEQ] | HGT].
  - exists one. apply estimator_one. assumption.
  - exists one. apply estimator_both_one. assumption.
  - exists zero. apply estimator_zero. assumption.
Qed.

End BinaryEstimator.


(** The Friendly Binary Consensus Protocol - 
    Non-triviality of Decisions on Properties of Consensus Values **)

Module Non_triviality_Properties_Consensus_Values
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        (PHash_function : Hash_function BinaryCV PVal PHash)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PVal.
Import PVal_Weights.
Import PHash.
Import PHash_function.
Import PThreshold.

Import BinaryCV.

Module PBinaryEstimator := BinaryEstimator PVal PVal_Weights PHash PHash_function.
Import PBinaryEstimator.

Module PProperties_Consensus_Values := Properties_Consensus_Values BinaryCV PVal PVal_Weights PHash PHash_function PBinaryEstimator PThreshold.
Export PProperties_Consensus_Values.

Definition non_trivial_consensus_value (p : C -> Prop) :=
  (exists sigma1, protocol_state sigma1 /\ decided_consensus_value p sigma1)
  /\
  (exists sigma2, protocol_state sigma2 /\ decided_consensus_value (predicate_not p) sigma2).

Theorem non_triviality_decisions_on_properties_of_consensus_values :
  exists p, non_trivial_consensus_value p.
Admitted.
End Non_triviality_Properties_Consensus_Values.






























  