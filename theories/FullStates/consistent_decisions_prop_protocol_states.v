(************************************************************)
(** Consistent Decisions on Properties of Protocol States  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.list_to_state.
Require Import Casper.FullStates.threshold.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.protocol_states.
Require Import Casper.FullStates.state_union.
Require Import Casper.FullStates.common_futures.


Module Type Properties_Protocol_States
              (PCons : Consensus_Values) 
              (PVal : Validators)
              (PStates : States PCons PVal)
              (PMessages : Messages PCons PVal PStates)
              (PIn_State : In_State PCons PVal PStates PMessages)
              (PLocally_Sorted : Locally_Sorted PCons PVal PStates PMessages PIn_State)
              (PAdd_In_Sorted : Add_In_Sorted PCons PVal PStates PMessages PIn_State PLocally_Sorted) 
              (PLists_To_State : List_To_State PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted)
              (PFault_Weights : Fault_Weights PCons PVal PStates PMessages PIn_State PLocally_Sorted)
              (PThreshold : Threshold PCons PVal PStates PMessages PIn_State PLocally_Sorted PFault_Weights)
              (PProtocol_States : Protocol_States PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted PLists_To_State PFault_Weights PThreshold)
              (PState_Union : State_Union PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted PLists_To_State)
              (PCommon_Futures : Common_Futures PCons PVal PStates PMessages PIn_State PLocally_Sorted PAdd_In_Sorted PLists_To_State PFault_Weights PThreshold PProtocol_States PState_Union)
              .

(* import the Module parameters in order to have access to 
   its parameters without having to use the DotNotation. *)
Import PCons.
Import PVal.
Import PStates.
Import PMessages.
Import PIn_State.
Import PLocally_Sorted.
Import PAdd_In_Sorted.
Import PLists_To_State.
Import PFault_Weights.
Import PThreshold.
Import PProtocol_States.
Import PState_Union.
Import PCommon_Futures.

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
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
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

Definition non_trivial (p : state -> Prop) :=
  (exists sigma1, protocol_state sigma1 /\ decided_state p sigma1)
  /\
  (exists sigma2, protocol_state sigma2 /\ decided_state (predicate_not p) sigma2).

End Properties_Protocol_States.