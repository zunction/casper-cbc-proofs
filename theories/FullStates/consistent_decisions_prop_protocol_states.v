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

Definition decided_state (q : state -> Prop) (sigma : state) : Prop := forall sigma',
  sigma' in_Futures sigma ->
  q sigma'.

(* Forward consistency *)
Lemma forward_consistency : forall sigma sigma' q,
  sigma' in_Futures sigma ->
  decided_state q sigma ->
  decided_state q sigma'.
Proof.
  unfold decided_state in *. intros.
  apply H0. apply in_Futures_trans with sigma'; assumption.
Qed.


(* TODO: Maybe introduce Consistent back; what about finiteness.
   NOTE: the Consistent predicate is unrolled.
 *)

(* Decisions on properties of protocol states for a state *)
Definition decisions_state (sigma : state) (p : state -> Prop) : Prop :=
  decided_state p sigma.

(* Decisions on properties of protocol states for a finite union of states *)
Definition decisions_states (sigmas : list state) (p : state -> Prop) : Prop :=
  Exists (decided_state p) sigmas.

(* Consistency of decisions on properties of protocol states for a state *)
Definition consistent_decisions_state (sigma : state) : Prop :=
  exists sigma',
    protocol_state(sigma') /\
    forall (p : state -> Prop),
      decisions_state sigma p ->
      p sigma'
  .

(* Consistency of decisions on properties of protocol states for a finite union of states *)
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
