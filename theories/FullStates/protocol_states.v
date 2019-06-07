Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)


(** Parameters of the protocol **)

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.threshold.


(** Messages and States **)

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.


(***************)
(** Estimator **)
(***************)

Parameter estimator : state -> C -> Prop.

Parameter estimator_total : forall s : state, exists c : C, estimator s c.

(** State membership **)
Require Import Casper.FullStates.in_state.

(** Canonical representation of states **)

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.


(*******************************)
(** Protocol state conditions **) 
(*******************************)


Require Import Casper.FullStates.fault_weights.


(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    syntactic_state_inclusion sigma1 sigma2.

(** The valid message condition **)
Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.


(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= t)%R.


Lemma fault_tolerance_condition_subset : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

(** Protocol states **)
Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall c v sigma sigma',
      protocol_state sigma -> (* 1 *)
      protocol_state sigma' ->
      syntactic_state_inclusion sigma sigma' ->
      valid_estimate_condition c sigma ->
      fault_tolerance_condition (add_in_sorted_fn (c, v, sigma) sigma') ->
      protocol_state (add_in_sorted_fn (c, v, sigma) sigma')
  .

Lemma protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, sigma) sigma'); try assumption.
    apply locally_sorted_message_justification. assumption.
Qed.

(* 
Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup (get_messages sigma).
Proof.
  intros.
  apply locally_sorted_nodup.
  apply protocol_state_sorted.
  assumption.
Qed.
 *)

Lemma protocol_state_singleton : forall v,
  exists msg, validator msg = v /\ protocol_state (next msg Empty).
Proof.
  Admitted.


Definition Reachable sigma1 sigma2 :=
  protocol_state sigma1 /\ protocol_state sigma2 /\ syntactic_state_inclusion sigma1 sigma2.

Notation "sigma2 'in_Futures' sigma1" :=
  (Reachable sigma1 sigma2)
  (at level 20).

Lemma in_Futures_trans : forall sigma1 sigma2 sigma3,
  sigma1 in_Futures sigma2 ->
  sigma2 in_Futures sigma3 ->
  sigma1 in_Futures sigma3.
Proof.
  intros. destruct H as [Hps2 [Hps1 Hincl21]]. destruct H0 as [Hps3 [_ Hincl32]].
  repeat (split; try assumption). apply incl_tran with (get_messages sigma2); assumption.
Qed.
