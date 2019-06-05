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


(** Canonical representation of states **)

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.


(** State equality **)
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.sort.
Require Import Casper.FullStates.state_eq.
Require Import Casper.FullStates.state_inclusion.
Require Import Casper.FullStates.sorted_subset.


Theorem inclusion_state_eq : forall sigma1 sigma2,
  state_inclusion sigma1 sigma2 ->
  state_inclusion sigma2 sigma1 ->
  state_eq sigma1 sigma2.
Proof.
  intros.
  destruct (sort_total sigma1) as [sigma1s Hsort1].
  destruct (sort_total sigma2) as [sigma2s Hsort2].
  apply sort_is_sorted in Hsort1 as Hsigma1s.
  apply sort_is_sorted in Hsort2 as Hsigma2s.
  apply sort_state_eq in Hsort1.
  apply sort_state_eq in Hsort2.
  apply state_eq_inclusion in Hsort1 as Hinsigma1s.
  apply state_eq_symmetric in Hsort1.
  apply state_eq_inclusion in Hsort1 as Hinsigma1s'.

  apply state_eq_inclusion in Hsort2 as Hinsigma2s.
  apply state_eq_symmetric in Hsort2.
  apply state_eq_inclusion in Hsort2 as Hinsigma2s'.

  apply (state_inclusion_transitive _ _ _ H) in Hinsigma2s.
  apply (state_inclusion_transitive _ _ _ Hinsigma1s') in Hinsigma2s.
  apply (state_inclusion_transitive _ _ _ H0) in Hinsigma1s.
  apply (state_inclusion_transitive _ _ _ Hinsigma2s') in Hinsigma1s.
  clear H. clear H0. clear Hinsigma1s'. clear Hinsigma2s'.
  
  apply sorted_subset_inclusion in Hinsigma1s; try assumption.
  apply sorted_subset_inclusion in Hinsigma2s; try assumption.

  apply sorted_subset_syntactic_inclusion in Hinsigma1s.
  apply sorted_subset_syntactic_inclusion in Hinsigma2s.

  apply sorted_syntactic_state_inclusion_equality_predicate in Hinsigma2s
  ; try assumption.
  subst.
  apply state_eq_symmetric in Hsort1.
  apply (state_eq_transitive _ _ _ Hsort1 Hsort2).
Qed.

(*******************************)
(** Protocol state conditions **) 
(*******************************)


Require Import Casper.FullStates.fault_weights.


(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    sorted_subset sigma1 sigma2.

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


(* 
Lemma fault_tolerance_condition_backwards : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  destruct (fault_weight_state_total sigma') as [r' H4].
  assert (LTw := fault_weight_state_add msg sigma sigma' r r' H H0 H1 H3 H4).
  apply H2 in H4.
  apply (Rle_trans _ _ _ LTw H4).
Qed.

Lemma fault_tolerance_condition_backwards_subset : forall sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  sorted_subset sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition in *.
  intros.
  destruct (fault_weight_state_total sigma') as [r' H4].
  apply (fault_weight_state_sorted_subset _ _ _ _ H1 H3) in H4 as H5.
  apply H2 in H4.
  apply (Rle_trans _ _ _ H5 H4).
Qed. *)

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

Theorem protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, sigma) sigma'); try assumption.
    + apply locally_sorted_message_justification. assumption.
    + apply add_in_sorted_function. reflexivity.
Qed.

Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup (get_messages sigma).
Proof.
  intros.
  apply locally_sorted_nodup.
  apply protocol_state_sorted.
  assumption.
Qed.

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
