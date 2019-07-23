Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

Require Import Casper.preamble.
Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.threshold.


(*********************)
(** Protocol states **)
(*********************)

Module Protocol_States
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PEstimator : Estimator PCons PVal PVal_Weights)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PThreshold.
Import PEstimator.

Module PThreshold_Properties := Threshold_Properties PCons PVal PVal_Weights PEstimator PThreshold.
Export PThreshold_Properties.


(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    syntactic_state_inclusion sigma1 sigma2.

(** The valid message condition **)
Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= t)%R.

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition (next msg Empty).
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_message_state. simpl.
  unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. apply threshold_nonnegative.
Qed.

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
      protocol_state sigma -> 
      protocol_state sigma' ->
      full_node_condition sigma sigma' ->
      valid_estimate_condition c sigma ->
      fault_tolerance_condition (add_in_sorted_fn (c, v, sigma) sigma') ->
      protocol_state (add_in_sorted_fn (c, v, sigma) sigma')
  .


Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition sigma.
Proof.
  intros.
  inversion H.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    simpl. apply Rge_le. apply threshold_nonnegative.
  - assumption.
Qed.

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

Lemma protocol_state_singleton : forall c v,
  valid_estimate_condition c Empty ->
  protocol_state (next (c, v, Empty) Empty).
Proof.
  intros.
  assert (Heq : add_in_sorted_fn (c, v, Empty) Empty = (next (c, v, Empty) Empty))
  ; try reflexivity.
  rewrite <- Heq.
  apply protocol_state_next; try assumption; try apply protocol_state_empty.
  - apply incl_refl. 
  - simpl. rewrite add_is_next. apply fault_tolerance_condition_singleton.
Qed.

Definition estimator_functional : Prop :=
  forall sigma c1 c2, estimator sigma c1 -> estimator sigma c2 -> c1 = c2.

Lemma protocol_state_empty_justification : forall sigma,
  protocol_state sigma ->
  sigma = Empty \/ exists msg, in_state msg sigma /\ justification msg = Empty.
Proof.
  intros. induction H; try (left; reflexivity). right.
  destruct sigma.
  - exists (c, v, Empty). split; try reflexivity.
    apply in_state_add_in_sorted_iff. left. reflexivity.
  - destruct IHprotocol_state2.
    + subst. exfalso. apply (in_empty_state (c0, v0, sigma1)). apply H1. 
      simpl. left. reflexivity.
    + destruct H4 as [msg [Hin Hj]].
      exists msg. split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.

Lemma extend_protocol_state : forall sigma,
  protocol_state sigma ->
  forall c,
  valid_estimate_condition c sigma ->
  forall v,
  protocol_state (add_in_sorted_fn (c, v, sigma) sigma).
Proof.
  intros sigma Hps c Hc v.
  constructor; try assumption; try apply incl_refl.
  unfold fault_tolerance_condition.
  apply fault_tolerance_condition_subset with (add (c,v,sigma) to sigma).
  - unfold syntactic_state_inclusion. apply set_eq_add_in_sorted.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    rewrite equivocating_senders_extend.
    apply protocol_state_fault_tolerance in Hps. assumption.
Qed.

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

(** Proof obligations from CBC_protocol **)
Definition prot_state : Type :=
  { s : state | protocol_state s}. 

Definition prot_state_proj1 (s : prot_state) := proj1_sig s. 
Coercion prot_state_proj1 : prot_state >-> state.

Definition reach := syntactic_state_inclusion. 

Lemma reach_trans :
  forall (s1 s2 s3 : prot_state), reach s1 s2 -> reach s2 s3 -> reach s1 s3. 
Proof.
  intros s1 s2 s3 H_12 H_23. 
  intros x H_in.
  spec H_12 x H_in.
  spec H_23 x H_12.
  assumption.
Qed.

Lemma reach_union :
  forall (s1 s2 : prot_state), reach s1 (state_union s1 s2).
Proof.   
  intros s1 s2. unfold state_union. 
  intros x H_in.
  assert (H_incl := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_incl as [_ useful]. 
  spec useful x. spec useful.
  apply in_app_iff. tauto.
  assumption.
Qed. 

Lemma reach_morphism :
  forall s1 s2 s3, reach s1 s2 -> s2 = s3 -> reach s1 s3. 
Proof. 
  intros; subst; assumption. 
Qed.

(** After cycling to fault_weights for a bit, **)

Lemma about_prot_state :
  forall (s1 s2 : sorted_state),
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= t)%R ->
    protocol_state (state_union s1 s2). 
Proof. 
  intros s1 s2 H_s1 H_s2 H_weight. 
  unfold state_union.
  inversion H_s1. subst.
  simpl. rewrite list_to_state_sorted; try assumption.
  destruct s2; simpl in *; assumption.
  remember (messages_union (get_messages s1) (get_messages s2)) as lm. 
  induction (get_messages s1) as [|hd tl IHlm].
  - simpl. simpl in Heqlm. rewrite Heqlm.
    admit.
  - apply protocol_state_empty.
  - simpl. destruct hd. destruct p.
    apply protocol_state_next. apply protocol_state_singleton. (msplit. 
End Protocol_States.
