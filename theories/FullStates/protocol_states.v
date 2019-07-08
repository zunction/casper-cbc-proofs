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

Lemma protocol_state_unequivocating :
  estimator_functional ->
  forall sigma,
  protocol_state sigma ->
  forall v,
  set_map v_eq_dec sender (get_messages sigma) = [v] ->
  forall msg1 msg2,
  in_state msg1 sigma ->
  in_state msg2 sigma ->
  in_state msg1 (justification msg2) \/ in_state msg2 (justification msg1).
Proof.
(*  intros EF sigma PS.
  induction PS; intros; subst.
  - inversion H1.
  - apply protocol_state_empty_justification in H.
    apply protocol_state_empty_justification in H0.
    destruct H0.
    + subst.
      inversion H6 as [Heq | Hcontra]; try inversion Hcontra; subst; clear H6.
      inversion H7 as [Heq | Hcontra]; try inversion Hcontra; subst; clear H7.
      unfold equivocating_messages. rewrite eq_dec_if_true; reflexivity.
    + destruct H0 as [[(c', v') j'] [Hin Hj]]. simpl in Hj. subst.
      assert (set_eq  (get_messages (add_in_sorted_fn (c, v, sigma0) sigma'))
                    ((c, v, sigma0) :: get_messages sigma')); try apply set_eq_add_in_sorted.
      apply (set_map_eq v_eq_dec sender) in H0. rewrite H5 in H0.
      apply set_eq_comm in H0. simpl in H0. destruct H0 as [Hincl _].
      destruct (Hincl v) as [Heq | Hcontra]; try inversion Hcontra
      ; try (apply set_add_intro2; reflexivity).
      subst.
      destruct (Hincl v') as [Heq | Hcontra]; try inversion Hcontra
      ; try (
        apply set_add_intro1
        ; apply set_map_exists
        ; exists (c', v', Empty); split; try reflexivity; assumption).
      subst.
     simpl in H5. destruct H5 as [_ Hincl]. 
    assert (In v (set_add v_eq_dec v (set_map v_eq_dec validator (get_messages sigma'))));
    try (apply set_add_intro2; reflexivity).
    apply Hincl in H5. destruct H5 as [Heq | Hfalse]; try inversion Hfalse; subst.
    assert (sigma' = Empty \/ (set_map v_eq_dec validator (get_messages sigma')) = [v]).
    { inversion PS2; try (left; reflexivity). right.
    assert (Hnodup : NoDup (set_map v_eq_dec validator (get_messages (add_in_sorted_fn (c0, v0, sigma0) sigma'0))))
    ; try apply set_map_nodup.
    apply (set_eq_singleton v_eq_dec); try assumption.
    subst. split; intros v' Inv'.
    - apply Hincl. apply set_add_iff. right. assumption.
    - destruct Inv' as [Heq | Hcontra]; try inversion Hcontra; subst.
      apply (set_eq_singleton_rev v_eq_dec) in H2; try apply set_map_nodup.
      destruct (set_eq_add_in_sorted (c0, v0, sigma0)  sigma'0) as [_ HH].
      destruct (incl_singleton _ v' Hincl v0)
      ; try (apply set_add_iff; right)
      ; apply (set_map_exists v_eq_dec validator)
      ; exists (c0, v0, sigma0); split; try reflexivity
      ; apply (HH (c0, v0, sigma0))
      ; left; reflexivity
      .
    }
    destruct H5 as [Heq | Hind]; subst.
    + unfold in_state in H4. simpl in H4.
      unfold in_state in H3. simpl in H3.
      destruct H3 as [Heq | Hcontra]; try inversion Hcontra; subst.
      destruct H4 as [Heq | Hcontra]; try inversion Hcontra; subst.
      unfold equivocating_messages. rewrite eq_dec_if_true; reflexivity.
     apply in_state_add_in_sorted_iff in H6.
       apply in_state_add_in_sorted_iff in H7.
      destruct H3; destruct H4; subst.
      * unfold equivocating_messages. rewrite eq_dec_if_true; reflexivity.
 *)Admitted.

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

End Protocol_States.