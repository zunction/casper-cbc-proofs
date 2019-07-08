Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.threshold.
Require Import Casper.FullStates.consistent_decisions_prop_protocol_states.


Module Non_triviality_Properties_Protocol_States
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

Module PProperties_Protocol_States := Properties_Protocol_States PCons PVal PVal_Weights PEstimator PThreshold.
Export PProperties_Protocol_States.

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= t)%R /\
      (sum_weights vs > t - weight v)%R
      .

Definition at_least_two_validators : Prop :=
  forall v1 : V, exists v2 : V, v1 <> v2.

Lemma exists_pivotal_message : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists v.
  subst. exists (set_remove v_eq_dec v vs). repeat split.
  - apply set_remove_nodup. assumption.
  - intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
  - assumption.
  - rewrite (sum_weights_in v) in Hgt; try assumption.
    rewrite Rplus_comm in Hgt.
    apply (Rplus_gt_compat_r (- weight v)%R) in Hgt.
    rewrite Rplus_assoc in Hgt.
    rewrite Rplus_opp_r in Hgt.
    rewrite Rplus_0_r in Hgt.
    assumption.
Qed.

Definition valid_protocol_state (sigma : state) (csigma cempty : C) (vs : list V) : state :=
  fold_right
    (fun v sigma' =>
      add_in_sorted_fn (csigma, v, sigma) (add_in_sorted_fn (cempty, v, Empty) sigma'))
    sigma
    vs.


Lemma in_valid_protocol_state : forall msg sigma csigma cempty vs,
  in_state msg (valid_protocol_state sigma csigma cempty vs) ->
  in_state msg sigma \/
  exists v, In v vs /\ (msg = (csigma, v, sigma) \/ (msg = (cempty, v, Empty))).
Proof.
  intros. induction vs.
  - simpl in H. left. assumption.
  - simpl in H. rewrite in_state_add_in_sorted_iff in H. rewrite in_state_add_in_sorted_iff in H.
    destruct H as [Heq | [Heq | Hin]];
    try (right; exists a; split; try (left; reflexivity); (left; assumption) || (right; assumption)).
    apply IHvs in Hin. destruct Hin; try (left; assumption). right.
    destruct H as [v [Hin H]].
    exists v. split; try assumption. right; assumption.
Qed.

Lemma in_valid_protocol_state_rev_sigma : forall sigma csigma cempty vs,
  syntactic_state_inclusion sigma (valid_protocol_state sigma csigma cempty vs).
Proof.
  intros. intros msg Hin.
  induction vs.
  - assumption.
  - simpl. apply in_state_add_in_sorted_iff. right.
    apply in_state_add_in_sorted_iff. right.
    assumption.
Qed.

Lemma in_valid_protocol_state_rev_csigma : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (csigma, v, sigma) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Lemma in_valid_protocol_state_rev_cempty : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (cempty, v, Empty) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. right.
       apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  at_least_two_validators ->
  exists p, non_trivial p.
Proof.
  intro H2v.
  destruct exists_pivotal_message as [v Hpivotal].
  destruct (estimator_total Empty) as [c Hc].
  destruct Hpivotal as [vs [Hnodup [Hnin [Hlt Hgt]]]].
  destruct vs as [ | v' vs].
  - exists (in_state (c,v,Empty)).
    split.
    + exists (next (c,v,Empty) Empty); split; try apply protocol_state_singleton; try assumption.
      intros sigma H. destruct H as [HLS1 [HLS2 H]]. apply H. simpl. left. reflexivity.
    + destruct (H2v v) as [v' Hv'].
      remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0).
      { subst. apply protocol_state_singleton. assumption. }
      destruct (estimator_total sigma0) as [c0 Hc0].
      exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      intro.
      apply protocol_state_fault_tolerance in Hps' as Hft'.
      unfold fault_tolerance_condition in Hft'.
      assert (Hnft' : (fault_weight_state sigma' > t)%R).
      { apply Rlt_le_trans with (fault_weight_state (add (c, v, Empty) to (add (c0, v, sigma0) to Empty))).
        - unfold fault_weight_state. unfold equivocating_senders. simpl.
          assert ( Hequiv : equivocating_message_state (c, v, Empty)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c0, v, sigma0). 
            split.
            - right. left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv.
          assert ( Hequiv0 : equivocating_message_state (c0, v, sigma0)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c, v, Empty). 
            split.
            - left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv0. simpl. rewrite eq_dec_if_true; try reflexivity.
          simpl. simpl in Hgt. unfold Rminus in Hgt.
          apply (Rplus_gt_compat_r (weight v)) in Hgt. rewrite Rplus_assoc in Hgt.
          rewrite Rplus_0_r. rewrite Rplus_0_l in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt.
          apply Rgt_lt. assumption.
        - apply fault_weight_state_incl. unfold syntactic_state_inclusion. simpl.
          intros x Hin. destruct Hin as [Hin | [Hin | Hcontra]]; try inversion Hcontra; subst
          ; try assumption.
          apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
      }
      unfold Rgt in Hnft'. apply (Rlt_irrefl t).
      apply Rlt_le_trans with (fault_weight_state sigma'); assumption.
  - remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
    assert (Hps0 : protocol_state sigma0).
    { subst. apply protocol_state_singleton. assumption. }
    destruct (estimator_total sigma0) as [c0 Hc0].
    exists (in_state (c0,v,sigma0)).
    split.
    + exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + remember (add_in_sorted_fn (c, v, Empty) Empty) as sigma.
      simpl in Heqsigma. rewrite add_is_next in Heqsigma.
      destruct (estimator_total sigma) as [csigma Hcsigma].
      remember (valid_protocol_state sigma csigma c (v' :: vs)) as sigma2.
      assert (Hequiv2 : set_eq (equivocating_senders sigma2) (v' :: vs)). 
      { unfold equivocating_senders. split; intros; intros x Hin.
        - apply (set_map_exists v_eq_dec sender)  in Hin.
          destruct Hin as [[(cx, vx) jx] [Hin Hsend]].
          simpl in Hsend. rewrite <- Hsend.
          apply filter_In in Hin. destruct Hin as [Hin Hequiv].
          apply existsb_exists in Hequiv.
          destruct Hequiv as [[(cy, vy) jy] [Hiny Hequiv]].
          rewrite Heqsigma2 in Hin.
          apply in_valid_protocol_state in Hin.
          destruct Hin as [Hin | [vv [Hin [Heq | Heq]]]]; try (inversion Heq; subst; assumption).
          exfalso. unfold equivocating_messages in Hequiv.
          rewrite Heqsigma in Hin. apply in_singleton_state in Hin.
          rewrite Heqsigma2 in Hiny.
          apply in_valid_protocol_state in Hiny.
          destruct Hiny as [Hiny | [vv [Hiny [Heq | Heq]]]].
          + rewrite Heqsigma in Hiny. apply in_singleton_state in Hiny.
            rewrite Hin in Hequiv. rewrite Hiny in Hequiv.
            rewrite eq_dec_if_true in Hequiv; try reflexivity.
            inversion Hequiv.
          + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
            rewrite eq_dec_if_false in Hequiv.
            * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
              intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
              apply Hnin. assumption.
            * intro. inversion H; subst; clear H. apply Hnin. assumption.
          + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
            rewrite eq_dec_if_false in Hequiv.
            * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
              intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
              apply Hnin. assumption.
            * intro. inversion H; subst; clear H. apply Hnin. assumption.
      - apply (set_map_exists v_eq_dec sender).
        exists (c, x, Empty). simpl. split; try reflexivity.
        apply filter_In. split.
        + rewrite Heqsigma2. apply in_valid_protocol_state_rev_cempty. assumption.
        + apply existsb_exists. exists (csigma, x, sigma). split.
          * rewrite Heqsigma2. apply in_valid_protocol_state_rev_csigma. assumption.
          * unfold equivocating_messages.
            { rewrite eq_dec_if_false.
              - rewrite eq_dec_if_true; try reflexivity. apply andb_true_iff. split.
                + apply negb_true_iff. unfold in_state_fn. 
                  rewrite in_state_dec_if_false; try reflexivity.
                  rewrite Heqsigma. intro. apply in_singleton_state in H.
                  apply Hnin. inversion H; subst; clear H. assumption.
                + apply negb_true_iff. unfold in_state_fn. 
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
              - intro. inversion H; subst. inversion H2.
            }
      }
  Admitted.

End Non_triviality_Properties_Protocol_States.