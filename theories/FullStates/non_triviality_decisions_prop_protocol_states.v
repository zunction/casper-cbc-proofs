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
        (PThreshold : Threshold PVal PVal_Weights)
        (PEstimator : Estimator PCons PVal)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PThreshold.
Import PEstimator.

Module PProperties_Protocol_States := Properties_Protocol_States PCons PVal PVal_Weights PThreshold PEstimator.
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

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  at_least_two_validators ->
  exists p, non_trivial p.
Proof.
  intro H2v.
  destruct exists_pivotal_message as [v Hpivotal].
  destruct (estimator_total Empty) as [c Hc].
  exists (in_state (c,v,Empty)).
  split.
  - exists (next (c,v,Empty) Empty); split; try apply protocol_state_singleton; try assumption.
    intros sigma H. destruct H as [HLS1 [HLS2 H]]. apply H. simpl. left. reflexivity.
  - destruct Hpivotal as [vs [Hnodup [Hnin [Hlt Hgt]]]].
    destruct vs.
    + destruct (H2v v) as [v' Hv'].
      remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0).
      { subst. apply protocol_state_singleton. assumption. }
      destruct (estimator_total sigma0) as [c0 Hc0].
      exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      intro.
  Admitted.

End Non_triviality_Properties_Protocol_States.