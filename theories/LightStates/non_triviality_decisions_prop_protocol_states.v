Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.consistent_decisions_prop_protocol_states.

Definition non_trivial (p : state -> Prop) :=
  (exists sigma1, protocol_state sigma1 /\ decided p sigma1)
  /\
  (exists sigma2, protocol_state sigma2 /\ decided (predicate_not p) sigma2).

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= t)%R /\
      (sum_weights vs > t - weight v)%R
      .

Lemma exists_pivotal_message : exists v, potentially_pivotal v.
Proof.
  destruct byzantine_fault_tolerance_interval as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
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
  exists p, non_trivial p.
Proof.
  destruct exists_pivotal_message as [v Hpivotal].
  destruct (estimator_total []) as [c Hc].
  exists (In (c,v,[])).
  split.
  - exists [(c,v,[])].
    split.
    { apply protocol_state_cons with c v [].
    - constructor.
    - assumption.
    - left. reflexivity.
    - simpl. rewrite eq_dec_if_true; try constructor.
    - constructor; try constructor; intro; inversion H.
    - unfold fault_tolerance_condition. unfold fault_weight_state. unfold equivocating_validators.
      simpl. unfold equivocating_messages. rewrite eq_dec_if_true; try reflexivity.
      simpl. apply Rge_le. apply threshold_nonnegative.
    }
    intros sigma H.
    destruct H as [_ [_ Hincl]]. apply Hincl. left. reflexivity.
  - 
  Admitted.