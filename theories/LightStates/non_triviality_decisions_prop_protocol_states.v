Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.

Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.states.
Require Import Casper.LightStates.hash_state.
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
      (sum_weights vs > t - weight v)%R /\
      exists v', ~ In v' (v :: vs)
      .

Lemma exists_pivotal_validator : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [[v [Hin Hlte]] Hv']]]].
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
  - destruct Hv' as [v' Hnin]. exists v'. intro. apply Hnin.
    destruct H; subst; try assumption.
    apply set_remove_1 in H. assumption.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  exists p, non_trivial p.
Proof.
  destruct exists_pivotal_validator as [v [vs [Hnodup [Hvnin [Hlte [Hgt [v' Hv'nin]]]]]]].
  destruct (estimator_total []) as [c Hc].
  exists (In (c,v,[])).
  split.
  - exists [(c,v,[])].
    split; try (apply (protocol_state_singleton c v) in Hc; try assumption; constructor).
    intros sigma H.
    destruct H as [_ [_ Hincl]]. apply Hincl. left. reflexivity.
  - apply exist_equivocating_messages in Hv'nin as Heqv.
    destruct Heqv as [j1 [j2 [Hj1ps [Hj2ps [c1 [c2 [Hval1 [Hval2 Heqv]]]]]]]].
    exists ((c1, v, hash_state j1) :: flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
    split.
    + induction vs.
      * simpl. apply protocol_state_singleton; try assumption.
      * simpl.
        { apply protocol_state_cons with c1 a j1; try assumption.
          - right; left; reflexivity.
          - admit.
          -
  Admitted.