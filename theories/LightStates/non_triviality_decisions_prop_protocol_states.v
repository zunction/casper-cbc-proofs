Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.

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

Definition non_trivial_prop (sigma : state) : Prop :=
  exists msg : message,
    In msg sigma /\
    exists (vs : list V),
      NoDup vs /\
      ~In (validator msg) vs /\
      (sum_weights vs <= t)%R /\
      (sum_weights vs > t - weight (validator msg))%R
      .

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  exists p, non_trivial p.
Proof.
  destruct byzantine_fault_tolerance_interval as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists non_trivial_prop.
  split.
  - destruct (protocol_state_singleton v) as [msg [Heq Hps]].
    exists [msg].
    split; try assumption.
    intros sigma H.
    exists msg. destruct H as [_ [Hpss Hinc]].
    split.
    + apply Hinc. left. reflexivity.
    + subst. exists (set_remove v_eq_dec (validator msg) vs). repeat split.
      * apply set_remove_nodup. assumption.
      * intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
      * assumption.
  Admitted.