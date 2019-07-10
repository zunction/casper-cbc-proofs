Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.RealsExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.fault_weights.

(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Module Type Threshold
              (PVal : Validators)
              (PVal_Weights : Validators_Weights PVal)
              .

Import PVal.
Import PVal_Weights.

Parameter t : R.

Axiom threshold_nonnegative : (t >= 0)%R .

Axiom sufficient_validators_condition :
  exists (vs : list V), 
    NoDup vs /\ 
    ((fold_right (fun v r => (weight v + r)%R) 0%R) vs > t)%R
  .
    (*(sum_weights vs > t)%R. *)

End Threshold.

(*****************************)
(** Properties of Threshold **)
(*****************************)
Module Threshold_Properties
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PEstimator : Estimator PCons PVal PVal_Weights)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PEstimator.
Import PThreshold.

Module PFault_Weights := Fault_Weights PCons PVal PVal_Weights PEstimator.
Export PFault_Weights.

Lemma sufficient_validators_pivotal_ind : forall vss,
  NoDup vss ->
  (sum_weights vss > t)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights vs > t)%R /\
  exists v,
    In v vs /\
    (sum_weights (set_remove v_eq_dec v vs) <= t)%R.
Proof.
  induction vss; intros.
  simpl in H0.
  - exfalso. apply (Rge_gt_trans t) in H0; try apply threshold_nonnegative.
    apply Rgt_not_eq in H0. apply H0. reflexivity.
  - simpl in H0. destruct (Rtotal_le_gt (sum_weights vss) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + apply NoDup_cons_iff in H. destruct H as [Hnin Hvss]. apply IHvss in H1; try assumption.
      destruct H1 as [vs [Hvs [Hincl H]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.

Lemma sufficient_validators_pivotal :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > t)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove v_eq_dec v vs) <= t)%R.
Proof.
  destruct sufficient_validators_condition as [vs [Hvs Hweight]].
  apply (sufficient_validators_pivotal_ind vs Hvs) in  Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  exists vs'. repeat (split; try assumption).
Qed.

End Threshold_Properties.