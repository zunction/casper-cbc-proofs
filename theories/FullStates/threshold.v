Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.RealsExtras.

Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.fault_weights.

(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Parameter t : R.

Parameter threshold_nonnegative : (t >= 0)%R .

Parameter sufficient_validators_condition :
  exists (vs : list V), NoDup vs /\ (sum_weights vs > t)%R.

Parameter validator_below_threshold_condition :
  exists (v : V), (weight v <= t)%R.

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

Lemma sufficient_validators_pivotal_non_empty :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > t)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove v_eq_dec v vs) <= t)%R /\
      set_remove v_eq_dec v vs <> nil.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlt]]]]].
  destruct vs.
  - inversion Hin.
  - destruct vs.
    + destruct Hin as [Heq | Hin]; try inversion Hin; subst.
      destruct validator_below_threshold_condition as [v0 Hlt0].
      assert (Hneq : v0 <> v).
      {
        intro; subst. simpl in Hgt. rewrite Rplus_0_r in Hgt.
        apply Rgt_lt in Hgt.
        apply (Rlt_le_trans t) in Hlt0; try assumption.
        apply (Rlt_asym _ _ Hlt0).
        admit.
      }
      exists [v0; v].
  Admitted.