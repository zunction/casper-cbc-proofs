Require Import Coq.Reals.Reals.

Require Import Casper.validators.
Require Import Casper.consensus_values.
Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.preamble.

(****************************)
(** Fault Weight of States **)
(****************************)

(**
Note that this includes equivocation fault weight, as we defaulted 
the weight of non-equivocating messages to 0
**)

(**********************)
(** fault_weight_msg **)
(**********************)

Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 j1 j2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,j1) (c2,v2,j2) 0
  | fault_weight_c_msg: forall c v j,
      fault_weight_msg (c,v,j) (c,v,j) 0
  | fault_weight_msg1: forall c1 c2 v j1 j2,
      in_state (c1,v,j1) j2 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_msg2: forall c1 c2 v j1 j2,
      in_state (c2,v,j2) j1 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_next: forall c1 c2 v j1 j2,
      c1 <> c2 \/ j1 <> j2 ->
      not (in_state (c1,v,j1) j2) ->
      not (in_state (c2,v,j2) j1) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

Theorem fault_weight_msg_functional : forall msg1 msg2 r1 r2,
  fault_weight_msg msg1 msg2 r1 ->
  fault_weight_msg msg1 msg2 r2 ->
  r1 = r2.
Proof.
  intros. inversion H; subst; clear H; inversion H0; subst; clear H0
  ; try reflexivity
  ; try contradiction.
  - destruct H6; contradiction.
  - destruct H1; contradiction.
Qed.

Theorem fault_weight_msg_total : forall msg1 msg2,
  exists r, fault_weight_msg msg1 msg2 r.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  destruct (v_eq_dec v1 v2).
  - destruct (c_eq_dec c1 c2).
    + destruct (state_eq_dec j1 j2); subst.
      * exists 0%R. apply fault_weight_c_msg.
      * destruct (in_state_dec (c2, v2, j1) j2).
        { exists 0%R. apply fault_weight_msg1. assumption. }
        destruct (in_state_dec (c2, v2, j2) j1).
        { exists 0%R. apply fault_weight_msg2. assumption. }
        exists (weight v2).
        apply fault_weight_next; try assumption.
        right. assumption.
    + subst.
      destruct (in_state_dec (c1, v2, j1) j2).
      { exists 0%R. apply fault_weight_msg1. assumption. }
      destruct (in_state_dec (c2, v2, j2) j1).
      { exists 0%R. apply fault_weight_msg2. assumption. }
      exists (weight v2).
      apply fault_weight_next; try assumption.
      left. assumption.
  - exists 0%R. apply fault_weight_v_diff. assumption.
Qed.

Theorem fault_weight_msg_nonnegative : forall msg1 msg2 r,
  fault_weight_msg msg1 msg2 r ->
  (0 <= r)%R.
Proof.
  intros.
  inversion H
    ; subst
    ; try apply Rle_refl.
  left.
  apply weight_positive.
Qed.

(*******************************)
(* fauult_weight_message_state *)
(*******************************)

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_Empty: forall msg,
      fault_weight_message_state msg Empty 0
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (next msg2 sigma) (r1 + r2)%R
.

Theorem fault_weight_message_state_functional : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_message_state_total : forall msg sigma,
  exists r, fault_weight_message_state msg sigma r.
Admitted.

Lemma fault_weight_message_state_empty_zero : forall msg r,
  fault_weight_message_state msg Empty r ->
  r = 0%R.
Proof.
  intros.
  inversion H; subst; try reflexivity.
  apply no_confusion_next_empty in H0. inversion H0.
Qed.

Lemma fault_weight_message_state_nonnegative : forall msg sigma r,
  fault_weight_message_state msg sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  - apply Rle_refl.
  - apply fault_weight_msg_nonnegative in H0.
    apply (Rplus_le_le_0_compat _ _ IHfault_weight_message_state H0).
Qed.

Lemma fault_weight_message_state_backwards : forall msg msg' sigma r1 r2,
  fault_weight_msg msg msg' r1 ->
  fault_weight_message_state msg (next msg' sigma) r2 ->
  fault_weight_message_state msg sigma (r2 - r1)%R.
Proof.
  intros.
  inversion H0; subst.
  - symmetry in H3.
    apply no_confusion_next_empty in H3. inversion H3.
  - apply no_confusion_next in H1. destruct H1; subst.
    apply (fault_weight_msg_functional msg msg' r1 r3 H) in H4; subst.
    rewrite Rplusminus_assoc. unfold Rminus.
    rewrite Rplus_opp_r. rewrite Rplus_0_r.
    assumption.
Qed.

Lemma fault_weight_message_state_sorted_subset : forall msg sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  generalize dependent r1. generalize dependent r2.
  induction H; intros.
  + apply fault_weight_message_state_empty_zero in H0; subst.
    apply fault_weight_message_state_nonnegative in H1.
    assumption.
  + destruct (fault_weight_msg_total msg msg0) as [r H2].
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H1.
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H0.
    apply (IHsorted_subset _ H1) in H0.
    unfold Rminus in H0. apply Rplus_le_reg_r in H0.
    assumption.
  + destruct (fault_weight_msg_total msg msg0) as [r H2].
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply fault_weight_msg_nonnegative in H2.
    apply (Rminus_lt_r r2 r) in H2.
    apply (Rle_trans _ _ _ H0 H2).
Qed.

(**********************)
(* fault_weight_state *)
(**********************)

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_Empty: 
      fault_weight_state Empty 0
  | fault_weight_state_Next: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (next msg sigma) (r1 + r2)%R
.


Theorem fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
Admitted.

Lemma fault_weight_state_nonnegative : forall sigma r,
  fault_weight_state sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  - apply Rle_refl.
  - apply fault_weight_message_state_nonnegative in H.
    apply (Rplus_le_le_0_compat _ _ H IHfault_weight_state).
Qed.

Lemma fault_weight_state_empty : forall r,
  fault_weight_state Empty r ->
  (r = 0)%R.
Proof.
  intros.
  inversion H; subst.
  - reflexivity.
  - apply no_confusion_next_empty in H0. inversion H0.
Qed.

Lemma fault_weight_state_backwards : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_state (next msg sigma) r2 ->
  fault_weight_state sigma (r2 - r1)%R.
Proof.
  intros.
  inversion H0; subst.
  - symmetry in H2.
    apply no_confusion_next_empty in H2. inversion H2.
  - apply no_confusion_next in H1. destruct H1; subst.
    apply (fault_weight_message_state_functional msg sigma r1 r0 H) in H2; subst.
    rewrite Rplusminus_assoc.
    rewrite Rplus_minus.
    assumption.
Qed.

Lemma fault_weight_state_sorted_subset : forall sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  generalize dependent r1. generalize dependent r2.
  induction H; intros.
  + apply fault_weight_state_empty in H0; subst.
    apply fault_weight_state_nonnegative in H1. 
    assumption.
  + destruct (fault_weight_message_state_total msg sigma) as [r1' H2].
    destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H2) in H0.
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply (fault_weight_message_state_sorted_subset _ _ _ _ _ H H2) in H3.
    (* maybe this part can be proved easier *)
    apply (Rplus_le_compat_r r1' _ _) in H0.
    rewrite Rplusminus_assoc_r in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_r in H0.
    apply (Rplus_le_compat_l (Ropp r2') _ _) in H3.
    rewrite Rplus_opp_l in H3.
    rewrite Rplusminus_assoc_r in H0.
    apply (Rplus_ge_reg_neg_r r2 (Ropp r2' + r1') r1 H3) in H0 .
    assumption.
  + destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply fault_weight_message_state_nonnegative in H3.
    assert (H4 := Rminus_lt_r r2 r2' H3).
    apply (Rle_trans _ _ _ H0 H4).
Qed.

Lemma fault_weight_state_add : forall msg sigma sigma' r1 r2,
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  apply add_in_sorted_sorted_subset in H1; try assumption.
  apply (fault_weight_state_sorted_subset sigma sigma' r1 r2 H1 H2 H3).
Qed.
