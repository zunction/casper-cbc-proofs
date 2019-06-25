Require Import Coq.Reals.Reals.
Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.justifications.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.

Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match message_eq_dec msg1 msg2 with
  | left _  => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match v_eq_dec v1 v2 with
      | left _  => negb (justification_in (Hash msg1) j2) && negb (justification_in (Hash msg2) j1)
      | right _ => false
      end
    end
  end.

Definition equivocating_message_state (msg : message) : state -> bool :=
  existsb (equivocating_messages msg).

Lemma equivocating_message_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  forall msg,
  equivocating_message_state msg sigma = true -> equivocating_message_state msg sigma' = true.
Proof.
  unfold equivocating_message_state. 
  intros. rewrite existsb_exists in *. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Definition equivocating_senders (sigma : state) : set V :=
  set_map v_eq_dec sender (filter (fun msg => equivocating_message_state msg sigma) sigma).

Lemma equivocating_senders_nodup : forall sigma,
  NoDup (equivocating_senders sigma).
Proof.
  intros. apply set_map_nodup.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  incl sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_message_state msg sigma) sigma').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_message_state_incl. assumption.
Qed.

Definition sum_weights : set V -> R := fold_right (fun v r => (weight v + r)%R) 0%R.

Definition fault_weight_state (sigma : state) : R := sum_weights (equivocating_senders sigma).

Lemma sum_weights_in : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (weight v + sum_weights (set_remove v_eq_dec v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (eq_dec_left v_eq_dec v). rewrite H. reflexivity.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (v_eq_dec v a); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (weight v) (weight a)). rewrite Rplus_assoc. 
    apply Rplus_eq_compat_l. apply IHvs; assumption.
Qed.

Lemma sum_weights_incl : forall vs vs',
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  intros vs vs'. generalize dependent vs.
  induction vs'; intros.
  - apply incl_empty in H1; subst. apply Rle_refl.
  - inversion H0; subst; clear H0.
    destruct (in_dec v_eq_dec a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup v_eq_dec a). assumption.
      * assumption.
      * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
        destruct Hrem as [Hin Hxa].
        apply H1 in Hin. destruct Hin; try assumption.
        exfalso; subst. apply Hxa. reflexivity.
      * assumption.
    + simpl. apply Rle_trans with (sum_weights vs').
      * apply IHvs'; try assumption.
        intros x Hin. apply H1 in Hin as Hin'. destruct Hin'; try assumption.
        exfalso; subst. apply n. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. apply weight_positive.
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

Lemma fault_weight_max : forall sigma,
  (fault_weight_state sigma <= sum_weights (set_map v_eq_dec sender sigma))%R.
Proof.
  intros.
  apply sum_weights_incl; try apply set_map_nodup.
  unfold equivocating_senders.
  apply set_map_incl.
  intros x Hin.
  apply filter_In in Hin. destruct Hin; assumption.
Qed.
