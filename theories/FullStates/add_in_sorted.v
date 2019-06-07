Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.



Fixpoint add_in_sorted_fn (msg: message) (sigma: state) : state :=
  match msg, sigma with
  | _, Empty => next msg Empty
  | msg, add (c, v, j) to sigma' =>
    match message_compare msg (c, v, j) with
    | Eq => sigma
    | Lt => next msg sigma
    | Gt => next (c, v, j) (add_in_sorted_fn msg sigma')
    end
  end.

Lemma set_eq_add_in_sorted : forall msg sigma,
  set_eq (get_messages (add_in_sorted_fn msg sigma)) (msg :: (get_messages sigma)).
Proof.
  induction sigma.
  - simpl. rewrite get_messages_next. simpl. split; apply incl_refl.
  - clear IHsigma1. simpl.
    destruct (message_compare msg (c, v, sigma1)) eqn:Hcmp.
    + simpl. apply (proj1 message_compare_strict_order) in Hcmp. subst.
      split; intros x H.
      * right. assumption.
      * destruct H; try assumption; subst. left. reflexivity.
    + rewrite get_messages_next. simpl. split; apply incl_refl.
    + simpl. split; intros x Hin.
      * destruct Hin; try (right; left; assumption).
        apply IHsigma2 in H. destruct H; try (left; assumption).
        right; right; assumption.
      * { destruct Hin as [Hmsg | [H1 | H2]]
        ; (left; assumption) || (right; apply IHsigma2)
        .
        - left; assumption.
        - right; assumption.
        }
Qed.

Lemma add_in_sorted_next : forall msg1 msg2 sigma,
  add_in_sorted_fn msg1 (next msg2 sigma) =
    match message_compare msg1 msg2 with
    | Eq => next msg2 sigma
    | Lt => next msg1 (next msg2 sigma)
    | Gt => next msg2 (add_in_sorted_fn msg1 sigma)
    end.
Proof.
  intros msg1 [(c, v) j] sigma. reflexivity.
Qed.

Lemma add_in_sorted_non_empty : forall msg sigma,
  add_in_sorted_fn msg sigma <> Empty.
Proof.
  intros. intro Hadd.
  destruct sigma; inversion Hadd.
  - apply (no_confusion_next_empty _ _ H0).
  - destruct (message_compare msg (c, v, sigma1)); inversion H0.
    apply (no_confusion_next_empty _ _ H0).
Qed.


Lemma add_in_sorted_inv1 : forall msg msg' sigma,
  add_in_sorted_fn msg sigma = next msg' Empty -> msg = msg'.
Proof.
  intros [(c, v) j] msg' sigma AddA.
  destruct sigma.
  - simpl in AddA. rewrite add_is_next in AddA. apply no_confusion_next in AddA.
    destruct AddA. assumption.
  - simpl in AddA. destruct (message_compare (c, v, j) (c0, v0, sigma1)) eqn:Hcmp
    ; rewrite add_is_next in AddA; apply no_confusion_next in AddA; destruct AddA; subst;
    try reflexivity.
    + apply (proj1 message_compare_strict_order) in Hcmp; inversion Hcmp; subst; clear Hcmp.
      reflexivity.
    + exfalso. apply (add_in_sorted_non_empty _ _ H0).
Qed.

Lemma add_in_sorted_sorted : forall msg sigma,
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  locally_sorted (add_in_sorted_fn msg sigma).
Proof.
  intros msg sigma. generalize dependent msg.
  induction sigma; intros.
  - simpl. assumption.
  - clear IHsigma1; rename sigma1 into j; rename sigma2 into sigma; rename IHsigma2 into IHsigma.
    simpl. destruct msg as [(mc, mv) mj].
    apply locally_sorted_message_justification in H0 as Hmj.
    repeat rewrite add_is_next in *.
    apply locally_sorted_tail in H as Hsigma.
    apply locally_sorted_head in H as Hcvj. apply locally_sorted_message_justification in Hcvj as Hj.
    apply (IHsigma _ Hsigma) in H0 as HLSadd.
    destruct (message_compare (mc, mv, mj) (c, v, j)) eqn:Hcmp.
    + assumption.
    + constructor; assumption.
    + apply message_compare_asymmetric in Hcmp.
      apply locally_sorted_message_characterization in HLSadd as Hadd.
      destruct Hadd as [Hadd | [Hadd | Hadd]].
      * exfalso. apply (add_in_sorted_non_empty _ _ Hadd).
      * destruct Hadd as [msg' [Hmsg' Hadd]]. rewrite Hadd.
        apply add_in_sorted_inv1 in Hadd; subst.
        constructor; assumption.
      * destruct Hadd as [msg1 [msg2 [sigma' [Hadd [HLS' [H1 Hlt12]]]]]].
        rewrite Hadd in *. constructor; try assumption.
        assert (Forall (message_lt (c, v, j)) (get_messages (add_in_sorted_fn (mc, mv, mj) sigma))).
        { apply Forall_forall. intros. apply set_eq_add_in_sorted in H2.
          destruct H2 as [Heq | Hin]; subst; try assumption.
          apply locally_sorted_first with sigma; assumption.
        }
        rewrite Hadd in H2. rewrite get_messages_next in H2. apply Forall_inv in H2. assumption.
Qed.

