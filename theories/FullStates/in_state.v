Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.


(** Syntactic membership predicate **)
Inductive in_state : message -> state -> Prop :=
  | InState : forall msg' msg sigma, 
          msg' = msg \/ in_state msg' sigma -> 
          in_state msg' (next msg sigma)
  .

Lemma in_empty_state : forall msg,
  ~ in_state msg Empty.
Proof.
  intros. intro. inversion H; subst.
  apply no_confusion_next_empty in H0; inversion H0.
Qed.

Theorem in_state_dec : forall msg sigma, 
  in_state msg sigma \/ ~ in_state msg sigma.
Proof.
  induction sigma.
  - right. apply in_empty_state.
  - rewrite add_is_next in *.
    clear IHsigma1.
    destruct (message_eq_dec msg (c,v,sigma1)).
    + left. constructor. left. assumption.
    + destruct IHsigma2.
      * left. constructor. right. assumption.
      * right. intro. inversion H0; subst; clear H0.
        rewrite add_is_next in *.
        apply no_confusion_next in H1; destruct H1; subst.
        destruct H3; try apply (n H0); apply (H H0).
Qed.

Lemma in_singleton_state : forall msg msg',
  in_state msg (next msg' Empty) -> msg = msg'.
Proof.
  intros.
  inversion H; subst; clear H.
  apply no_confusion_next in H0; destruct H0; subst.
  destruct H2; try assumption.
  exfalso. apply (in_empty_state _ H).
Qed.

Lemma in_sorted_state : forall sigma,
  locally_sorted sigma ->
   forall msg,
  in_state msg sigma ->
  locally_sorted_msg msg.
Proof.
  intros sigma H. induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - apply in_singleton_state in H0; subst. apply locally_sorted_message_justification. assumption.
  - inversion H2; subst; clear H2. rewrite add_is_next in H3.
    apply no_confusion_next in H3; destruct H3; subst.
    destruct H5; subst.
    + apply locally_sorted_message_justification. assumption.
    + apply IHlocally_sorted2 ; assumption.
Qed.

Theorem add_in_sorted_message_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  in_state msg sigma'.
Proof.
  intros.
  induction H; try (constructor; left; reflexivity).
  constructor. right. assumption.
Qed.

Theorem add_in_sorted_no_junk : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  forall msg', in_state msg' sigma' -> msg' = msg \/ in_state msg' sigma.
Proof.
  intros msg sigma sigma' H.
  induction H as
  [ [(hc, hv) hj]
  | [(hc, hv) hj] Hsigma
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma HLT
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma Hsigma' HGT HAdd H_H 
  ]; intros [(c', v') j'] HIn
  ; inversion HIn as [[(inc, inv) inj] [(inc', inv') inj'] insigma [HInEq | HIn'] X Y ]
    ; clear HIn; subst
  ; try (right; assumption)
  ; try (left; assumption)
  . 
  - right. constructor. right. assumption.
  - inversion HInEq; clear HInEq; subst. right. constructor. left. reflexivity.
  - apply H_H in HIn'. destruct HIn' as [HInEq | HIn'].
    + left. assumption.
    + right. constructor. right. assumption.
Qed.

Lemma state_set_In : forall msg1 msg2 sigma,
  locally_sorted (next msg2 sigma) ->
  in_state msg1 sigma ->
  message_lt msg2 msg1.
Proof.
  intros. generalize dependent msg1. generalize dependent msg2. induction sigma; intros.
  - apply in_empty_state in H0; inversion H0.
  - rewrite add_is_next in *. inversion H0; clear H0; subst. 
    rewrite add_is_next in *. apply no_confusion_next in H1. destruct H1; subst.
     destruct msg2 as [(c2, v2) j2]. inversion H; subst; clear H.
    rewrite add_is_next in *.  apply no_confusion_next in H5. destruct H5; subst.
    destruct H3; subst; try assumption.
    apply (message_lt_transitive (c2, v2, j2) (c, v, sigma1) msg1 H6).
    apply IHsigma2; assumption.
Qed.


Theorem add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
  induction sigma; intros; repeat rewrite add_is_next in *.
  - exfalso. apply (in_empty_state _ H0).
  - inversion H0; subst; clear H0.
    rewrite add_is_next in *.
    apply no_confusion_next in H1; destruct H1; subst.
    destruct H3.
    + subst. constructor.
    + apply (state_set_In _ _ _ H) in H0 as Hlt.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.

