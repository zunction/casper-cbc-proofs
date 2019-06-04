Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.

Definition syntactic_state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  forall msg, in_state msg sigma1 -> in_state msg sigma2.

Theorem add_in_sorted_state_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros msg sigma sigma' H. unfold syntactic_state_inclusion.
  induction H; intros; try assumption. 
  - exfalso. apply (in_empty_state msg0 H).
  - constructor. right. assumption.
  - inversion H1; subst; clear H1.
    apply no_confusion_next in H2; destruct H2; subst.
    destruct H4; subst.
    + constructor. left. reflexivity.
    + constructor. right. apply IHadd_in_sorted.
      assumption. 
Qed.

Lemma sorted_syntactic_state_inclusion_first_equal : forall sigma sigma' msg,
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg sigma') ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros.
  intros msg' Hin.
  apply (state_set_In _ _ _ H) in Hin as Hlt.
  assert (Hin' : in_state msg' (next msg sigma)).
  { constructor. right. assumption. }
  apply H1 in Hin'. inversion Hin'; subst; clear Hin'.
  apply no_confusion_next in H2; destruct H2; subst.
  destruct H4; try assumption.
  subst. exfalso. apply (message_lt_irreflexive _ Hlt).
Qed.

Lemma sorted_syntactic_state_inclusion : forall sigma sigma' msg msg',
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg' sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg' sigma') ->
  (msg = msg' /\ syntactic_state_inclusion sigma sigma')
  \/
  (message_lt msg' msg /\ syntactic_state_inclusion (next msg sigma) sigma').
Proof.
  intros.
  assert (Hin : in_state msg (next msg' sigma')).
  { apply H1. constructor. left. reflexivity. }
  inversion Hin; subst; clear Hin.
  apply no_confusion_next in H2; destruct H2; subst.
  destruct H4.
  - left. subst. split; try reflexivity.
    apply sorted_syntactic_state_inclusion_first_equal with msg'; assumption.
  - right. apply (state_set_In _ _ _ H0) in H2.
    split; try assumption.
    intros msg1 Hin1.
    inversion Hin1; subst.
    apply no_confusion_next in H3; destruct H3; subst.
    destruct H5; subst.
    + apply H1 in Hin1.
      inversion Hin1; subst.
      apply no_confusion_next in H3; destruct H3; subst.
      destruct H5; subst; try assumption.
      exfalso. apply (message_lt_irreflexive _ H2).
    + apply (state_set_In _ _ _ H) in H3.
      apply H1 in Hin1.
      inversion Hin1; subst.
      apply no_confusion_next in H4; destruct H4; subst.
      destruct H6; subst; try assumption.
      exfalso. apply (message_lt_transitive _ _ _ H2) in H3.
      apply (message_lt_irreflexive _ H3).
Qed.

Lemma sorted_syntactic_state_inclusion_eq_ind : forall sigma1 sigma2 msg1 msg2,
  locally_sorted (next msg1 sigma1) ->
  locally_sorted (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg1 sigma1) (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg2 sigma2) (next msg1 sigma1) ->
  msg1 = msg2 /\ syntactic_state_inclusion sigma1 sigma2 /\ syntactic_state_inclusion sigma2 sigma1.
Proof.
  intros.
  apply sorted_syntactic_state_inclusion in H1; try assumption.
  apply sorted_syntactic_state_inclusion in H2; try assumption.
  destruct H1; destruct H2; destruct H1; destruct H2; subst.
  - repeat (split; try reflexivity; try assumption).
  - exfalso. apply (message_lt_irreflexive _ H2).
  - exfalso. apply (message_lt_irreflexive _ H1).
  - exfalso. apply (message_lt_transitive _ _ _ H1) in H2. apply (message_lt_irreflexive _ H2).
Qed.

Theorem sorted_syntactic_state_inclusion_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  syntactic_state_inclusion sigma1 sigma2 ->
  syntactic_state_inclusion sigma2 sigma1 ->
  sigma1 = sigma2.
Proof.
  induction sigma1; intros; destruct sigma2; repeat rewrite add_is_next in *.
  - reflexivity.
  - assert (Hin : in_state (c,v, sigma2_1) Empty).
    { apply H2. constructor. left. reflexivity. }
    inversion Hin; subst; clear Hin. exfalso. apply (no_confusion_next_empty _ _ H3).
  - assert (Hin : in_state (c,v, sigma1_1) Empty).
    { apply H1. constructor. left. reflexivity. }
    inversion Hin; subst; clear Hin. exfalso. apply (no_confusion_next_empty _ _ H3).
  - apply sorted_syntactic_state_inclusion_eq_ind in H2; try assumption.
    destruct H2 as [Heq [Hin12 Hin21]].
    inversion Heq; subst; clear Heq.
    apply locally_sorted_tail in H.
    apply locally_sorted_tail in H0.
    apply IHsigma1_2 in Hin21; try assumption.
    subst.
    reflexivity.
Qed.

