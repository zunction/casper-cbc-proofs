Require Import Coq.Classes.RelationClasses.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.sort.
Require Import Casper.FullStates.state_eq.


Definition state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  forall msg, in_state_eq msg sigma1 -> in_state_eq msg sigma2.

Lemma state_inclusion_empty : forall sigma, state_inclusion Empty sigma.
Proof.
  intros. unfold state_inclusion. intros. exfalso; apply (in_state_eq_empty _ H).
Qed.

Lemma state_inclusion_next_l : forall msg sigma sigma',
  state_inclusion sigma sigma' ->
  state_inclusion (next msg sigma) (next msg sigma').
Proof.
  unfold state_inclusion.
  intros. apply in_state_eq_next in H0.
  unfold in_state_eq.
  destruct H0.
  - exists msg. split; try assumption.
    rewrite in_state_iff. left. reflexivity.
  - apply H in H0. destruct H0 as [msg0' [Hin Heq]].
    exists msg0'. split; try assumption.
    rewrite in_state_iff. right. assumption.
Qed.

Lemma state_inclusion_next_r : forall msg sigma sigma',
  state_inclusion sigma sigma' ->
  state_inclusion sigma (next msg sigma').
Proof.
  unfold state_inclusion. intros.
  apply H in H0. destruct H0 as [msg0' [Hin Heq]].
    exists msg0'. split; try assumption.
    rewrite in_state_iff. right. assumption.
Qed.


Theorem state_inclusion_reflexive : Reflexive state_inclusion.
Proof.
  intros sigma msg H. assumption.
Qed.

Theorem state_inclusion_transitive : Transitive state_inclusion.
Proof.
  intros sigma1 sigma2 sigma3 H12 H23 msg Hin.
  apply H12 in Hin. apply (H23 _ Hin).
Qed.

Theorem state_eq_inclusion : forall sigma1 sigma2,
  state_eq sigma1 sigma2 ->
  state_inclusion sigma1 sigma2.
Proof.
  unfold state_inclusion.
  intros. inversion H; subst; clear H.
  destruct H1 as [sigmas [Hsigma1s Hsigma2s]].
  inversion H0; subst; clear H0. destruct H.
  apply (in_sorted_state_all _ _ Hsigma1s) in H.
  destruct H as [xs [Hxs Hin]].
  unfold in_state_eq.
  apply (in_sort_state _ _ Hsigma2s) in Hin.
  destruct Hin as [x' [Hx's Hin]]. 
  exists x'. split; try assumption.
  apply (message_sort_eq _ _ _ Hxs) in Hx's.
  apply (message_eq_transitive msg x x'); assumption.
Qed.

Theorem sorted_state_inclusion : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  state_inclusion sigma1 sigma2 <-> syntactic_state_inclusion sigma1 sigma2.
Proof.
  intros.
  split; intros.
  { intros msg Hin.
    apply in_sorted_state in Hin as Hjs; try assumption.
    apply (set_in_state_sorted _ _ H Hjs) in Hin.
    apply H1 in Hin.
    apply (set_in_state_sorted _ _ H0 Hjs) in Hin.
    assumption.
  }
  {
    intros msg Hin. inversion Hin; subst; clear Hin. destruct H2.
    apply H1 in H2. unfold in_state_eq. exists x. split; assumption.
  }
Qed.
