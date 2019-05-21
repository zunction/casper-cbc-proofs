Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.state_inclusion.

Inductive sorted_subset : state -> state -> Prop :=
  | SubSet_Empty: forall sigma,
          sorted_subset Empty sigma
  | SubSet_Next_l: forall msg sigma sigma',
          sorted_subset sigma sigma' ->
          sorted_subset (next msg sigma) (next msg sigma')
  | SubSet_Next_r: forall msg sigma sigma',
          sorted_subset sigma sigma' ->
          sorted_subset sigma (next msg sigma')
  .

Notation "sigma1 '=>' sigma2" :=
  (sorted_subset sigma1 sigma2)
  (at level 20).


Lemma sorted_subset_syntactic_inclusion : forall sigma sigma',
  sorted_subset sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros sigma sigma' H. induction H; intros.
  - intros msg H. exfalso. apply (in_empty_state _ H).
  - intros msg' H0. inversion H0; subst; clear H0. 
    apply no_confusion_next in H1; destruct H1; subst.
    destruct H3; subst.
    + constructor. left. reflexivity.
    + constructor. right. apply IHsorted_subset. assumption.
  - constructor. right.  apply IHsorted_subset. assumption.
Qed.


Lemma syntactic_inclusion_sorted_subset : forall sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  syntactic_state_inclusion sigma sigma' ->
  sorted_subset sigma sigma'.
Proof.
  intros sigma sigma'.
  generalize dependent sigma.
  induction sigma'; intros.
  - destruct sigma.
    + constructor.
    + rewrite add_is_next in *. assert (H2 : in_state (c, v, sigma1) Empty).
      { apply H1. constructor. left. reflexivity. }
      exfalso. apply (in_empty_state _ H2).
  - clear IHsigma'1. rewrite add_is_next in *.
    apply locally_sorted_tail in H0 as LSsigma'2.
    destruct sigma.
    + constructor.
    + rewrite add_is_next in *.
      apply sorted_syntactic_state_inclusion in H1; try assumption.
      destruct H1; destruct H1; apply locally_sorted_tail in H0.
      * inversion H1; subst; clear H1.
        apply SubSet_Next_l.
        apply locally_sorted_tail in H.
        apply IHsigma'2; assumption.
      * apply SubSet_Next_r.
        apply IHsigma'2; assumption.
Qed.

Corollary sorted_subset_inclusion : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_subset sigma1 sigma2 <-> state_inclusion sigma1 sigma2.
Proof.
  intros; split; intro.
  - apply sorted_state_inclusion; try assumption.
    apply sorted_subset_syntactic_inclusion. assumption.
  - apply syntactic_inclusion_sorted_subset; try assumption.
    apply sorted_state_inclusion; assumption.
Qed.
