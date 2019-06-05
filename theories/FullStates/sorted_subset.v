Require Import Coq.Classes.RelationClasses.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.state_inclusion.
Require Import Casper.FullStates.add_in_sorted.

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

Lemma sorted_subset_syntactic_inclusion : forall sigma sigma',
  sorted_subset sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  unfold syntactic_state_inclusion.
  intros sigma sigma' H. induction H; intros; repeat rewrite get_messages_next.
  - intros msg H. exfalso. apply (in_empty_state _ H).
  - intros msg' H0. 
    destruct H0; subst.
    + left. reflexivity.
    + right. apply IHsorted_subset. assumption.
  - intros msg' H'. right.  apply IHsorted_subset. assumption.
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
      { apply H1. left. reflexivity. }
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


Lemma sorted_subset_reflexive : Reflexive sorted_subset. 
Proof.
  intro sigma.
  induction sigma.
  - constructor.
  - rewrite add_is_next in *.
    constructor. assumption.
Qed.

Lemma sorted_subset_empty : forall sigma,
  sorted_subset sigma Empty -> sigma = Empty.
Proof.
  intros.
  inversion H as
    [ gamma Uempty Ugamma
    | msg gamma gamma' IHgamma Unext Unext'
    | msg gamma gamma' IHgamma Ugamma Unext'
    ]
  ; try reflexivity
  ; exfalso; apply (no_confusion_next_empty _ _ Unext')
  .
Qed.

Lemma sorted_subset_transitive : Transitive sorted_subset .
Proof.
  intros sigma1 sigma2 sigma3. generalize dependent sigma2.  generalize dependent sigma1.
  induction sigma3; intros.
  - apply sorted_subset_empty in H0; subst.
    apply sorted_subset_empty in H; subst.
    constructor.
  - clear IHsigma3_1. rename sigma3_1 into j.
    rename sigma3_2 into sigma3. rename IHsigma3_2 into IHsigma3. 
    rewrite add_is_next in *.
    inversion H0 as
      [ gamma3 Uempty Ugamma3
      | msg3 gamma2 gamma3 IHgamma3 Unext2 Unext3
      | msg3 gamma2 gamma3 IHgamma3 Ugamma2 Unext3
      ]
    ; subst
    ; clear H0
    ; try rewrite add_is_next in *
    ; try (apply no_confusion_next in Unext2; destruct Unext2; subst)
    ; try (apply no_confusion_next in Unext3; destruct Unext3; subst)
    .
    + apply sorted_subset_empty in H; subst. constructor.
    + inversion H as
        [ gamma21 Uempty1 Ugamma21
        | msg21 gamma1 gamma21 IHgamma21 Unext1 Unext21
        | msg21 gamma1 gamma21 IHgamma21 Ugamma1 Unext21
        ]
      ; subst
      ; clear H
      ; try rewrite add_is_next in *
      ; try (apply no_confusion_next in Unext1; destruct Unext1; subst)
      ; try (apply no_confusion_next in Unext21; destruct Unext21; subst)
      .
      * constructor.
      * constructor. apply IHsigma3 with gamma2; assumption.
      * apply SubSet_Next_r. apply IHsigma3 with gamma2; assumption.
    + apply SubSet_Next_r. apply IHsigma3 with sigma2; assumption.
Qed.

Lemma add_in_sorted_sorted_subset : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  sorted_subset sigma sigma'.
Proof.
  intros.
  apply add_in_sorted_state_preservation in H1.
  apply syntactic_inclusion_sorted_subset; try assumption.
Qed.

