Require Import Coq.Classes.RelationClasses.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.adequacy.sort.


(** State and message equality (as sets) **)

Inductive state_eq : state -> state -> Prop :=
  | State_eq : forall sigma1 sigma2,
      (exists sigmas, sort sigma1 sigmas /\ sort sigma2 sigmas) ->
      state_eq sigma1 sigma2.

Lemma sorted_state_eq_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  state_eq sigma1 sigma2 ->
  sigma1 = sigma2.
Proof.
  intros. inversion H1; subst; clear H1.
  apply sort_sorted_idem in H. apply sort_sorted_idem in H0.
  destruct H2 as [sigmas [Hsigma1s Hsigma2s]].
  apply (sort_functional _ _ _ H) in Hsigma1s; clear H; subst.
  apply (sort_functional _ _ _ H0) in Hsigma2s; clear H0; subst.
  reflexivity.
Qed.

Lemma state_eq_reflexive : Reflexive state_eq.
Proof.
  unfold Reflexive. induction x.
  - constructor. exists Empty. split; constructor.
  - constructor.
    inversion IHx2; subst; clear IHx2.
    destruct H as [x2s [Hx2s _]].
    inversion IHx1; subst; clear IHx1.
    destruct H as [x1s [Hx1s _]].
    destruct (add_in_sorted_total (c, v, x1s) x2s) as [sigmas Hsigmas].
    exists sigmas.
    assert (forall A : Prop, A -> (A /\ A)); try (intros; split; assumption).
    apply H. rewrite add_is_next.
    apply Sort_next with x1s x2s; assumption.
Qed.

Lemma state_eq_symmetric : Symmetric state_eq.
Proof.
  unfold Symmetric.
  intros. destruct H. destruct H as [sigmas [H1 H2]].
  constructor. exists sigmas. split; assumption.
Qed.

Lemma state_eq_empty : forall sigma,
  state_eq sigma Empty -> sigma = Empty.
Proof.
  intros.
  inversion H; subst; clear H.
  destruct H0 as [zs [Hzs1 Hzs2]].
  inversion Hzs2; subst; clear Hzs2.
  apply sort_empty. assumption.
Qed.

Lemma empty_eq_state : forall sigma,
  state_eq Empty sigma -> sigma = Empty.
Proof.
  intros. apply state_eq_empty. apply state_eq_symmetric. assumption.
Qed.

Lemma state_eq_transitive : Transitive state_eq.
Proof.
  unfold Transitive.
  intros.
  constructor.
  inversion H; subst; clear H.
  destruct H1 as [xys [Hxs Hys]].
  inversion H0; subst; clear H0.
  destruct H as [yzs [Hys' Hzs]].
  apply (sort_functional _ _ _ Hys) in Hys'; subst; clear Hys.
  exists yzs. split; assumption.
Qed.


Lemma sort_state_eq : forall sigma sigmas,
  sort sigma sigmas -> state_eq sigma sigmas.
Proof.
  intros. constructor.
  exists sigmas.
  split; try assumption.
  apply sort_sorted_idem.
  apply sort_is_sorted with sigma.
  assumption.
Qed.

Definition message_eq (msg1 : message) (msg2 : message) : Prop :=
  state_eq (next msg1 Empty) (next msg2 Empty).

Lemma message_sort_eq : forall msg1 msg2 msgs,
  message_sort msg1 msgs -> message_sort msg2 msgs -> message_eq msg1 msg2.
Proof.
  unfold message_sort. unfold message_eq. intros.
  constructor. exists (next msgs Empty).
  split; assumption.
Qed.

Lemma message_eq_reflexive : Reflexive message_eq.
Proof.
  unfold Reflexive. unfold message_eq. intro. apply state_eq_reflexive.
Qed.

Lemma message_eq_transitive : Transitive message_eq.
Proof.
  unfold Transitive.
  unfold message_eq. intros msg1 msg2 msg3. apply state_eq_transitive.
Qed.

Lemma message_eq_construct : forall msg1 msg2,
  message_eq msg1 msg2
  -> exists c v j1 j2, msg1 = (c, v, j1)/\ msg2 = (c, v, j2) /\ state_eq j1 j2.
Proof.
  intros. inversion H; subst; clear H.
  destruct H0 as [msgs [H1s H2s]].
  inversion H1s; subst; clear H1s; try (exfalso; symmetry in H0; apply (no_confusion_next_empty _ _ H0)).
  rename H0 into Hjs.
  inversion H2s; subst; clear H2s; try (exfalso; symmetry in H3; apply (no_confusion_next_empty _ _ H3)).
  rewrite add_is_next in *.
  apply no_confusion_next in H; destruct H; subst.
  apply no_confusion_next in H0; destruct H0; subst.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  apply add_in_empty in H2; subst.
  apply add_in_empty in H5.
  apply no_confusion_next in H5. destruct H5 as [H5 _]. inversion H5; subst; clear H5.
  exists c0. exists v0. exists j. exists j0. repeat (split; try reflexivity).
  exists js0. split;assumption.
Qed.

(*******************************)
(** Semantic state membership **)
(*******************************)

Definition in_state_eq (msg : message) (sigma' : state) : Prop :=
  exists msg', in_state msg' sigma' /\ message_eq msg msg'.

Lemma in_state_eq_empty : forall msg, ~ in_state_eq msg Empty.
Proof.
  intro. intro. inversion H; subst; clear H. destruct H0.
  apply (in_empty_state _ H).
Qed.

Lemma in_state_eq_next : forall msg msg' sigma',
  in_state_eq msg (next msg' sigma') ->
  message_eq msg msg' \/ in_state_eq msg sigma'.
Proof.
  unfold in_state_eq.
  intros. destruct H as [msg'' [Hin Heq]].
  rewrite in_state_iff in Hin; destruct Hin; subst.
  - left; assumption.
  - right.  exists msg''. split; assumption.
Qed.


Lemma set_in_state_sorted : forall msg sigma,
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  in_state_eq msg sigma <-> in_state msg sigma.
Proof.
  intros. split; intros.
  {
  inversion H1; subst; clear H1. destruct H2.
  apply message_eq_construct in H2.
  destruct H2 as [c0 [v0 [j1 [j2 [EQ1 [EQ2 SEQ]]]]]]; subst.
  apply in_sorted_state in H1 as Hj2s; try assumption.
  inversion SEQ; subst; clear SEQ.
  destruct H2 as [js [Hj1s Hj2s']].
  apply locally_sorted_message_justification in H0.
  apply locally_sorted_message_justification in Hj2s.
  apply sort_sorted_idem in H0.
  apply sort_sorted_idem in Hj2s.
  apply (sort_functional _ _ _ H0) in Hj1s; subst; clear H0.
  apply (sort_functional _ _ _ Hj2s) in Hj2s'; subst; clear Hj2s.
  assumption.
  }
  {
    exists msg. split; try assumption.
    apply message_eq_reflexive.
  }
Qed.

