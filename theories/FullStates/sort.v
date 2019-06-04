Require Import Casper.preamble.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.syntactic_state_inclusion.

(** (Insertion) sorting function **)

Inductive sort : state -> state -> Prop :=
  | Sort_empty : sort Empty Empty
  | Sort_next : forall c v j js sigma sigmas sigma',
    sort j js ->
    sort sigma sigmas ->
    add_in_sorted (c,v,js) sigmas sigma' ->
    sort (next (c,v,j) sigma) sigma'.

Fixpoint sort_fn (sigma : state) : state :=
  match sigma with
  | Empty => Empty
  | add (c, v, j) to sigma' =>
    add_in_sorted_fn (c, v, sort_fn j) (sort_fn sigma')
  end.

Lemma sort_function : RelationFunction sort sort_fn.
Proof.
  intros sigma sigma'. generalize dependent sigma'.
  induction sigma; intros; split; intros.
  - inversion H; subst. reflexivity.
  - subst. simpl. constructor.
  - rewrite add_is_next in H. inversion H; subst; clear H.
    apply IHsigma1 in H5. apply IHsigma2 in H6.
    apply add_in_sorted_function in H7.
    subst. reflexivity.
  - rewrite add_is_next. subst. apply Sort_next with (sort_fn sigma1) (sort_fn sigma2).
    + apply IHsigma1. reflexivity.
    + apply IHsigma2. reflexivity.
    + apply add_in_sorted_function. reflexivity.
Qed.

Theorem sort_is_sorted : forall sigma sigmas,
  sort sigma sigmas -> locally_sorted sigmas.
Proof.
  intros.
  induction H; try constructor.
  apply add_in_sorted_sorted with (c, v, js) sigmas; try assumption.
  apply locally_sorted_message_justification; assumption.
Qed.

Theorem sort_sorted_idem : forall sigma,
  locally_sorted sigma -> sort sigma sigma.
Proof.
  intros. induction H.
  - constructor.
  - apply Sort_next with j Empty; try assumption; constructor.
  - apply Sort_next with j (next msg' sigma); try assumption.
    apply add_in_Next_lt; assumption.
Qed.

Theorem sort_total : forall sigma, exists sigmas, sort sigma sigmas.
Proof.
  apply relation_function_total with sort_fn.
  apply sort_function.
Qed.

Theorem sort_functional : forall sigma sigmas1 sigmas2,
  sort sigma sigmas1 ->
  sort sigma sigmas2 ->
  sigmas1 = sigmas2.
Proof.
  apply relation_function_functional with sort_fn.
  apply sort_function.
Qed.

Lemma sort_empty : forall sigma,
  sort sigma Empty -> sigma = Empty.
Proof.
  intros. inversion H; subst; clear H; try reflexivity.
  exfalso.
  inversion H2.
  apply (no_confusion_next_empty msg' sigma' H).
Qed.

Definition message_sort (msg : message) (msgs : message) : Prop :=
  sort (next msg Empty) (next msgs Empty).

Lemma message_sort_construct : forall c v j js,
  sort j js -> message_sort (c, v, j) (c, v, js).
Proof.
  intros.
  unfold message_sort. apply Sort_next with js Empty; try assumption; constructor.
Qed.

Lemma message_sort_destruct : forall msg msgs,
  message_sort msg msgs ->
  exists c v j js, msg = (c,v,j) /\ msgs = (c,v,js) /\ sort j js.
Proof.
  intros.
  inversion H; subst; clear H.
  - exfalso. symmetry in H1. apply (no_confusion_next_empty _ _ H1).
  - rewrite add_is_next in *.
    apply no_confusion_next in H0; destruct H0; subst.
    inversion H2; subst; clear H2.
    apply add_in_empty in H3.
    apply no_confusion_next in H3; destruct H3; subst. clear H0.
    exists c. exists v. exists j. exists js.
    repeat split; try reflexivity.
    assumption.
Qed.

Definition in_state_sorted (msg : message) (sigmas : state) : Prop :=
  exists msgs,  message_sort msg msgs /\ in_state msgs sigmas .

Theorem in_sorted_state_all : forall sigma sigmas,
  sort sigma sigmas ->
  forall msg, in_state msg sigma -> in_state_sorted msg sigmas.
Proof.
  intros sigma sigmas H. unfold in_state_sorted. induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - rewrite in_state_iff in H2.
    destruct H2; subst.
    + exists (c,v,js). split; try assumption.
      * apply message_sort_construct; assumption.
      * apply add_in_sorted_message_preservation with sigmas; assumption.
    + apply IHsort2 in H2.
      destruct H2 as [msgs [Hmsgs Hin]].
      exists msgs. split; try assumption.
      apply (add_in_sorted_state_preservation _ _ _ H1 msgs Hin).
Qed.

Theorem in_sort_state : forall sigma sigmas,
  sort sigma sigmas ->
  forall msgs,
  in_state msgs sigmas ->
  exists msg, message_sort msg msgs /\ in_state msg sigma.
Proof.
  intros sigma sigmas H.
  induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - apply (add_in_sorted_no_junk _ _ _ H1) in H2.
    destruct H2; subst.
    + exists (c, v, j). split.
      * apply message_sort_construct; assumption.
      * left. reflexivity.
    + apply IHsort2 in H2.
      destruct H2 as [js' [Hjs' Hin]].
      exists js'. split; try assumption.
      right. assumption.
Qed.

