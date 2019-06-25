Require Import Coq.Classes.RelationClasses.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.states.

(**************)
(** Messages **)
(**************)

Definition message := (C * V * state)%type.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Fixpoint get_messages (sigma : state) : list message :=
  match sigma with
  | Empty => []
  | add (c, v, j) to sigma' => (c,v,j) :: get_messages sigma'
  end.

Definition state_in (msg : message) (sigma : state) : Prop :=
  In msg (get_messages sigma).

Definition next (msg : message) (sigma : state) : state :=
  match msg with
  | (c, v, j) => add (c, v, j) to sigma
  end.

Lemma get_messages_next : forall msg sigma,
  get_messages (next msg sigma) = msg :: get_messages sigma.
Proof.
  destruct msg as [(c, v) j]. simpl. reflexivity.
Qed.

Lemma add_is_next : forall c v j sigma,
  add (c, v, j)to sigma = next (c, v, j) sigma.
Proof.
  intros. unfold next. reflexivity.
Qed.

Lemma no_confusion_next : forall msg1 msg2 sigma1 sigma2,
  next msg1 sigma1 = next msg2 sigma2 ->
  msg1 = msg2 /\ sigma1 = sigma2.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  inversion H; subst; clear H.
  split; reflexivity.
Qed.

Lemma no_confusion_next_empty : forall msg sigma,
  next msg sigma <> Empty.
Proof.
  intros. intro. destruct msg as [(c, v) j]. inversion H.
Qed.

Definition message_compare  (msg1 msg2 : message) : comparison :=
  state_compare (next msg1 Empty) (next msg2 Empty).

Lemma message_compare_strict_order : CompareStrictOrder message_compare.
Proof.
  split.
  - intros msg1 msg2. unfold message_compare.
    rewrite (state_compare_reflexive (next msg1 Empty) (next msg2 Empty)).
    split; intros; subst; try reflexivity.
    apply no_confusion_next in H. destruct H. assumption.
  - intros msg1 msg2 msg3. unfold message_compare. apply state_compare_transitive.
Qed.

Lemma message_compare_reflexive : forall msg,
  message_compare msg msg = Eq.
Proof.
  intros. apply (proj1 message_compare_strict_order). reflexivity.
Qed.

Definition message_compare_asymmetric : CompareAsymmetric message_compare :=
  compare_asymmetric_intro message message_compare message_compare_strict_order.

Definition message_lt := compare_lt message_compare.

Definition message_lt_irreflexive : Irreflexive message_lt :=
  compare_lt_irreflexive message message_compare (proj1 message_compare_strict_order).

Definition message_lt_transitive: Transitive message_lt :=
  compare_lt_transitive message message_compare (proj2 message_compare_strict_order).

Definition message_lt_strict_order: StrictOrder message_lt :=
  compare_lt_strict_order message message_compare message_compare_strict_order.

Definition message_lt_total_order: TotalOrder message_lt :=
  compare_lt_total_order message message_compare message_compare_strict_order.

Definition message_eq_dec : forall x y : message, {x = y} + {x <> y} :=
  compare_eq_dec message message_compare message_compare_strict_order.

Definition messages_union : set message -> set message -> set message :=
  set_union message_eq_dec.
