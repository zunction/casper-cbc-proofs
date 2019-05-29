Require Import Coq.Classes.RelationClasses.
Require Import List.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.consensus_values.
Require Import Casper.validators.
Require Import Casper.full_states.

(**************)
(** Messages **)
(**************)

Definition message := (C * V * state)%type.

Fixpoint get_messages (sigma : state) : list message :=
  match sigma with
  | Empty => []
  | add (c, v, j) to sigma' => (c,v,j) :: get_messages sigma'
  end.


Definition next (msg : message) (sigma : state) : state :=
  match msg with
  | (c, v, j) => add (c, v, j) to sigma
  end.

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

Definition msg_lt (msg1 msg2 : message) : Prop :=
  state_lt (next msg1 Empty) (next msg2 Empty).

Corollary msg_lt_irreflexive : Irreflexive msg_lt.
Proof.
  unfold Irreflexive. unfold Reflexive.
  destruct x as [(c, v) j].
  unfold complement. intros.
  unfold msg_lt in H. unfold next in H.
  apply state_lt_irreflexive in H. inversion H.
Qed.

Corollary msg_lt_transitive: Transitive msg_lt.
Proof.
  unfold Transitive.
  destruct x as [(c1, v1) j1].
  destruct y as [(c2, v2) j2].
  destruct z as [(c3, v3) j3].
  unfold msg_lt. unfold next.
  intros.
  apply state_lt_transitive with (add (c2, v2, j2)to Empty); assumption.
Qed.

Lemma msg_lt_strict_order : StrictOrder msg_lt.
Proof.
  constructor.
  - apply msg_lt_irreflexive.
  - apply msg_lt_transitive.
Qed.

Corollary msg_lt_total_order: TotalOrder msg_lt.
Proof.
  unfold TotalOrder. 
  unfold msg_lt.
  destruct c1 as [(c1, v1) j1].
  destruct c2 as [(c2, v2) j2].
  unfold next.
  destruct (c_lt_total_order c1 c2); subst.
  + destruct (v_lt_total_order v1 v2); subst.
    * destruct (state_lt_total_order j1 j2); subst.
      { left. reflexivity. }
      { destruct H.
          { right. left. apply state_lt_M; try reflexivity || assumption. }
          { right. right. apply state_lt_M; try reflexivity || assumption. }
      }
    * destruct H.
      { right. left. apply state_lt_V; try reflexivity || assumption. }
      { right. right. apply state_lt_V; try reflexivity || assumption. }
  + destruct H.
    * right. left. apply state_lt_C; try assumption.
    * right. right. apply state_lt_C; try assumption.
Qed.

Corollary message_eq_dec : forall x y : message, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with msg_lt.
  - apply msg_lt_strict_order.
  - apply msg_lt_total_order.
Qed.

