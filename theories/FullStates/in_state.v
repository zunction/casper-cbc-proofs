Require Import List.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.messages.

Module In_State
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PEstimator : Estimator PCons PVal)
        .

Import PCons.
Import PVal.
Import PEstimator.

Module PMessages := Messages PCons PVal PEstimator.
Export PMessages.


(** Syntactic membership predicate **)
Definition in_state (msg : message) (sigma : state) : Prop :=
  In msg (get_messages sigma).

Definition syntactic_state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  incl (get_messages sigma1) (get_messages sigma2).

Lemma in_empty_state : forall msg,
  ~ in_state msg Empty.
Proof.
  intros. intro. inversion H.
Qed.

Lemma in_state_dec : forall msg sigma, 
  {in_state msg sigma} + {~ in_state msg sigma}.
Proof.
  intros. apply in_dec. apply message_eq_dec.
Qed.

Lemma in_state_dec_if_true {A} : forall msg sigma (T E : A),
  in_state msg sigma ->
  (if in_state_dec msg sigma then T else E) = T.
Proof.
  intros. destruct (in_state_dec msg sigma); try reflexivity.
  exfalso. apply n. apply H.
Qed.

Lemma in_state_dec_if_false {A} : forall msg sigma (T E : A),
  ~ in_state msg sigma ->
  (if in_state_dec msg sigma then T else E) = E.
Proof.
  intros. destruct (in_state_dec msg sigma); try reflexivity.
  exfalso. apply H. apply i.
Qed.

Definition in_state_fn  (msg : message) (sigma : state) : bool :=
  match in_state_dec msg sigma with
  | left _ => true
  | right _ => false
  end.

Lemma in_state_function : PredicateFunction2 in_state in_state_fn.
Proof.
  intros msg sigma; split; intro; destruct (in_state_dec msg sigma) eqn:Hin;
  unfold in_state_fn in *.
  - rewrite Hin. reflexivity.
  - exfalso; apply n; apply H.
  - assumption.
  - exfalso. rewrite Hin in H. discriminate.
Qed.

Lemma in_state_iff : forall msg msg1 sigma1,
  in_state msg (next msg1 sigma1) <-> msg1 = msg \/ in_state msg sigma1.
Proof.
  unfold in_state. intros. rewrite get_messages_next. simpl.
  split; intros; destruct H; (left; assumption) || (right; assumption).
Qed.

Lemma in_singleton_state : forall msg msg',
  in_state msg (next msg' Empty) -> msg = msg'.
Proof.
  intros. apply in_state_iff in H.
  destruct H; subst; try reflexivity.
  exfalso. apply (in_empty_state _ H).
Qed.

End In_State.