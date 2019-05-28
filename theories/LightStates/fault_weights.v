Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

Require Import Casper.validators.
Require Import Casper.hash.
Require Import Casper.sorted_lists.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.


Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 j1 j2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,j1) (c2,v2,j2) 0
  | fault_weight_c_msg: forall c v j,
      fault_weight_msg (c,v,j) (c,v,j) 0
  | fault_weight_msg1: forall c1 c2 v j1 j2,
      In (Hash (c1,v,j1)) j2 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_msg2: forall c1 c2 v j1 j2,
      In (Hash (c2,v,j2)) j1 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_next: forall c1 c2 v j1 j2,
      c1 <> c2 ->
      j1 <> j2 ->
      not (In (Hash (c1,v,j1)) j2) ->
      not (In (Hash (c2,v,j2)) j1) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

Lemma fault_weight_msg_equal : forall msg w,
  fault_weight_msg msg msg w -> w = 0%R.
Proof.
  intros. inversion H; subst; try reflexivity.
  exfalso. apply H2. reflexivity.
Qed.

Lemma fault_weight_msg_neq_v : forall c1 c2 v1 v2 j1 j2 w,
  v1 <> v2 ->
  fault_weight_msg (c1,v1,j1) (c2,v2,j2) w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H. reflexivity.
Qed.

Lemma fault_weight_msg_in1 :forall msg1 c2 v2 j2 w,
  In (Hash msg1) j2 ->
  fault_weight_msg msg1 (c2,v2,j2) w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H8. assumption.
Qed.

Lemma fault_weight_msg_in2 :forall c1 v1 j1 msg2 w,
  In (Hash msg2) j1 ->
  fault_weight_msg (c1,v1,j1) msg2 w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H9. assumption.
Qed.

Fixpoint fault_weight_msg_fn (msg1 msg2 : message) : R :=
  match message_compare msg1 msg2 with
  | Eq => 0%R
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match v_compare v1 v2 with
      | Eq =>
        match hash_list_in (Hash msg1) j2 with
        | true => 0%R
        | false =>
          match hash_list_in (Hash msg2) j1 with
          | true => 0%R
          | false => weight v1
          end
        end
      | _ => 0%R
      end
    end
  end.

Lemma fault_weight_msg_function : forall msg1 msg2 w,
  fault_weight_msg msg1 msg2 w <-> fault_weight_msg_fn msg1 msg2 = w.
Proof.
  intros [(c1, v1) j1] [(c2, v2) j2] w; split; intros; simpl.
  - destruct (message_eq_dec (c1, v1, j1) (c2, v2,j2)) eqn:Hc.
    + rewrite e in H. 
      apply (proj1 message_compare_strict_order) in e as Heq.
      simpl in Heq. rewrite Heq.
      apply fault_weight_msg_equal in H. subst. reflexivity.
Admitted.

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_nil: forall msg,
      fault_weight_message_state msg [] 0
  | fault_weight_message_state_cons: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (msg2 :: sigma) (r1 + r2)%R
.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_nil: 
      fault_weight_state [] 0
  | fault_weight_state_cons: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (msg :: sigma) (r1 + r2)%R
.
