Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.consensus_values.
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
      c1 <> c2 \/ j1 <> j2 ->
      not (In (Hash (c1,v,j1)) j2) ->
      not (In (Hash (c2,v,j2)) j1) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

Lemma fault_weight_msg_equal : forall msg w,
  fault_weight_msg msg msg w -> w = 0%R.
Proof.
  intros. inversion H; subst; try reflexivity.
  exfalso. destruct H2 as [H2 | H2]; apply H2; reflexivity.
Qed.

Lemma fault_weight_msg_neq_v : forall c1 c2 v1 v2 j1 j2 w,
  v1 <> v2 ->
  fault_weight_msg (c1,v1,j1) (c2,v2,j2) w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H. reflexivity.
Qed.

Lemma fault_weight_msg_in2 :forall msg1 c2 v2 j2 w,
  In (Hash msg1) j2 ->
  fault_weight_msg msg1 (c2,v2,j2) w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H7. assumption.
Qed.

Lemma fault_weight_msg_in1 :forall c1 v1 j1 msg2 w,
  In (Hash msg2) j1 ->
  fault_weight_msg (c1,v1,j1) msg2 w ->
  w = 0%R.
Proof.
  intros. inversion H0; subst; try reflexivity.
  exfalso. apply H8. assumption.
Qed.

Lemma fault_weight_msg_defined :forall c1 v j1 c2 j2 w,
  fault_weight_msg (c1,v,j1) (c2, v, j2) w ->
  ~ In (Hash (c2, v, j2)) j1 ->
  ~ In (Hash (c1, v, j1)) j2 ->
  c1 <> c2 \/ j1 <> j2 ->
  w = weight v.
Proof.
  intros. inversion H; subst; clear H; try reflexivity
  ; exfalso.
  - apply H10; reflexivity.
  - destruct H2 as [H | H]; apply H; reflexivity.
  - apply H1. apply H9.
  - apply H0. apply H9.
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
  intros [(c1, v1) j1] [(c2, v2) j2] w; simpl; split; intros
  ; destruct (c_compare c1 c2) eqn:Hc
  ; destruct (v_compare v1 v2) eqn:Hv
  ; destruct (hash_list_in (Hash (c1, v1, j1)) j2) eqn:Hin2
  ; destruct (hash_list_in (Hash (c2, v2, j2)) j1) eqn:Hin1
  ; destruct (hash_list_compare j1 j2) eqn:Hj
  ; ( apply compare_lt_neq in Hv
    || apply compare_gt_neq in Hv
    || apply (proj1 v_compare_strict_order) in Hv
    )
  ; ( apply compare_lt_neq in Hc
    || apply compare_gt_neq in Hc
    || apply (proj1 c_compare_strict_order) in Hc
    )
  ; ( apply compare_lt_neq in Hj
    || apply compare_gt_neq in Hj
    || apply (proj1 hash_list_compare_strict_order) in Hj
    )
  ; (apply hash_list_compare_in in Hin1 || apply hash_list_compare_not_in in Hin1)
  ; (apply hash_list_compare_in in Hin2 || apply hash_list_compare_not_in in Hin2)
  ; subst
  ; try apply (proj1 v_compare_strict_order)
  ; try apply (proj1 c_compare_strict_order)
  ; try (apply (proj1 hash_list_compare_strict_order))
  ; try
    ( try (apply fault_weight_msg_equal in H; subst; reflexivity)
    ; try (apply fault_weight_msg_in1 in H; subst; try reflexivity; assumption)
    ; try (apply fault_weight_msg_in2 in H; subst; try reflexivity; assumption)
    ; try (apply fault_weight_msg_neq_v in H; subst; (reflexivity || assumption))
    ; symmetry
    ; apply (fault_weight_msg_defined _ _ _ _ _ _ H Hin1 Hin2)
    ; try (right; assumption)
    ; left; assumption
    )
  ; try (apply fault_weight_c_msg; assumption)
  ; try (apply fault_weight_v_diff; assumption)
  ; try (apply fault_weight_msg1; assumption)
  ; try (apply fault_weight_msg2; assumption)
  ; apply fault_weight_next
  ; try assumption
  ; try (right; assumption)
  ; left; assumption
  .
Qed.

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_nil: forall msg,
      fault_weight_message_state msg [] 0
  | fault_weight_message_state_cons: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (msg2 :: sigma) (r1 + r2)%R
.

Definition fault_weight_message_state_fn (msg : message) (sigma : state) : R :=
  fold_right (fun r1 r2 => (r1 + r2)%R) 0%R (map (fault_weight_msg_fn msg) sigma).

Lemma fault_weight_message_state_function : forall msg sigma w,
  fault_weight_message_state msg sigma w
  <->
  fault_weight_message_state_fn msg sigma = w
  .
Proof.
  induction sigma; intros; unfold fault_weight_message_state_fn; split; intros.
  - inversion H. reflexivity.
  - simpl in H; subst. constructor.
  - inversion H; subst. apply fault_weight_msg_function in H5.
    apply IHsigma in H3.
    simpl.  rewrite H5. 
    unfold fault_weight_message_state_fn in H3. rewrite H3.
    apply Rplus_comm.
  - simpl in H. subst. rewrite Rplus_comm. constructor.
    + apply IHsigma. reflexivity.
    + apply fault_weight_msg_function. reflexivity.
Qed.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_nil: 
      fault_weight_state [] 0
  | fault_weight_state_cons: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (msg :: sigma) (r1 + r2)%R
.
