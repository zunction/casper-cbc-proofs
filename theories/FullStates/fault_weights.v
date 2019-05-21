Require Import Coq.Reals.Reals.

Require Import Casper.validators.
Require Import Casper.consensus_values.
Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.in_state.

(****************************)
(** Fault Weight of States **)
(****************************)

(**
Note that this includes equivocation fault weight, as we defaulted 
the weight of non-equivocating messages to 0
**)

Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 j1 j2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,j1) (c2,v2,j2) 0
  | fault_weight_c_msg: forall c v j,
      fault_weight_msg (c,v,j) (c,v,j) 0
  | fault_weight_msg1: forall c1 c2 v j1 j2,
      in_state (c1,v,j1) j2 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_msg2: forall c1 c2 v j1 j2,
      in_state (c2,v,j2) j1 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_next: forall c1 c2 v j1 j2,
      c1 <> c2 \/ j1 <> j2 ->
      not (in_state (c1,v,j1) j2) ->
      not (in_state (c2,v,j2) j1) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

Theorem fault_weight_msg_functional : forall msg1 msg2 r1 r2,
  fault_weight_msg msg1 msg2 r1 ->
  fault_weight_msg msg1 msg2 r2 ->
  r1 = r2.
Proof.
  intros. inversion H; subst; clear H; inversion H0; subst; clear H0
  ; try reflexivity
  ; try contradiction.
  - destruct H6; contradiction.
  - destruct H1; contradiction.
Qed.

Theorem fault_weight_msg_total : forall msg1 msg2,
  exists r, fault_weight_msg msg1 msg2 r.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  destruct (v_eq_dec v1 v2).
  - destruct (c_eq_dec c1 c2).
    + destruct (state_eq_dec j1 j2); subst.
      * exists 0%R. apply fault_weight_c_msg.
      * destruct (in_state_dec (c2, v2, j1) j2).
        { exists 0%R. apply fault_weight_msg1. assumption. }
        destruct (in_state_dec (c2, v2, j2) j1).
        { exists 0%R. apply fault_weight_msg2. assumption. }
        exists (weight v2).
        apply fault_weight_next; try assumption.
        right. assumption.
    + subst.
      destruct (in_state_dec (c1, v2, j1) j2).
      { exists 0%R. apply fault_weight_msg1. assumption. }
      destruct (in_state_dec (c2, v2, j2) j1).
      { exists 0%R. apply fault_weight_msg2. assumption. }
      exists (weight v2).
      apply fault_weight_next; try assumption.
      left. assumption.
  - exists 0%R. apply fault_weight_v_diff. assumption.
Qed.

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_Empty: forall msg,
      fault_weight_message_state msg Empty 0
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (next msg2 sigma) (r1 + r2)%R
.

Theorem fault_weight_message_state_functional : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_message_state_total : forall msg sigma,
  exists r, fault_weight_message_state msg sigma r.
Admitted.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_Empty: 
      fault_weight_state Empty 0
  | fault_weight_state_Next: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (next msg sigma) (r1 + r2)%R
.


Theorem fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
Admitted.
