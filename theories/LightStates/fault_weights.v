Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

Require Import Casper.validators.
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
      not (In (Hash (c2,v,j2)) j2) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

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
