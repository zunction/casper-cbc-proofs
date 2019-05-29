Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.
Require Import Casper.sorted_lists.


(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)



(** Parameters of the protocol **)

Require Import Casper.consensus_values.
Require Import Casper.validators.
Require Import Casper.threshold.
Require Import Casper.hash.

(** Messages **)

Require Import Casper.LightStates.messages.


(************)
(** States **)
(************)

Require Import Casper.LightStates.states.

Require Import Casper.LightStates.hash_state.

(***************)
(** Estimator **)
(***************)

Parameter estimator : state -> C -> Prop.

Parameter estimator_total : forall s : state, exists c : C, estimator s c.

(********************)
(* State properties *)
(********************)

Definition state_sorted : state -> Prop := LocallySorted message_lt.


Require Import Casper.LightStates.fault_weights.


(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The valid message condition **)

Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state_fn sigma <= t)%R.


(** TODO? Define protocol messages; also for the full version? **)

Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state []
  | protocol_state_cons : forall c v sigma hsigma sigma' sigma'',
      protocol_state sigma ->
      protocol_state sigma' ->
      valid_estimate_condition c sigma ->
      hash_state sigma hsigma ->
      @add_in_sorted_list message message_lt (c, v, hsigma) sigma' sigma'' ->
      fault_tolerance_condition sigma'' ->
      protocol_state sigma''
.

Theorem protocol_state_sorted : forall state,
  protocol_state state -> LocallySorted message_lt state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_list_sorted message_lt (c,v,hsigma) sigma'); try assumption.
    apply message_lt_strict_order.
Qed.

Theorem protocol_state_message_sorted : forall c v hs state,
  protocol_state state ->
  In (c,v,hs) state ->
  LocallySorted hash_lt hs.
Proof.
  intros.
  induction H.
  - inversion H0.
  - apply (add_in_sorted_list_in (c0, v0, hsigma) (c, v, hs) sigma' sigma'' H4) in H0.
    destruct H0.
    + inversion H0; subst. apply (hash_state_sorted sigma). assumption.
    + apply IHprotocol_state2. assumption.
Qed.
