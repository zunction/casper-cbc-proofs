Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.
(** Parameters of the protocol **)

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.threshold.


(** Messages and States **)

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.fault_weights.


(** Observed validators in a state **)
Definition observed (sigma:state) (v:V) : Prop :=
  exists msg, in_state msg sigma /\ sender msg = v.

(** Later messages for a message in a state **)
Definition later (msg:message) (sigma:state) : list message :=
  filter (fun msg' => in_state_fn msg (justification msg'))
    (get_messages sigma).

(** Messages from a sender in a state **)
Definition from_sender (v:V) (sigma:state) : list message :=
  filter (fun msg' => v_eq_fn (sender msg') v)
    (get_messages sigma).

(** Messages from a finite group of senders in a state **)
Definition from_group (vs:list V) (sigma:state) : list message :=
  filter (fun msg' => in_fn v_eq_dec (sender msg') vs)
    (get_messages sigma).

(** Later messages for a message and a sender in a state **)
Definition later_from (msg:message) (v:V) (sigma:state) : list message :=
  filter 
    (fun msg' => (in_state_fn msg (justification msg')) && 
                 (v_eq_fn (sender msg') v))
    (get_messages sigma)
  .

(** -------------------- **)
(** Latest messages from senders in a state **)
(** note: there cannot be duplicates in the result **)
Definition lm (sigma:state) : V -> list message :=
  fun v => filter 
            (fun msg => is_nil_fn (later_from msg v sigma))
            (from_sender v sigma)
  .

(** Latest message driven estimator **)
Definition latest_message_driven (estimator : state -> C -> Prop) : Prop :=
  exists estimator',
    forall sigma c,
    estimator sigma c = estimator' (lm sigma)
  .
(** -------------------- **)

(** -------------------- **)
(** Latest estimates from senders in a state **)
(** note: there can be duplicates in the result **)
Definition le (sigma:state) : V -> set C :=
  fun v => set_map c_eq_dec estimate (lm sigma v)
  .

(** Latest estimate driven estimator **)
Definition latest_estimate_driven (estimator : state -> C -> Prop) : Prop :=
  exists estimator',
    forall sigma c,
    estimator sigma c = estimator' (le sigma)
  .
(** -------------------- **)

(** -------------------- **)
(** Latest messages from non-equivocating senders in a state **)
Definition lmh (sigma:state) : V -> list message :=
  fun v => match in_fn v_eq_dec v (equivocating_senders sigma) with
            | true => []
            | false => lm sigma v
           end.

(** Latest honest message driven estimator **)
Definition latest_honest_message_driven (estimator : state -> C -> Prop) : Prop :=
  exists estimator',
    forall sigma c,
    estimator sigma c = estimator' (lmh sigma)
  .
(** -------------------- **)

(** -------------------- **)
(** Latest estimates from non-equivocating senders in a state **)
Definition leh (sigma:state) : V -> set C :=
  fun v => set_map c_eq_dec estimate (lmh sigma v)
  .

(** Latest honest estimate driven estimator **)
Definition latest_honest_estimate_driven (estimator : state -> C -> Prop) : Prop :=
  exists estimator',
    forall sigma c,
    estimator sigma c = estimator' (leh sigma)
  .

(** -------------------- **)








