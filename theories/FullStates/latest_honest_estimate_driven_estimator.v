Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.threshold.
Require Import Casper.FullStates.fault_weights.


Module Type Latest_Honest_Estimate
              (PCons : Consensus_Values) 
              (PVal : Validators)
              (PStates : States PCons PVal)
              (PMessages : Messages PCons PVal PStates)
              (PIn_State : In_State PCons PVal PStates PMessages)
              (PLocally_Sorted : Locally_Sorted PCons PVal PStates PMessages PIn_State)
              (PFault_Weights : Fault_Weights PCons PVal PStates PMessages PIn_State PLocally_Sorted)
              (PThreshold : Threshold PCons PVal PStates PMessages PIn_State PLocally_Sorted PFault_Weights)
              .

(* import the Module parameters in order to have access to 
   its parameters without having to use the DotNotation. *)
Import PCons.
Import PVal.
Import PStates.
Import PMessages.
Import PIn_State.
Import PLocally_Sorted.
Import PFault_Weights.
Import PThreshold.

(** Observed validators in a state **)
(** note: since a state is finite then there is a finite
    set of observed validators **)
Definition observed (sigma:state) : list V :=
  set_map v_eq_dec sender (get_messages sigma)
  .

(* Observed as predicate
Definition observed (sigma:state) (v:V) : Prop :=
  exists msg, in_state msg sigma /\ sender msg = v.
*)

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
Definition le (sigma:state) : V -> list C :=
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

End Latest_Honest_Estimate.






