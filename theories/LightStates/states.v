Require Import Bool.
Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.hash_function.
Require Import Casper.LightStates.messages.

(** Hash sets **)

Module States 
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PHash : Hash)
        (PHash_function : Hash_function PCons PVal PHash)
        .

Import PCons.
Import PVal.
Import PHash.
Import PHash_function.

Module PMessages := Messages PCons PVal PHash.
Export PMessages.

Module PValidators_Properties := Validators_Properties PVal.
Import PValidators_Properties.

Definition state := set message.

Definition state_empty := empty_set message.

Definition state_add := set_add message_eq_dec.

Definition state_remove := set_remove message_eq_dec.

Definition state_in := set_mem message_eq_dec.

Definition state_union := set_union message_eq_dec.

Lemma state_eq_dec : forall (sigma1 sigma2 : state), {sigma1 = sigma2} + {sigma1 <> sigma2}.
Proof.
  intros. apply list_eq_dec. apply message_eq_dec.
Qed.

(** More properties of messages **)

(** Messages from a sender in a state **)
Definition from_sender (v:V) (sigma:state) : list message :=
  filter (fun msg' => v_eq_fn (sender msg') v) sigma.

(** Later messages for a message and a sender in a state **)
Definition later_from (msg:message) (v:V) (sigma:state) : list message :=
  filter 
    (fun msg' => (justification_in (Hash msg) (justification msg')) && 
                 (v_eq_fn (sender msg') v))
    sigma
  .

(*
(** Later messages for a message and a sender in a state **)
Definition later_from (msg:message) (v:V) (sigma:state) : list message :=
  filter 
    (fun msg' => (in_state_fn msg (justification msg')) && 
                 (v_eq_fn (sender msg') v))
    (get_messages sigma)
  .

(** Latest messages from senders in a state **)
(** note: there cannot be duplicates in the result **)
Definition latest_messages (sigma:state) : V -> list message :=
  fun v => filter 
            (fun msg => is_nil_fn (later_from msg v sigma))
            (from_sender v sigma)
  .

(** Latest estimates from senders in a state **)
(** note: there can be duplicates in the result **)
Definition latest_estimates (sigma:state) : V -> list C :=
  fun v => set_map c_eq_dec estimate (latest_messages sigma v)
  .

Definition validators_latest_estimates (c:C) (sigma:state) : list V :=
    filter (fun v => in_fn c_eq_dec c (latest_estimates sigma v)) (observed sigma)
  .
*)
End States.