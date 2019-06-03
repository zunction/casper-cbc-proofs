Require Import Coq.Lists.ListSet.

Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.

Definition hash_state : state -> justification :=
  set_map hash_eq_dec Hash.
