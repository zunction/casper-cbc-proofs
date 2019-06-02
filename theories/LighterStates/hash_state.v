Require Import Coq.Lists.ListSet.

Require Import Casper.LighterStates.hashes.
Require Import Casper.LighterStates.messages.
Require Import Casper.LighterStates.states.

Definition hash_state : state -> justification :=
  set_map hash_eq_dec Hash.
