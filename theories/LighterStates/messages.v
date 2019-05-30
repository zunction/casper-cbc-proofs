Require Import Casper.LighterStates.consensus_values.
Require Import Casper.LighterStates.validators.
Require Import Casper.LighterStates.hashes.


Definition message : Type := C * V * justification.

Definition validator (msg : message) : V :=
  match msg with (_, v, _) => v end.

Parameter Hash : message -> hash.

