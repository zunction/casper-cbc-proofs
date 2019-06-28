(*******************************)
(** Binary consensus protocol **)
(*******************************)

Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.


Require Import Casper.preamble.

Require Import Casper.FullStates.protocol_states.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.consensus_values.

Require Import Casper.FullStates.latest_honest_estimate_driven_estimator.

(** Concrete parameters **)
Inductive C : Set := 
  | zero:C 
  | one:C
  .

(*
Definition score (c:C) (sigma:state) : R :=
  fold_right Rplus R0  
    (filter (fun v => In c (le sigma v)) (observed sigma))
  .
*)

(*
Definition estimator : state -> C -> Prop :=
  forall sigma,
  match (score zero sigma) (score one sigma) with
    | LT => one
    | GT => zero
    | Eq => 
*)







  