(************************************************************)
(** Consistent Decisions on Properties of Protocol States  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.locally_sorted.

(* work in progress *)

(* Decided properties of protocol states *)

(* note: the states can be considered protocol states, as in the paper *)
(* this version is more general *)
Definition decided (state_prop : state -> Prop) (sigma : state) : Prop :=
  locally_sorted(sigma) ->
  (forall sigma',
      locally_sorted(sigma') ->
      sigma => sigma' ->
      state_prop(sigma')) ->
  state_prop(sigma).

(* Forward consistency *)
Lemma forward_consistency : forall sigma sigma' state_prop,
  protocol_state(sigma) ->
  protocol_state(sigma') ->
  sigma => sigma' ->
  decided state_prop sigma ->
  decided state_prop sigma'.
Admitted.

(* Consistency of properties of protocol states *)
Definition consistent ( state_props : list (state -> Prop)) : Prop :=
  exists sigma,
  protocol_state(sigma) ->
  Forall (fun state_prop => state_prop sigma) state_props.
