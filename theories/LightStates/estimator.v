Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.states.

(***************)
(** Estimator **)
(***************)

Module Type Estimator
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PHash.

Module PStates := States PCons PVal PHash.
Export PStates.

Parameter estimator : state -> C -> Prop.

Axiom estimator_total : forall s : state, exists c : C, estimator s c.

End Estimator.