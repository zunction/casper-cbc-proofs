Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.states.

(***************)
(** Estimator **)
(***************)

Module Type Estimator
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        .

Import PCons.
Import PVal.
Import PVal_Weights.

Module PStates := States PCons PVal.
Export PStates.

Parameter estimator : state -> C -> Prop.

Axiom estimator_total : forall s : state, exists c : C, estimator s c.

End Estimator.
