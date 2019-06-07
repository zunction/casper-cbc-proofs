Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.

Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.fault_weights.

(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Parameter t : R.

Parameter threshold_nonnegative : (t >= 0)%R .


(*
(** TODO: Can we assume validators' individual weights are below the threshold **)
Parameter validators_beyond_threshold : forall v : V, (weight v <= t)%R.
*)
(**
  NOTE: Because lists are finite (by definition), the assumption below
  states that there exists a finite set of validators whose weight is 
  larger than the threshold.

**)

Parameter byzantine_fault_tolerance :
  exists (vs : list V), NoDup vs /\ (sum_weights vs > t)%R.

Lemma byzantine_fault_tolerance_interval :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > t)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove v_eq_dec v vs) <= t)%R.
  Admitted.