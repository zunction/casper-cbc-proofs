Require Import List.

Require Import Coq.Reals.Reals.

(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Parameter t : R.

Parameter threshold_nonnegative : (t >= 0)%R .
