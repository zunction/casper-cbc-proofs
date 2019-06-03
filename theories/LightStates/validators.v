Require Import Coq.Reals.Reals.

(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Parameter V : Set .

Parameter v_non_empty : exists v : V, True.

Parameter v_eq_dec : forall (v1 v2 : V), {v1 = v2} + {v1 <> v2}.

(***********************)
(** Validator weights **)
(***********************)

Parameter weight : V -> R.

Parameter weight_positive : forall v : V, (0 < weight v)%R.
