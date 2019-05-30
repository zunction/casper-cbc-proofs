(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Parameter C : Set .

Parameter c_non_empty : exists c : C, True.

Parameter c_eq_dec : forall (c1 c2 : C), {c1 = c2} + {c1 <> c2}.
