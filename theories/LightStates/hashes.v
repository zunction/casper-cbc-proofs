Require Import Casper.preamble.


(*******************)
(** Hash universe **)
(*******************)

Module Type Hash.

Parameter hash : Set .

Parameter hash_compare : hash -> hash -> comparison.

(** hash totally ordered **)

Axiom hash_compare_strict_order : CompareStrictOrder hash_compare.

End Hash.


(*********************)
(** Hash properties **)
(*********************)

Module Hash_Properties
        (PHash : Hash)
        .

Import PHash.

Definition hash_lt := compare_lt hash_compare.

Definition hash_lt_strict_order :=   compare_lt_strict_order hash hash_compare hash_compare_strict_order.

Lemma hash_compare_refl : forall h, hash_compare h h = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 hash_compare_strict_order).
Qed.

Definition hash_eq_dec : forall x y : hash, {x = y} + {x <> y} :=
  compare_eq_dec hash hash_compare hash_compare_strict_order.

End Hash_Properties.