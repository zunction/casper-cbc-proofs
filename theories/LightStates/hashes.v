Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.ListSetExtras.

(*******************)
(** Hash universe **)
(*******************)

Parameter hash : Set .

Parameter hash_eq_dec : forall (h1 h2 : hash), {h1 = h2} + {h1 <> h2}.

Definition justification := set hash.

Definition justification_in := set_mem hash_eq_dec.

Definition justification_eq := @set_eq hash.

Lemma justification_eq_dec : forall (hs1 hs2 : justification), {hs1 = hs2} + {hs1 <> hs2}.
Proof.
  intros. apply list_eq_dec. apply hash_eq_dec.
Qed.