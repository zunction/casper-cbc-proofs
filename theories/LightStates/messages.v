Require Import Casper.preamble.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.


Definition message : Type := C * V * justification.

Definition validator (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition consensus_value (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition justify (msg : message) : justification :=
  match msg with (_, _, j) => j end.

Parameter Hash : message -> hash.

Parameter hash_injective : Injective Hash.

Lemma message_eq_dec : forall (msg1 msg2 : message), {msg1 = msg2} + {msg1 <> msg2}.
Proof.
  destruct msg1 as [(c1, v1) j1]. destruct msg2 as [(c2, v2) j2].
  destruct (c_eq_dec c1 c2).
  - subst. destruct (v_eq_dec v1 v2).
    + subst. destruct (justification_eq_dec j1 j2).
      * subst. left. reflexivity.
      * right. intro. inversion H; subst. apply n. reflexivity.
    + right. intro. inversion H; subst. apply n. reflexivity.
  - right. intro. inversion H; subst. apply n. reflexivity.
Qed.
