Require Import Casper.preamble.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.justifications.


Definition message : Type := C * V * justification.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition consensus_value (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition justify (msg : message) : justification :=
  match msg with (_, _, j) => j end.

Parameter Hash : message -> hash.

Parameter hash_injective : Injective Hash.

Lemma message_eq_dec : forall x y : message, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as [(cx, vx) jx].   destruct y as [(cy, vy) jy].
  destruct (c_eq_dec cx cy); try (right; intro; inversion H; apply n; assumption).
  destruct (v_eq_dec vx vy); try (right; intro; inversion H; apply n; assumption).
  destruct (justification_eq_dec jx jy); try (right; intro; inversion H; apply n; assumption).
  left. subst. reflexivity.
Qed.