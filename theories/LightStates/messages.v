Require Import Casper.preamble.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.justifications.

Module Messages
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PHash : Hash)
        .

Import PCons.
Import PVal.
Import PHash.

Module PJustifications := Justifications PHash.
Export PJustifications.

Definition message : Type := C * V * justification_type.

Definition estimate (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : justification_type :=
  match msg with (_, _, j) => j end.

Lemma message_eq_dec : forall x y : message, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as [(cx, vx) jx].   destruct y as [(cy, vy) jy].
  destruct (c_eq_dec cx cy); try (right; intro; inversion H; apply n; assumption).
  destruct (v_eq_dec vx vy); try (right; intro; inversion H; apply n; assumption).
  destruct (justification_eq_dec jx jy); try (right; intro; inversion H; apply n; assumption).
  left. subst. reflexivity.
Qed.

End Messages.


