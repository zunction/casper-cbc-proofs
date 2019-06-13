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

Definition message_eq (msg1 msg2 : message) : Prop :=
  match msg1, msg2 with 
    (c1, v1, j1), (c2, v2,j2) => 
      c1 = c2 /\ v1 = v2 /\ justification_eq j1 j2
  end.

Lemma message_eq_dec : forall (msg1 msg2 : message), {message_eq msg1 msg2} + {~ message_eq msg1 msg2}.
Proof.
  destruct msg1 as [(c1, v1) j1]. destruct msg2 as [(c2, v2) j2].
  destruct (c_eq_dec c1 c2).
  - subst. destruct (v_eq_dec v1 v2).
    + subst. destruct (justification_eq_dec j1 j2).
      * left. simpl. split; try reflexivity. split; try reflexivity. assumption.
      * right. intro. simpl in H. destruct H as [_ [_ Heq]]. apply n. assumption.
    + right. intro.  simpl in H. destruct H as [_ [Heq _]]; subst. apply n. reflexivity.
  - right. intro. inversion H; subst. apply n. reflexivity.
Qed.
