Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Class TotalOrder {A} (lt : relation A) : Prop :=
   totality : forall c1 c2, c1 = c2 \/ lt c1 c2 \/ lt c2 c1.

Theorem strict_total_order_eq_dec : forall (A : Type) (rel : A -> A -> Prop),
  StrictOrder rel ->
  TotalOrder rel ->
  forall x y : A, x = y \/ x <> y.
Proof.
  intros.
  destruct H.
  destruct (H0 x y) as [Heq | [H | H]]
  ; try (left; assumption)
  ; try (right; intro; subst; apply (StrictOrder_Irreflexive _ H); assumption)
  .
Qed.

