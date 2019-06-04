Require Import Coq.Classes.RelationClasses.

From Casper
Require Import preamble.

From Casper
Require Import consensus_values.

From Casper
Require Import validators.



(************)
(** States **)
(************)

Inductive state : Set :=
  | Empty : state
  | Next : C ->  V -> state -> state -> state.


Notation "'add' ( c , v , j ) 'to' sigma" :=
  (Next c v j sigma)
  (at level 20).

(********************)
(* State properties *)
(********************)

Fixpoint state_compare (sigma1 sigma2 : state) : comparison :=
  match sigma1, sigma2 with
  | Empty, Empty => Eq
  | Empty, _ => Lt
  | _, Empty => Gt
  | add (c1, v1, j1) to sigma1, add (c2, v2, j2) to sigma2 =>
    match c_compare c1 c2 with
    | Eq =>
      match v_compare v1 v2 with
      | Eq =>
        match state_compare j1 j2 with
        | Eq => state_compare sigma1 sigma2
        | cmp_j => cmp_j
        end
      | cmp_v => cmp_v
      end
    | cmp_c => cmp_c
    end
  end.

Lemma state_compare_reflexive : CompareReflexive state_compare.
Proof.
  destruct c_compare_strict_order as [Rc _].
  destruct v_compare_strict_order as [Rv _].
  intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
  - simpl in H.
    destruct (c_compare c c0) eqn:Hcmp; try discriminate.
    apply Rc in Hcmp; subst.
    destruct (v_compare v v0) eqn:Hcmp; try discriminate.
    apply Rv in Hcmp; subst.
    destruct (state_compare x1 y1) eqn:Hcmp; try discriminate.
    apply IHx1 in Hcmp. apply IHx2 in H. subst.
    reflexivity.
  - inversion H; subst. simpl.
    rewrite compare_eq_refl; try apply Rc.
    rewrite compare_eq_refl; try apply Rv.
    assert (state_compare y1 y1 = Eq). { apply IHx1. reflexivity. }
    assert (state_compare y2 y2 = Eq). { apply IHx2. reflexivity. }
    rewrite H0. assumption.
Qed.

Lemma state_compare_transitive : CompareTransitive state_compare.
Proof.
  destruct c_compare_strict_order as [Rc Tc].
  destruct v_compare_strict_order as [Rv Tv].
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; simpl
    ; inversion H; clear H
    ; destruct (c_compare c0 c) eqn:Hc0; try discriminate
    ; inversion H0; clear H0
    ; destruct (c_compare c c1) eqn:Hc1; try discriminate
    ; try (apply (Tc c0 c c1 _ Hc0) in Hc1 ; rewrite Hc1; reflexivity)
    ; try (apply Rc in Hc0; subst; rewrite Hc1; try reflexivity)
    ; try (apply Rc in Hc1; subst; rewrite Hc0; try reflexivity)
    ; destruct (v_compare v0 v) eqn:Hv0; try discriminate
    ; destruct (v_compare v v1) eqn:Hv1; try discriminate
    ; try (apply (Tv v0 v v1 _ Hv0) in Hv1; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv0; subst; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv1; subst; rewrite Hv0; try reflexivity)
    ; destruct (state_compare x1 y1) eqn:Hj0; try discriminate
    ; destruct (state_compare y1 z1) eqn:Hj1; try discriminate
    ; try (apply (IHy1 x1 z1 _ Hj0) in Hj1; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj0; subst; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj1; subst; rewrite Hj0; try reflexivity)
    ; try rewrite H1; try rewrite H2
    ; try (apply (IHy2 x2 z2 _ H2) in H1; rewrite H1; try reflexivity)
    .
Qed.

Lemma state_compare_strict_order : CompareStrictOrder state_compare.
Proof.
  split.
  - apply state_compare_reflexive.
  - apply state_compare_transitive.
Qed.

Definition state_lt := compare_lt state_compare.

Definition state_lt_irreflexive : Irreflexive state_lt :=
  compare_lt_irreflexive state state_compare state_compare_reflexive.

Definition state_lt_transitive: Transitive state_lt :=
  compare_lt_transitive state state_compare state_compare_transitive.

Definition state_lt_strict_order: StrictOrder state_lt :=
  compare_lt_strict_order state state_compare state_compare_strict_order.

Definition state_lt_total_order: TotalOrder state_lt :=
  compare_lt_total_order state state_compare state_compare_strict_order.

Definition state_eq_dec : forall x y : state, {x = y} + {x <> y} :=
  compare_eq_dec state state_compare state_compare_strict_order.
