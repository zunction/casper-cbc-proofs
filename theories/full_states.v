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


Notation "'add' ( c , v , msg ) 'to' sigma" :=
  (Next c v msg sigma)
  (at level 20).

(********************)
(* State properties *)
(********************)

Inductive state_lt : state -> state -> Prop :=
  | state_lt_Empty : forall c v j sigma, 
      state_lt Empty (add (c,v,j) to sigma)
  | state_lt_C : forall c1 c2 v1 v2 j1 j2 sigma1 sigma2,
      c_lt c1 c2 ->
      state_lt (add (c1,v1,j1) to sigma1) (add (c2,v2,j2) to sigma2)
  | state_lt_V : forall c v1 v2 j1 j2 sigma1 sigma2,
      v_lt v1 v2 -> 
      state_lt (add (c,v1,j1) to sigma1) (add (c,v2,j2) to sigma2)
  | state_lt_M : forall c v j1 j2 sigma1 sigma2,
      state_lt j1 j2 ->
      state_lt (add (c,v,j1) to sigma1) (add (c,v,j2) to sigma2)
  | state_lt_Next : forall c v j sigma1 sigma2,
      state_lt sigma1 sigma2 ->
      state_lt (add (c,v,j) to sigma1) (add (c,v,j) to sigma2)
  .

Lemma state_lt_irreflexive : Irreflexive state_lt.
Proof.
 assert (SOc : StrictOrder c_lt); try apply c_lt_strict_order.
 assert (SOv : StrictOrder v_lt); try apply v_lt_strict_order. 
 assert (EE : not(state_lt Empty Empty)); try (unfold not; intros; inversion H).
 unfold Irreflexive. unfold Reflexive. induction x.
    + apply EE.
    + unfold complement. intros. inversion H; subst.
      * destruct SOc. 
        apply StrictOrder_Irreflexive in H1. inversion H1.
      * destruct SOv. 
        apply StrictOrder_Irreflexive in H1. inversion H1.
      * apply IHx1 in H1. inversion H1.
      * apply IHx2 in H1. inversion H1.
Qed.

Lemma state_lt_transitive: Transitive state_lt.
Proof.
  assert (SOc : StrictOrder c_lt); try apply c_lt_strict_order.
  assert (SOv : StrictOrder v_lt); try apply v_lt_strict_order.
  destruct SOc as [_ Soc]. 
  destruct SOv as [_ Sov]. 
  unfold Transitive in *.
  intros. generalize dependent x. induction H0.
  - intros. inversion H.
  - intros. inversion H0; subst; try (apply state_lt_C; assumption).
    + constructor.
    + apply state_lt_C; try assumption. apply (Soc _ _ _ H3 H). 
  - intros. inversion H0; subst; try (apply state_lt_V; assumption).
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. apply (Sov _ _ _ H3 H).
  - intros; subst. inversion H; subst.
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. assumption.
    + apply state_lt_M. apply IHstate_lt. assumption.
    + apply state_lt_M. assumption. 
  - intros; subst. inversion H; subst.
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. assumption.
    + apply state_lt_M. assumption.
    + apply state_lt_Next. apply IHstate_lt. assumption.
Qed.

Lemma state_lt_strict_order : StrictOrder state_lt.
Proof.
  constructor.
  - apply state_lt_irreflexive.
  - apply state_lt_transitive.
Qed.

Theorem state_lt_total_order : TotalOrder state_lt.
Proof.
  unfold TotalOrder.
  intros. generalize dependent c2.
  induction c1.
  - induction c2.
    + left. reflexivity.
    + right. left. apply state_lt_Empty.
  - induction c2.
    + right. right. apply state_lt_Empty.
    + destruct (c_lt_total_order c c0); subst.
      * destruct (v_lt_total_order v v0); subst.
        { destruct (IHc1_1 c2_1); subst.
            { destruct (IHc1_2 c2_2); subst.
                { left. reflexivity. }
                { destruct H. 
                    { right. left. apply state_lt_Next. assumption. }
                    { right. right. apply state_lt_Next. assumption. }
                 }
             }
            {  destruct H. 
              { right. left. apply state_lt_M. assumption. }
              { right. right. apply state_lt_M. assumption. }
            }
        }
        { destruct H.
          { right. left. apply state_lt_V.  assumption. }
          { right. right. apply state_lt_V. assumption. }
        } 
     * destruct H.
        { right. left. apply state_lt_C.
          {assumption. }
        }
        { right. right. apply state_lt_C. 
          {assumption. }
        }
Qed.

Corollary state_eq_dec : forall x y : state, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with state_lt.
  - apply state_lt_strict_order.
  - apply state_lt_total_order.
Qed.

