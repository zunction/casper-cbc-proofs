Require Import Coq.Classes.RelationClasses.
Require Import List.

Require Import Casper.consensus_values.
Require Import Casper.validators.
Require Import Casper.hash.
Require Import Casper.sorted_lists.


Definition message : Set := C * V * list hash.

Parameter Hash : message -> hash.

Definition message_lt (m1 : message) (m2 : message) : Prop :=
  match m1,m2 with
    (c1,v1,hs1),(c2,v2,hs2) =>
      c_lt c1 c2 \/ (c1 = c2 /\ (v_lt v1 v2 \/ (v1 = v2 /\ hash_lex hs1 hs2))) 
  end.

Lemma message_lt_storder : StrictOrder message_lt.
Proof.
  assert (SOc : StrictOrder c_lt); try apply c_lt_strict_order.
  assert (SOv : StrictOrder v_lt); try apply v_lt_strict_order.
  assert (SOh : StrictOrder hash_lt); try apply hash_lt_strict_order.
  assert (SOhs : StrictOrder hash_lex); try apply (list_lex_storder hash hash_lt SOh).
  constructor.
  - unfold Irreflexive. unfold Reflexive. destruct x as [(c, v) h]. intro.
    destruct H.
    + destruct SOc. unfold Irreflexive in *. unfold Reflexive in *.
      apply (StrictOrder_Irreflexive c H).
    + destruct H. destruct H0.
      * destruct SOv. unfold Irreflexive in *. unfold Reflexive in *.
      apply (StrictOrder_Irreflexive v H0).
      * destruct H0.
        destruct SOhs. unfold Irreflexive in *. unfold Reflexive in *.
        apply (StrictOrder_Irreflexive h H1).
  - unfold Transitive.
    destruct SOc as [_ Soc].
    destruct SOv as [_ Sov].
    destruct SOhs as [_ Sohs].
    destruct x as [(cx, vx) hx].
    destruct y as [(cy, vy) hy].
    destruct z as [(cz, vz) hz].
    simpl. intros Hxy Hyz. 
    destruct Hxy as [Hxyc | [Hxyc [Hxyv | [Hxyv Hxyh]]]]; destruct Hyz as [Hyzc | [Hyzc [Hyzv | [Hyzv Hyzh]]]]
     ; subst
     ; try (left; assumption)
     ; try (right; split; auto; left; assumption).
    + left. apply (Soc _ _ _ Hxyc Hyzc).
    + right; split; auto; left. apply (Sov _ _ _ Hxyv Hyzv).
    + right; split; auto; right; split; auto.
       apply (Sohs _ _ _ Hxyh Hyzh).
Qed.


Module MessageOrder <: TotalLeBool.
  Definition t := nat.
  Fixpoint leb x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => leb x' y'
    end.
  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
End NatOrder.
