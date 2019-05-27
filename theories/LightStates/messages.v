Require Import Coq.Classes.RelationClasses.
Require Import List.

Require Import Casper.preamble.
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

Lemma message_lt_strict_order : StrictOrder message_lt.
Proof.
  assert (SOc : CompareStrictOrder c_compare); try apply c_compare_strict_order.
  assert (SOv : CompareStrictOrder v_compare); try apply v_compare_strict_order.
  assert (SOh : CompareStrictOrder hash_compare); try apply hash_compare_strict_order.
  assert (SOhs : StrictOrder hash_lex); try apply hash_lex_strict_order.
  constructor.
  - unfold Irreflexive. unfold Reflexive. destruct x as [(c, v) h]. intro.
    destruct H.
    + destruct SOc. unfold Irreflexive in *. unfold Reflexive in *.
      apply compare_lt_irreflexive in H; assumption.
    + destruct H. destruct H0.
      * destruct SOv. unfold Irreflexive in *. unfold Reflexive in *.
        apply compare_lt_irreflexive in H0; assumption. 
      * destruct H0.
        destruct SOhs. unfold Irreflexive in *. unfold Reflexive in *.
        apply (StrictOrder_Irreflexive h H1).
  - unfold Transitive.
    destruct c_lt_strict_order as [_ Soc].
    destruct v_lt_strict_order as [_ Sov].
    destruct hash_lex_strict_order as [_ Sohs].
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

