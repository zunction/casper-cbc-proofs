Require Import Coq.Classes.RelationClasses.
Require Import List.

Require Import Casper.preamble.
Require Import Casper.consensus_values.
Require Import Casper.validators.
Require Import Casper.hash.
Require Import Casper.sorted_lists.


Definition message : Set := C * V * list hash.

Parameter Hash : message -> hash.

Definition message_compare (m1 m2 : message) : comparison :=
  match m1,m2 with
    (c1,v1,hs1),(c2,v2,hs2) =>
      match c_compare c1 c2 with
      | Eq =>
        match v_compare v1 v2 with
        | Eq => hash_list_compare hs1 hs2
        | v_cmp => v_cmp
        end
      | c_cmp => c_cmp
      end
  end.

Definition message_lt : message -> message -> Prop := compare_lt message_compare.

Lemma message_compare_strict_order : CompareStrictOrder message_compare.
Proof.
  destruct c_compare_strict_order as [Rc Tc].
  destruct v_compare_strict_order as [Rv Tv].
  destruct hash_list_compare_strict_order as [Rhs Ths].
  split.
  - intros [(c1, v1) hs1]  [(c2, v2) hs2]; split; intro.
    + inversion H. clear H.
      destruct (c_compare c1 c2) eqn: Hc; try discriminate. apply Rc in Hc; subst.
      destruct (v_compare v1 v2) eqn: Hv; try discriminate. apply Rv in Hv; subst.
      apply Rhs in H1; subst. reflexivity.
    + inversion H; subst. simpl.
      rewrite c_compare_refl. rewrite v_compare_refl. rewrite hash_list_compare_refl.
      reflexivity.
  - intros  [(c1, v1) hs1]  [(c2, v2) hs2] [(c3, v3) hs3].
    destruct comp; intros H12 H23; inversion H12; clear H12; inversion H23; clear H23
    ; destruct (c_compare c1 c2) eqn: Hc12; try discriminate
    ; destruct (c_compare c2 c3) eqn: Hc23; try discriminate
    ; destruct (v_compare v1 v2) eqn: Hv12; try discriminate
    ; destruct (v_compare v2 v3) eqn: Hv23; try discriminate
    ; simpl
    ; try rewrite H0
    ; try rewrite H1
    ; try (apply (Tc _ _ _ _ Hc12) in Hc23; rewrite Hc23; reflexivity)
    ; try (apply Rc in Hc12; subst; rewrite Hc23; reflexivity)
    ; try (apply Rc in Hc23; subst; rewrite Hc12; reflexivity)
    ; apply Rc in Hc12; apply Rc in Hc23; subst; rewrite c_compare_refl
    ; try (apply (Tv _ _ _ _ Hv12) in Hv23; rewrite Hv23; reflexivity)
    ; try (apply Rv in Hv12; subst; rewrite Hv23; reflexivity)
    ; try (apply Rv in Hv23; subst; rewrite Hv12; reflexivity)
    ; apply Rv in Hv12; apply Rv in Hv23; subst; rewrite v_compare_refl
    ; apply (Ths _ _ _ _ H0) in H1; rewrite H1; reflexivity
    .
Qed.

Lemma message_compare_refl : forall msg, message_compare msg msg = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 message_compare_strict_order).
Qed.

Definition message_lt_strict_order: StrictOrder message_lt :=
  compare_lt_strict_order message message_compare message_compare_strict_order.

Definition message_lt_total_order: TotalOrder message_lt :=
  compare_lt_total_order message message_compare message_compare_strict_order.

Definition message_eq_dec : EqualityDec message :=
  compare_eq_dec message message_compare message_compare_strict_order.

Lemma message_neq : forall (c1 c2 : C) (v1 v2 : V) (j1 j2 : list hash),
  (c1, v1, j1) <> (c2, v2, j2) <->
  (c1 <> c2 \/ v1 <> v2 \/ j1 <> j2).
Proof.
  intros; split; intros.
  - destruct (message_compare (c1, v1, j1) (c2, v2, j2)) eqn:Hmsg.
    + exfalso. apply H. apply (proj1 message_compare_strict_order).
      assumption.
    + inversion Hmsg; clear Hmsg.
      destruct (c_compare c1 c2) eqn:Hc; try discriminate.
      destruct (v_compare v1 v2) eqn:Hv; try discriminate.
      * right. right. intro. subst. apply compare_eq_lt in H1; try assumption.
        apply (proj1 hash_list_compare_strict_order).
      * right. left. intro. subst. apply compare_eq_lt in Hv; try assumption.
        apply (proj1 v_compare_strict_order).
      * left.  intro. subst. apply compare_eq_lt in Hc; try assumption.
        apply (proj1 c_compare_strict_order).
    + inversion Hmsg; clear Hmsg.
      destruct (c_compare c1 c2) eqn:Hc; try discriminate.
      destruct (v_compare v1 v2) eqn:Hv; try discriminate.
      * right. right. intro. subst. apply compare_eq_gt in H1; try assumption.
        apply (proj1 hash_list_compare_strict_order).
      * right. left. intro. subst. apply compare_eq_gt in Hv; try assumption.
        apply (proj1 v_compare_strict_order).
      * left.  intro. subst. apply compare_eq_gt in Hc; try assumption.
        apply (proj1 c_compare_strict_order).
  - intro. inversion H0; subst. clear H0. destruct H as [H | [H | H]]; apply H; reflexivity.
Qed.
  