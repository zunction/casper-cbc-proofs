Require Import Coq.Lists.ListSet.
Require Import List.
Import ListNotations.


Lemma eq_dec_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall v,
  exists n, Aeq_dec v v = left n.
Proof.
  intros.  destruct (Aeq_dec v v) eqn:Hv.
  - exists e. reflexivity.
  - exfalso. apply n. reflexivity.
Qed.


Lemma eq_dec_right {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x y,
  x <> y ->
  exists n, Aeq_dec x y = right n.
Proof.
  intros.  destruct (Aeq_dec x y) eqn:Hv.
  - exfalso. apply H. assumption.
  - exists n. reflexivity.
Qed.

Definition set_eq {A} (s1 s2 : set A) : Prop :=
  incl s1 s2 /\ incl s2 s1.

Lemma set_eq_comm {A} : forall s1 s2 : set A,
  set_eq s1 s2 <-> set_eq s2 s1.
Proof.
  intros; split; intro; destruct H; split; assumption.
Qed.

Lemma set_eq_tran {A} : forall s1 s2 s3 : set A,
  set_eq s1 s2 ->
  set_eq s2 s3 ->
  set_eq s1 s3.
Proof.
  intros. split; apply incl_tran with s2; apply H || apply H0.
Qed.

Lemma set_eq_cons {A} : forall (a : A) (s1 s2 : set A),
  set_eq s1 s2 ->
  set_eq (a :: s1) (a :: s2).
Proof.
  intros. split; intros x Hin; destruct Hin; subst
  ; (left; reflexivity) || (right; apply H; assumption).
Qed.

Lemma set_union_comm {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  set_eq (set_union Aeq_dec s1 s2) (set_union Aeq_dec s2 s1).
Proof.
  intros; split; intro x; intros; apply set_union_iff in H; apply set_union_iff; destruct H;
  (left ; assumption) || (right; assumption).
Qed.

Lemma set_union_empty {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  set_union Aeq_dec s1 s2 = nil ->
  s1 = nil /\ s2 = nil
  .
Proof.
  intros.
  destruct s2.
  - destruct (set_union_comm Aeq_dec s1 nil). rewrite H in H1. destruct s1.
    + split; reflexivity.
    + simpl in H1. destruct (H1 a). apply set_add_intro. left. reflexivity.
  - simpl in H. assert (@incl A nil nil); try apply incl_refl.
    rewrite <- H in H0 at 1. destruct (H0 a). apply set_add_intro. left. reflexivity.
Qed.

Lemma set_union_incl_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  incl s1 (set_union Aeq_dec s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  left; assumption.
Qed.

Lemma set_union_incl_right {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  incl s2 (set_union Aeq_dec s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  right; assumption.
Qed.

Lemma set_union_incl_iterated {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall ss s,
  In s ss ->
  incl s (fold_right (set_union Aeq_dec) nil ss).
Proof.
  induction ss; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. apply set_union_incl_left.
    + apply IHss in H. apply incl_tran with (fold_right (set_union Aeq_dec) [] ss); try assumption.
      apply set_union_incl_right.
Qed.

(* 
Lemma set_union_assoc {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2 s3,
  set_union Aeq_dec (set_union Aeq_dec s1 s2) s3
  = set_union Aeq_dec s1 (set_union Aeq_dec s2 s3).
  Admitted.


Lemma set_union_singleton {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
   set_union Aeq_dec [x] s = set_add Aeq_dec x s.
Proof.
  intros.
  Admitted.


Lemma set_add_last {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall x s,
  ~ In x s ->
  set_add Aeq_dec x s = s ++ [x].
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. apply not_in_cons in H. destruct H. rewrite IHs; try assumption.
    destruct (eq_dec_right Aeq_dec x a H). rewrite H1. reflexivity.
Qed.
 *)

Lemma set_union_empty_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s,
  NoDup s ->
  set_eq (set_union Aeq_dec nil s) s.
Proof.
  intros. split; intros x Hin.
  - apply set_union_elim in Hin. destruct Hin.
    + inversion H0.
    + assumption.
  - apply set_union_intro. right. assumption.
Qed.

Lemma set_map_nodup {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s,
  NoDup (set_map Aeq_dec f s).
Proof.
  induction s; simpl; try constructor.
  apply set_add_nodup. assumption.
Qed.

Lemma set_map_in {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall x s,
  In x s ->
  In (f x) (set_map Aeq_dec f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - apply set_add_intro2. reflexivity.
  - apply set_add_intro1. apply IHs. assumption.
Qed.

Lemma set_map_incl {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s s',
  incl s s' ->
  incl (set_map Aeq_dec f s) (set_map Aeq_dec f s').
Proof.
  induction s; intros; intro msg; intros.
  - inversion H0.
  - simpl in H0. apply set_add_elim in H0. destruct H0.
    + subst. apply set_map_in. apply H. left. reflexivity.
    + apply IHs; try assumption. intros x; intros. apply H. right. assumption.
Qed.

Lemma set_remove_not_in {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
  ~ In x s ->
  set_remove Aeq_dec x s = s.
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. apply not_in_cons in H.  destruct H.
    destruct (eq_dec_right Aeq_dec x a H). rewrite H1.
    rewrite (IHs H0). reflexivity.
Qed.

Lemma set_remove_first {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x y s,
  x = y -> set_remove Aeq_dec x (y::s) = s.
Proof.
  intros. destruct (Aeq_dec x y) eqn:Hcmp; simpl; rewrite Hcmp; try reflexivity.
  exfalso. apply n. assumption.
Qed.

Lemma set_remove_nodup_1 {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
  NoDup (set_remove Aeq_dec x s) ->
  ~ In x (set_remove Aeq_dec x s) ->
  NoDup s.
Proof.
  induction s; intros.
  - constructor.
  - simpl in H0 . destruct (Aeq_dec x a). 
    + subst. simpl in H. destruct (eq_dec_left Aeq_dec a). rewrite H1 in H. constructor; assumption.
    + apply not_in_cons in H0. destruct H0. simpl in H.
      destruct (eq_dec_right Aeq_dec x a H0).
    rewrite H2 in H. inversion H; subst; clear H.
    constructor; try apply IHs; try assumption.
    intro. apply H5. apply set_remove_3; try assumption. intro; subst. apply H0; reflexivity.
Qed.

Lemma set_eq_remove {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 ->
  set_eq (set_remove Aeq_dec x s1) (set_remove Aeq_dec x s2).
Proof.
  intros. 
  destruct H1. split; intros a Hin
  ; apply set_remove_iff; try assumption
  ; apply set_remove_iff in Hin; try assumption; destruct Hin
  ; split; try assumption
  .
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma incl_remove_union  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  incl
    (set_remove Aeq_dec x (set_union Aeq_dec s1 s2))
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
  .
Proof.
  intros. intros y Hin. apply set_remove_iff in Hin.
  - apply set_union_intro. destruct Hin. apply set_union_elim in H1.
    destruct H1; try (left; assumption).
    right. apply set_remove_3; assumption.
  - apply set_union_nodup; assumption.
Qed.

Lemma set_eq_remove_union_in  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  In x s1 ->
  set_eq
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
    (set_union Aeq_dec s1 s2)
  .
Proof.
  split; intros msg Hin; apply set_union_iff; apply set_union_iff in Hin
  ; destruct Hin; try (left; assumption)
  .
  - apply set_remove_iff in H2; try assumption. destruct H2. right. assumption.
  - destruct (Aeq_dec msg x).
    + subst. left. assumption.
    + right. apply set_remove_iff; try assumption. split; assumption.
Qed.

Lemma set_eq_remove_union_not_in  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  ~ In x s1 ->
  set_eq
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
    (set_remove Aeq_dec x (set_union Aeq_dec s1 s2))
  .
Proof.
  intros.
  assert (HnodupUs1s2 := H0).
  apply (set_union_nodup Aeq_dec H) in HnodupUs1s2.
  split; intros msg Hin.
  - apply set_remove_iff; try assumption.
    apply set_union_iff in Hin.
    destruct Hin; split.
    + apply set_union_iff. left. assumption.
    + intro; subst. apply H1. assumption.
    + apply set_remove_iff in H2; try assumption.
      destruct H2. apply set_union_iff. right. assumption.
    + intro; subst.
      apply set_remove_iff in H2; try assumption.
      destruct H2. apply H3. reflexivity.
  - apply set_union_iff; try assumption.
    apply set_remove_iff in Hin; try assumption.
    destruct Hin. apply set_union_iff in H2.
    destruct H2; try (left; assumption).
    right. apply set_remove_iff; try assumption.
    split; assumption.
Qed.

Unset Implicit Arguments.
