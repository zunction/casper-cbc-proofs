Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.
Import ListNotations.

From Casper
Require Import preamble.

(** Sorted Lists **)

Inductive list_lex {A} {lt : relation A} : list A -> list A -> Prop :=
  | list_lex_empty : forall h l,
      list_lex nil (cons h l)
  | list_lex_head : forall h1 h2 l1 l2,
      lt h1 h2 -> list_lex (cons h1 l1) (cons h2 l2)
  | list_lex_tail : forall h l1 l2,
      list_lex l1 l2 -> list_lex (cons h l1) (cons h l2)
  .

Fixpoint list_compare {A} (compare : A -> A -> comparison)
    (l1 l2 : list A) : comparison :=
  match l1,l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | (h1 :: t1), (h2 :: t2) => 
    match compare h1 h2 with
    | Eq => @list_compare A compare t1 t2
    | cmp => cmp
    end
  end.

Fixpoint Inb {A} (compare : A -> A -> comparison) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t =>
    match compare a h with
    | Eq => true
    | _ => Inb compare a t
    end
  end.

Lemma compare_in : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  PredicateFunction2 (@In A) (Inb compare).
Proof.
  intros A compare H a l.
  induction l; intros; split; intros.
  - inversion H0.
  - discriminate.
  - inversion H0; subst.
    + simpl. rewrite compare_eq_refl; try apply (proj1 H). reflexivity.
    + simpl. apply IHl in H1; try assumption. rewrite H1.
      destruct (compare a a0); reflexivity.
  - simpl in H0. destruct (compare a a0) eqn:Hcmp.
    + left. symmetry. apply (proj1 H). assumption.
    + right. apply IHl; try assumption.
    + right. apply IHl; try assumption.
Qed.

Lemma compare_not_in : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  forall a l, not (In a l) <-> Inb compare a l = false.
Proof.
  intros. rewrite (compare_in _ compare H a l).
  apply not_true_iff_false.
Qed.

Definition list_lt {A} {compare : A -> A -> comparison} :=
  @compare_lt (list A) (list_compare compare).

Lemma list_lex_lt : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  EqualRelations (@list_lex A (compare_lt compare)) (@list_lt A compare).
Proof.
  intros. intros l1 l2; split; intros. unfold list_lt.
  - induction H0;  unfold compare_lt in *.
    + reflexivity.
    + simpl. rewrite H0. reflexivity.
    + simpl. rewrite (compare_eq_refl _ _ H h). assumption.
  - generalize dependent l2. induction l1; intros; destruct l2; try discriminate.
    + constructor.
    + inversion H0. destruct (compare a a0) eqn:Hcmp; try discriminate.
      * apply H in Hcmp; subst. apply list_lex_tail. apply IHl1. assumption.
      * apply list_lex_head. assumption.
Qed.

Lemma list_compare_strict_order : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  CompareStrictOrder (@list_compare A compare).
Proof.
  intros. destruct H as [R T].
  split.
  - intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
    + simpl in H. destruct (compare a a0) eqn:Hcmp; try discriminate H.
      apply R in Hcmp; subst. apply IHx in H; subst.
      reflexivity.
    + inversion H; subst. simpl. rewrite compare_eq_refl; try assumption.
      apply IHx. reflexivity.
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; inversion H; clear H; destruct (compare a0 a) eqn:Ha0; try discriminate
    ; inversion H0; clear H0; destruct (compare a a1) eqn:Ha1; try discriminate
    ; try apply (IHy _ _ _ H2) in H1; try apply (T _ _ _ _ Ha0) in Ha1
    ; try apply R in Ha0; subst
    ; try (simpl; rewrite Ha1; try rewrite H1, H2; reflexivity)
    ; try (simpl; rewrite Ha1; rewrite H2; reflexivity)
    ; try (apply R in Ha1; subst; simpl;  rewrite Ha0; rewrite H1; reflexivity)
    .
Qed.

Lemma list_lex_strict_order : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare -> StrictOrder (@list_lex A (compare_lt compare)).
Proof.
  intros. apply list_compare_strict_order in H as CSO. destruct H as [R TR]. 
  apply equal_relations_strict_order with (@list_lt A compare).
  - apply equal_relations_symmetric. apply list_lex_lt. assumption.
  - apply compare_lt_strict_order. assumption.
Qed.

Lemma list_lex_total_order : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare -> TotalOrder (@list_lex A (compare_lt compare)).
Proof.
  intros. apply list_compare_strict_order in H as CSO. destruct H as [R TR]. 
  apply equal_relations_total_order with (@list_lt A compare).
  - apply equal_relations_symmetric. apply list_lex_lt. assumption.
  - apply compare_lt_total_order. assumption.
Qed.

Inductive add_in_sorted_list {A} {lt : relation A} : A -> list A -> list A -> Prop :=
   | add_in_nil : forall msg,
          add_in_sorted_list msg nil (msg :: nil)
   | add_in_cons_eq : forall msg sigma,
          add_in_sorted_list msg (msg :: sigma) (msg :: sigma)
   | add_in_cons_lt : forall msg msg' sigma,
          lt msg msg' ->  
          add_in_sorted_list msg (msg' :: sigma) (msg :: msg' :: sigma)
   | add_in_Next_gt : forall msg msg' sigma sigma',
          lt msg' msg ->
          add_in_sorted_list msg sigma sigma' ->
          add_in_sorted_list msg (msg' :: sigma) (msg' :: sigma')
  .

Fixpoint add_in_sorted_list_fn {A} {compare : A -> A -> comparison} (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | h :: t =>
    match compare x h with
    | Lt => x :: h :: t
    | Eq => h :: t
    | Gt => h :: @add_in_sorted_list_fn A compare x t
    end
  end.

Lemma add_in_sorted_list_function : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  RelationFunction2
    (@add_in_sorted_list A (compare_lt compare))
    (@add_in_sorted_list_fn A compare).
Proof.
  intros. intros x xs xxs; split; intros.
  - induction H0.
    + reflexivity.
    + simpl. rewrite compare_eq_refl; try reflexivity. apply (proj1 H).
    + simpl. rewrite H0. reflexivity.
    + simpl. apply compare_asymmetric_intro in H0; try assumption. rewrite H0.
      rewrite IHadd_in_sorted_list. reflexivity.
  - generalize dependent xxs. generalize dependent x. induction xs; intros.
    + simpl in H0; subst. constructor.
    + simpl in H0. destruct (compare x a) eqn:Hcmp; subst.
      * apply (proj1 H) in Hcmp; subst. constructor.
      * constructor. assumption.
      * apply compare_asymmetric_intro in Hcmp; try assumption.
        constructor; try assumption.
        apply IHxs. reflexivity.
Qed.

Corollary add_in_sorted_list_functional : forall A compare,
   CompareStrictOrder compare ->
   forall x l1 l2 l2',
   @add_in_sorted_list A (compare_lt compare) x l1 l2 ->
   @add_in_sorted_list A (compare_lt compare) x l1 l2' ->
   l2 = l2'.
Proof.
  intros.
  apply
    (relation_function2_functional _ _ _ _ 
      (@add_in_sorted_list_fn A compare)
      (add_in_sorted_list_function _ _ H)
      _ _
      l2
    )  in H1; assumption.
Qed.

Theorem add_in_sorted_list_total : forall A compare x l,
  CompareStrictOrder compare ->
  exists l', @add_in_sorted_list A (compare_lt compare) x l l'.
Proof.
  intros.
  apply
    relation_function2_total with (@add_in_sorted_list_fn A compare).
    apply add_in_sorted_list_function.
    assumption.
Qed.

Lemma add_in_sorted_list_no_empty {A} {lt : relation A} : forall msg sigma,
  ~ @add_in_sorted_list A lt msg sigma [].
Proof.
  unfold not. intros.
  inversion H; subst.
Qed.

Theorem add_in_sorted_list_in {A} {lt : relation A} : forall msg msg' sigma sigma',
  @add_in_sorted_list A lt msg sigma sigma' -> 
  In msg' sigma' ->
  msg = msg' \/In msg' sigma.
Proof. 
  intros. induction H; try (right; assumption).
  - destruct H0; inversion H; subst. left. assumption.
  - simpl in H0. simpl. assumption. 
  - simpl. simpl in H0. destruct H0.
    + right. left. assumption.
    + apply IHadd_in_sorted_list in H0. destruct H0.
      * left. assumption.
      * right . right. assumption.
Qed.

Lemma add_in_sorted_list_head {A} {lt : relation A} : forall msg sigma sigma',
  @add_in_sorted_list A lt msg sigma sigma' -> 
  In msg sigma'.
Proof.
  intros.
  induction H
  ; try ( constructor; reflexivity).
  - right. assumption.
Qed.

Lemma add_in_sorted_list_tail {A} {lt : relation A} : forall msg sigma sigma',
  @add_in_sorted_list A lt msg sigma sigma' -> 
  incl sigma sigma'.
Proof.
  intros.
  induction H.
  - constructor. inversion H.
  - apply incl_refl.
  - apply incl_tl. apply incl_refl.
  - apply (incl_tl msg') in IHadd_in_sorted_list.
    assert (Hmsg': In msg' (msg' :: sigma')).
      { constructor. reflexivity. }
    apply (incl_cons Hmsg') in IHadd_in_sorted_list.
    assumption.
Qed.

Lemma add_in_sorted_list_first {A} {lt : relation A} : forall msg a b sigma sigma',
    StrictOrder lt ->
    LocallySorted lt (a :: sigma) ->
    lt a msg ->
    @add_in_sorted_list A lt msg (a :: sigma) (a :: b :: sigma') -> 
    lt a b.
Proof.
  intros. 
  destruct H as [HI HT].
  unfold Transitive in HT.
  unfold Irreflexive in HI. unfold Reflexive in HI. unfold complement in HI.
  inversion H2; subst; try (apply HI in H1; inversion H1).
  inversion H7; subst; try assumption.
  inversion H0; subst. assumption.
Qed.

Theorem add_in_sorted_list_sorted {A} (lt : relation A) : forall msg sigma sigma',
    StrictOrder lt ->
    LocallySorted lt sigma ->
    @add_in_sorted_list A lt msg sigma sigma' -> 
    LocallySorted lt sigma'.
Proof.
  intros msg sigma sigma' SO Hsorted. 
  assert (SO' := SO).
  destruct SO as [HI _].
  unfold Irreflexive in HI. unfold Reflexive in HI. unfold complement in HI.
  generalize dependent msg.
  generalize dependent sigma'. induction Hsorted.
  - intros. inversion H; subst. constructor.
  - intros. inversion H; subst.
    + constructor.
    + constructor; try assumption; try constructor.
    + inversion H5; subst. constructor; try assumption; try constructor.
  - intros. inversion H0; subst.
    + constructor; try assumption.
    + constructor;  try assumption. constructor;  try assumption.
    + apply IHHsorted in H6. inversion H6; subst.
      * constructor.
      * inversion H0; subst ; try (apply HI in H4; inversion H4).
        inversion H8; subst; try constructor; try assumption.
      * assert (LocallySorted lt (a :: b :: l)); try (constructor; assumption).
        apply (add_in_sorted_list_first _ _ _ _ _ SO' H3 H4) in H0.
        constructor; assumption. 
Qed.

(** Sorted lists as sets **)
Definition set_eq {A} (s1 s2 : list A) := incl s1 s2 /\ incl s2 s1.

Theorem set_eq_reflexive {A} : forall (s : list A), set_eq s s.
Proof.
  induction s;split; intro; intro; assumption.
Qed.

Lemma set_In {A}  (lt : relation A) : forall x y s,
  StrictOrder lt ->
  LocallySorted lt (y :: s) ->
  In x s ->
  lt y x.
Proof.
  intros x y s SO LS IN. generalize dependent x. generalize dependent y.
  destruct SO as [_ HT]. unfold Transitive in HT.
  induction s.
  - intros y LS x IN. inversion IN.
  - intros y LS x IN.
    inversion LS; subst.
    inversion IN; subst.
    + assumption.
    + apply (IHs a H1 x) in H.
      apply (HT y a x H3 H).
Qed.

Lemma set_eq_first_equal {A}  (lt : relation A) : forall x1 x2 s1 s2,
  StrictOrder lt ->
  LocallySorted lt (x1 :: s1) ->
  LocallySorted lt (x2 :: s2) ->
  set_eq (x1 :: s1) (x2 :: s2) ->
  x1 = x2 /\ set_eq s1 s2.
Proof.
  intros x1 x2 s1 s2 SO LS1 LS2 SEQ. destruct SEQ as [IN1 IN2].
  assert (SO' := SO). destruct SO' as [IR TR].
  assert (x12 : x1 = x2).
  {
    unfold incl in *. destruct (IN1 x1). { simpl. left. reflexivity. }
    - subst. reflexivity.
    - apply (set_In lt x1 x2 s2 SO LS2) in H.
      destruct (IN2 x2). { simpl. left. reflexivity. }
      * subst. apply IR in H. inversion H.
      * apply (set_In lt x2 x1 s1 SO LS1) in H0.
        apply (TR x1 x2 x1 H0) in H. apply IR in H. inversion H.
  }
  subst.
  split; try reflexivity.
  split; unfold incl.
  - intros. assert (INa1 := H).
    apply (set_In lt _ _ _ SO LS1) in H. 
    destruct (IN1 a).
    { simpl. right. assumption. }
    + subst. apply IR in H. inversion H.
    + assumption.
  - intros. assert (INa2 := H).
    apply (set_In lt _ _ _ SO LS2) in H. 
    destruct (IN2 a).
    { simpl. right. assumption. }
    + subst. apply IR in H. inversion H.
    + assumption.
Qed.

Theorem set_equality_predicate {A}  (lt : relation A) : forall s1 s2,
  StrictOrder lt ->
  LocallySorted lt s1 ->
  LocallySorted lt s2 ->
  set_eq s1 s2 <-> s1 = s2.
Proof.
  intros s1 s2 SO LS1 LS2 . assert (SO' := SO). destruct SO' as [IR TR].
  split. 
  - generalize dependent s2. induction s1; destruct s2.
    + intros. reflexivity.
    + intros. destruct H. exfalso. apply (H0 a). simpl. left. reflexivity.
    + intros. destruct H. exfalso. apply (H a). simpl. left. reflexivity.
    + intros. apply (set_eq_first_equal lt a a0 s1 s2 SO LS1 LS2) in H. destruct H; subst.
      apply Sorted_LocallySorted_iff in LS1. apply Sorted_inv in LS1. destruct LS1 as [LS1 _]. apply Sorted_LocallySorted_iff in LS1.
      apply Sorted_LocallySorted_iff in LS2. apply Sorted_inv in LS2. destruct LS2 as [LS2 _]. apply Sorted_LocallySorted_iff in LS2.
      apply (IHs1 LS1 s2 LS2) in H0. subst. reflexivity.
  - intros. subst. apply set_eq_reflexive.
Qed.