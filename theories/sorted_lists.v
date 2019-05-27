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

Fixpoint list_eqb {A} {eqb : A -> A -> bool}
    (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [], [] => true
  | (h1 :: t1), (h2 :: t2) => @list_eqb A eqb t1 t2 && eqb h1 h2
  | _,_ => false
  end.

Lemma list_eqb_eq : forall A (eqb : A -> A -> bool),
  EqualityFn eqb ->
  EqualityFn (@list_eqb A eqb).
Proof.
  intros.
  split.
  - generalize dependent y. induction x; intros; destruct y.
    + reflexivity.
    + simpl in H0. discriminate H0.
    + simpl in H0. discriminate H0.
    + inversion H0.
      rewrite andb_true_iff in H2. destruct H2.
      apply IHx in H1; subst. apply H in H2; subst.
      reflexivity.
  - intros. subst. induction y.
    + reflexivity.
    + simpl. rewrite IHy. simpl.  rewrite (H a). reflexivity.
Qed.

Fixpoint list_lexb {A} {eqb : A -> A -> bool} {ltb : A -> A -> bool}
    (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [], (h :: l) => true
  | (h1 :: t1), (h2 :: t2) => 
      if eqb h1 h2
        then @list_lexb A eqb ltb t1 t2
        else  (if ltb h1 h2 then true
              else false)
  | _,_ => false
  end.

Lemma list_lex_storder : forall A lt,
  StrictOrder lt -> StrictOrder (@list_lex A lt).
Proof.
  intros. destruct H. constructor.
  - unfold Irreflexive in *. unfold Reflexive in *. intros. intro.
    induction x; inversion H; subst.
    + apply (StrictOrder_Irreflexive a H1).
    + apply IHx. assumption.
  - unfold Transitive in *. intros. generalize dependent x. induction H0.
    + intros. inversion H.
    + intros. inversion H0; subst.
      * constructor.
      * apply (StrictOrder_Transitive _ _ _ H3) in H.
        apply list_lex_head. assumption.
      * apply list_lex_head. assumption.
    + intros. inversion H; subst.
      * constructor.
      * apply list_lex_head. assumption.
      * apply list_lex_tail. apply (IHlist_lex _ H3).
Qed.

Lemma list_lex_total : forall A lt,
  TotalOrder lt -> TotalOrder (@list_lex A lt).
Proof.
  intros. unfold TotalOrder in *. intros.
  generalize dependent c2. induction c1; destruct c2.
  - left. reflexivity.
  - right; left. constructor.
  - right; right. constructor.
  - destruct (H a a0) as [H1 | [H2 |H3]].
    + subst. destruct (IHc1 c2) as [IH1 | [ IH2 | IH3]].
      * subst. left. reflexivity.
      * right; left. apply list_lex_tail. assumption.
      * right; right. apply list_lex_tail. assumption.
    + right; left. apply list_lex_head. assumption.
    + right; right. apply list_lex_head. assumption.
Qed.

Lemma list_lex_lexb : forall A lt eqb ltb,
  EqualityFn eqb ->
  Irreflexive lt ->
  RelationFn lt ltb ->
  forall l1 l2, @list_lex A lt l1 l2 <-> @list_lexb A eqb ltb l1 l2 = true.
Proof.
  intros; split; intros.
  - induction H2.
    + reflexivity.
    + apply H1 in H2 as Hlt. simpl. destruct (eqb h1 h2) eqn: Heqb. 
      * exfalso. apply H in Heqb; subst. apply (H0 h2 H2).
      * rewrite Hlt. reflexivity.
    + simpl.
      assert (eqb h h = true).
      { apply H. reflexivity. }
      rewrite H3. assumption.
  - generalize dependent l2. induction l1; intros; destruct l2.
    + discriminate H2.
    + constructor.
    + discriminate H2.
    + inversion H2. destruct (eqb a a0) eqn: Heqb.
      * apply H in Heqb; subst. apply list_lex_tail. apply IHl1. assumption.
      * destruct (ltb a a0) eqn: Hltb; try discriminate .
        apply H1 in Hltb.
        apply list_lex_head.
        assumption.
Qed.

Inductive add_in_sorted {A} {lt : relation A} : A -> list A -> list A -> Prop :=
   | add_in_nil : forall msg,
          add_in_sorted msg nil (msg :: nil)
   | add_in_cons_eq : forall msg sigma,
          add_in_sorted msg (msg :: sigma) (msg :: sigma)
   | add_in_cons_lt : forall msg msg' sigma,
          lt msg msg' ->  
          add_in_sorted msg (msg' :: sigma) (msg :: msg' :: sigma)
   | add_in_Next_gt : forall msg msg' sigma sigma',
          lt msg' msg ->
          add_in_sorted msg sigma sigma' ->
          add_in_sorted msg (msg' :: sigma) (msg' :: sigma')
  .

Fixpoint add_in_sorted_fn {A} {eqb ltb : A -> A -> bool} (x : A) (l : list A) : list A :=
  match xs with
  | [] => [x]
  | h :: t =>
    if eqb x h then h :: t
    else if 

Theorem add_in_sorted_functional : forall A lt x l1 l2 l2',
   StrictOrder lt ->
   @add_in_sorted A lt x l1 l2 ->
   @add_in_sorted A lt x l1 l2' ->
   l2 = l2'.
Proof.
  intros A lt x l1 l2 l2' SO. assert (SO' := SO). destruct SO' as [IR TR]. 
  generalize dependent x. generalize dependent l2. generalize dependent l2'.
  induction l1; intros l2' l2 x Add Add'.
  - inversion Add; subst. inversion Add'; subst. reflexivity.
  - inversion Add; inversion Add'; subst; try reflexivity.
    + destruct (IR a H7).
    + destruct (IR a H6).
    + destruct (IR a H3).
    + destruct (IR a (TR a x a H7 H3)).
    + destruct (IR a H2).
    + destruct (IR a (TR a x a H2 H9)).
    + apply (IHl1 _ _ _ H4) in H10. subst. reflexivity.
Qed.

Theorem add_in_sorted_total : forall A lt x l,
  TotalOrder lt ->
  exists l', @add_in_sorted A lt x l l'.
Proof.
  intros. generalize dependent x.
  induction l.
  - intros. exists [x]. constructor.
  - intros. destruct (H a x) as [Heq | [LTax | LTxa]].
    + subst. exists (x :: l). constructor.
    + destruct (IHl x). exists (a :: x0). constructor; assumption.
    + exists (x :: a :: l). constructor. assumption.
Qed.

Theorem add_in_sorted_in {A} {lt : relation A} : forall msg msg' sigma sigma',
  @add_in_sorted A lt msg sigma sigma' -> 
  In msg' sigma' ->
  msg = msg' \/In msg' sigma.
Proof. 
  intros. induction H; try (right; assumption).
  - destruct H0; inversion H; subst. left. assumption.
  - simpl in H0. simpl. assumption. 
  - simpl. simpl in H0. destruct H0.
    + right. left. assumption.
    + apply IHadd_in_sorted in H0. destruct H0.
      * left. assumption.
      * right . right. assumption.
Qed.

Lemma add_in_sorted_first {A} {lt : relation A} : forall msg a b sigma sigma',
    StrictOrder lt ->
    LocallySorted lt (a :: sigma) ->
    lt a msg ->
    @add_in_sorted A lt msg (a :: sigma) (a :: b :: sigma') -> 
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

Theorem add_in_sorted_sorted {A} (lt : relation A) : forall msg sigma sigma',
    StrictOrder lt ->
    LocallySorted lt sigma ->
    @add_in_sorted A lt msg sigma sigma' -> 
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
        apply (add_in_sorted_first _ _ _ _ _ SO' H3 H4) in H0.
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