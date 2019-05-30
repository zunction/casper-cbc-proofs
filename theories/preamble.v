Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Reals.

Require Import List.
Import ListNotations.


Inductive fold_rel {A B:Type} (rel : A -> B -> B -> Prop) (def : B) : list A -> B -> Prop :=
  | fold_empty : fold_rel rel def [] def
  | fold_cons : forall a l fl fal,
    fold_rel rel def l fl ->
    rel a fl fal ->
    fold_rel rel def (a :: l) fal
  .


Definition reduce_rel {A:Type} (rel : A -> A -> A -> Prop) (l : list A) (r : A) : Prop :=
  match l with
  | [] => False
  | a :: t => fold_rel rel a t r
  end.

Inductive filter_rel {A:Type} (p : A -> Prop) : list A -> list A -> Prop :=
  | filter_empty : filter_rel p [] []
  | filter_cons_p : forall a t t',
    filter_rel p t t' ->
    p a ->
    filter_rel p (a :: t) (a :: t')
  | filter_cons_not_p : forall a t t',
    filter_rel p t t' ->
    ~p a ->
    filter_rel p (a :: t) t'
  .

Lemma Forall_tail : forall A (a:A) l P,
  Forall P (a :: l) -> Forall P l.
Proof.
  intros. inversion H. assumption.
Qed.

Class PredicateFunction {A} (r : A -> Prop) (r_fn : A -> bool) : Prop :=
  predicate_function : forall a, r a <-> r_fn a = true.

Lemma predicate_function_neg : forall A  (r : A -> Prop) (r_fn : A -> bool),
  PredicateFunction r r_fn ->
  forall a, ~ r a <-> r_fn a = false.
Proof.  intros. rewrite (H a).   apply not_true_iff_false. Qed.

Lemma predicate_function_decidable : forall A  (r : A -> Prop) (r_fn : A -> bool),
  PredicateFunction r r_fn ->
  forall a, r a \/ ~r a.
Proof.
  intros. destruct (r_fn a) eqn:Hr.
  - left. apply H. assumption.
  - right. apply (predicate_function_neg _ _ _ H). assumption.
Qed.

Class PredicateFunction2 {A B} (r : A -> B -> Prop) (r_fn : A -> B -> bool) : Prop :=
  predicate_function2 : forall a b, r a b <-> r_fn a b = true.

Lemma predicate_function2_neg : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, ~ r a b <-> r_fn a b = false.
Proof.  intros. rewrite (H a b).   apply not_true_iff_false. Qed.

Lemma predicate_function2_decidable : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, r a b \/ ~r a b.
Proof.
  intros. destruct (r_fn a b) eqn:Hr.
  - left. apply H. assumption.
  - right. apply (predicate_function2_neg _ _ _ _ H). assumption.
Qed.

Class RelationFunction {A B} (r : A -> B -> Prop) (r_fn : A -> B) : Prop :=
  relation_function : forall a b, r a b <-> r_fn a = b.

Lemma relation_function_neg : forall A B (r : A -> B -> Prop) (r_fn : A -> B),
  RelationFunction r r_fn ->
  forall a b, ~ r a b <-> r_fn a <> b.
Proof.
  intros; split; intros.
  - intro. apply H0. apply H. assumption.
  - intro. apply H in H1. rewrite H1 in H0. apply H0. reflexivity.
Qed.

Lemma relation_function_total : forall A B (r : A -> B -> Prop) (r_fn : A -> B),
  RelationFunction r r_fn ->
  forall a, exists b, r a b.
Proof.
  intros. exists (r_fn a). apply H. reflexivity.
Qed.

Lemma relation_function_functional : forall A B (r : A -> B -> Prop) (r_fn : A -> B),
  RelationFunction r r_fn ->
  forall a b1 b2, r a b1 -> r a b2 -> b1 = b2.
Proof.
  intros. apply H in H0. apply H in H1. subst. reflexivity.
Qed.

Lemma filter_rel_function : forall A (p : A -> Prop) (f : A -> bool),
  PredicateFunction p f ->
  RelationFunction (filter_rel p) (filter f).
Proof. unfold RelationFunction.
  intros A p f H l; induction l; intros; split; intros.
  - inversion H0; subst. reflexivity.
  - simpl in H0; subst. constructor.
  - inversion H0; subst; clear H0; apply IHl in H3; simpl; rewrite H3; clear H3;
    (apply H in H5 || apply (predicate_function_neg _ _ _ H) in H5)
    ; rewrite H5; reflexivity.
  - simpl in H0. destruct (f a) eqn:Hfa; subst
    ; (apply H in Hfa || apply (predicate_function_neg _ _ _ H) in Hfa)
    ; (apply filter_cons_p || apply filter_cons_not_p); try assumption
    ; apply IHl
    ; reflexivity
    .
Qed.

Class RelationFunction2 {A B C} (r : A -> B -> C -> Prop) (r_fn : A -> B -> C) : Prop :=
  relation_function2 : forall a b c, r a b c <-> r_fn a b = c.

Lemma relation_function2_neg : forall A B C (r : A -> B -> C -> Prop) (r_fn : A -> B -> C),
  RelationFunction2 r r_fn ->
  forall a b c, ~ r a b c <-> r_fn a b <> c.
Proof.
  intros; split; intros.
  - intro. apply H0. apply H. assumption.
  - intro. apply H in H1. rewrite H1 in H0. apply H0. reflexivity.
Qed.

Lemma relation_function2_total : forall A B C (r : A -> B -> C -> Prop) (r_fn : A -> B -> C),
  RelationFunction2 r r_fn ->
  forall a b, exists c, r a b c.
Proof.
  intros. exists (r_fn a b). apply H. reflexivity.
Qed.

Lemma relation_function2_functional : forall A B C (r : A -> B -> C -> Prop) (r_fn : A -> B -> C),
  RelationFunction2 r r_fn ->
  forall a b c1 c2, r a b c1 -> r a b c2 -> c1 = c2.
Proof.
  intros. apply H in H0. apply H in H1. subst. reflexivity.
Qed.

Lemma fold_rel_function :
  forall A B (rel : A -> B -> B -> Prop)  (rel_fn : A -> B -> B) def,
    RelationFunction2 rel rel_fn ->
    RelationFunction (fold_rel rel def) (fold_right rel_fn def).
Proof.
  intros. intro l. induction l; intro r; split; intros.
  - inversion H0; subst. reflexivity.
  - simpl in H0; subst. constructor.
  - inversion H0; subst; clear H0; apply IHl in H3; simpl; rewrite H3; clear H3;
    (apply H in H5 || apply (predicate_function_neg _ _ _ H) in H5)
    ; rewrite H5; reflexivity.
  - simpl in H0.  remember (fold_right rel_fn def l). apply IHl in Heqb as Hfold.
    apply H in H0. subst. apply fold_cons with (fold_right rel_fn def l); assumption.
Qed.

Class TotalOrder {A} (lt : relation A) : Prop :=
   totality : forall c1 c2, c1 = c2 \/ lt c1 c2 \/ lt c2 c1.

Class Commutative {A} (op : A -> A -> A -> Prop) : Prop :=
   commutativity : forall c1 c2 c12, op c1 c2 c12 -> op c2 c1 c12.

Class CompareReflexive {A} (compare : A -> A -> comparison) : Prop :=
    compare_eq : forall x y, compare x y = Eq <-> x = y.

Lemma compare_eq_refl : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  forall x, compare x x = Eq.
Proof. intros. apply H. reflexivity. Qed.

Lemma compare_eq_lt : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  forall x, ~compare x x = Lt.
Proof. 
  intros.
  assert (compare x x = Eq); try apply (compare_eq_refl _ _ H). rewrite H0.
  intro. discriminate.
Qed.

Lemma compare_lt_neq : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  forall x y, compare x y = Lt -> x <> y.
Proof. 
  intros. intro. subst. apply (compare_eq_lt _ _ H y H0).
Qed.

Lemma compare_eq_gt : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  forall x, ~compare x x = Gt.
Proof. 
  intros.
  assert (compare x x = Eq); try apply (compare_eq_refl _ _ H). rewrite H0.
  intro. discriminate.
Qed.

Lemma compare_gt_neq : forall A (compare : A -> A -> comparison),
  CompareReflexive compare ->
  forall x y, compare x y = Gt -> x <> y.
Proof. 
  intros. intro. subst. apply (compare_eq_gt _ _ H y H0).
Qed.

Class CompareTransitive {A} (compare : A -> A -> comparison) : Prop :=
    compare_transitive : forall x y z comp,
      compare x y = comp ->
      compare y z = comp ->
      compare x z = comp.

Class CompareStrictOrder {A} (compare : A -> A -> comparison) : Prop :=
    compare_strict_order :
      CompareReflexive compare /\
      CompareTransitive compare.

Class CompareAsymmetric {A} (compare : A -> A -> comparison) : Prop :=
    compare_asymmetric : forall x y, compare x y = Lt <-> compare y x = Gt.

Class EqualityDec (A : Type) : Prop :=
    equality_dec : forall x y : A, x = y \/ x <> y.

Class EqualRelations {A} (r1 r2 : relation A) : Prop :=
    equal_relations : forall x y, r1 x y <-> r2 x y.

Lemma equal_relations_symmetric : forall A, Symmetric (@EqualRelations A).
Proof.
  unfold EqualRelations.
  intros A r1 r2 H12 x y; split; intros; apply H12; assumption.
Qed.

Lemma equal_relations_strict_order : forall A (r1 r2 : relation A),
  EqualRelations r1 r2 ->
  StrictOrder r1 ->
  StrictOrder r2.
Proof.
  intros. destruct H0 as [IR TR]. split.
  - intros x H2. apply (IR x). apply H. assumption.
  - intros x y z H1 H2. apply H. apply (TR x y z); apply H; assumption.
Qed.

Lemma equal_relations_total_order : forall A (r1 r2 : relation A),
  EqualRelations r1 r2 ->
  TotalOrder r1 ->
  TotalOrder r2.
Proof.
  intros. intros x y . destruct (H0 x y) as [HEq | [Hxy | Hyx]].
  - left; assumption.
  - right; left. apply H. assumption.
  - right; right.  apply H. assumption.
Qed.

Lemma compare_assymetric : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare -> CompareAsymmetric compare.
Proof.
  intros. destruct H as [R TR]. intros; split; intros.
  - destruct (compare y x) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. apply (compare_eq_lt _ _ R _ H). 
    + apply (TR _ _ _ _ Hyx) in H. apply (compare_eq_lt _ _ R _ H). 
  - destruct (compare x y) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. apply (compare_eq_gt _ _ R _ H). 
    + apply (TR _ _ _ _ Hyx) in H. apply (compare_eq_gt _ _ R _ H).
Qed.

Definition compare_lt {A} (compare : A -> A -> comparison) (x y : A) : Prop :=
  compare x y = Lt.

Lemma compare_lt_irreflexive : forall A  (compare : A -> A -> comparison),
  CompareReflexive compare -> Irreflexive (compare_lt compare).
Proof.
  intros. intros x Hlt. unfold compare_lt in *.
  assert (compare x x = Eq) ; try apply (compare_eq_refl _ compare H x).
  rewrite Hlt in H0. discriminate.
Qed.

Lemma compare_lt_transitive : forall A  (compare : A -> A -> comparison),
  CompareTransitive compare -> Transitive (compare_lt compare).
Proof.
  unfold compare_lt.
  intros. 
  intros x y z Hxy Hyz.
  apply (H _ _ _ _ Hxy Hyz).
Qed.

Lemma compare_lt_strict_order : forall A  (compare : A -> A -> comparison),
  CompareStrictOrder compare -> StrictOrder (compare_lt compare).
Proof.
  intros. destruct H as [R T].
  split.
  - apply compare_lt_irreflexive; assumption.
  - apply compare_lt_transitive; assumption.
Qed.

Lemma compare_lt_asymmetric : forall A  (compare : A -> A -> comparison),
  CompareStrictOrder compare -> Asymmetric (compare_lt compare).
Proof.
  intros.
  apply compare_lt_strict_order in H. destruct H as [IR TR].
  intros x y Hxy Hyx. apply (TR _ _ _ Hxy) in Hyx. apply (IR _ Hyx).
Qed.

Lemma compare_lt_total_order : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare -> TotalOrder (compare_lt compare).
Proof.
  unfold compare_lt.
  intros. intros x y.
  assert (CSO := H).
  destruct H as [R TR].
  destruct (compare x y) eqn:Hcmp.
  - apply R in Hcmp. left. assumption.
  - right. left. reflexivity.
  - right. right. apply compare_assymetric in CSO. apply CSO in Hcmp. assumption.
Qed.

Lemma compare_eq_dec : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  EqualityDec A.
Proof.
  intros. intros x y.
  destruct (compare x y) eqn:Hxy
  ; try (left; apply (proj1 H); assumption)
  ; right; intro; subst
  .
  -  apply compare_eq_lt in Hxy; try apply (proj1 H); assumption.
  -  apply compare_eq_gt in Hxy; try apply (proj1 H); assumption.
Qed.

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

(** This lemma is needed in fault_weight_state_backwards **)
Lemma Rplusminus_assoc : forall r1 r2 r3, 
  (r1 + r2 - r3)%R = (r1 + (r2 - r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplusminus_assoc_r : forall r1 r2 r3, 
  (r1 - r2 + r3)%R = (r1 + (- r2 + r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_opp_l : forall r, (Ropp r + r)%R = 0%R.
Proof.
  intros.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_ge_reg_neg_r : forall r1 r2 r3,
  (r2 <= 0)%R -> (r3 <= r1 + r2)%R -> (r3 <= r1)%R.
Proof.
  intros.
  apply Rge_le.
  apply Rle_ge in H.
  apply Rle_ge in H0.
  apply (Rplus_ge_reg_neg_r r1 r2 r3 H H0).
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rminus_lt_r : forall r1 r2,
  (0 <= r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  apply Rplus_le_compat_l. 
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  assumption.
Qed.

Lemma Rminus_lt_r_strict : forall r1 r2,
  (0 < r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  apply Rplus_le_compat_l. 
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  apply Rlt_le in H.
  assumption.
Qed.
