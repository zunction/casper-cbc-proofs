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
