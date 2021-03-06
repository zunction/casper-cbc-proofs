Require Import Reals Bool Relations RelationClasses List ListSet EqdepFacts ProofIrrelevance Eqdep_dec.
Import ListNotations.

From CasperCBC Require Export Classes.

(** * General utility definitions, lemmas, and tactics *)

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec_save" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

Definition noneOrAll
  (op : option Prop)
  : Prop
  :=
  match op with
  | None => True
  | (Some p) => p
  end.

Lemma exist_eq
  {X}
  (P : X -> Prop)
  (a b : {x : X | P x})
  : a = b <-> proj1_sig a = proj1_sig b.
Proof.
  destruct a as [a Ha]; destruct b as [b Hb]; simpl.
  split; intros Heq.
  - inversion Heq. reflexivity.
  - subst. apply f_equal. apply proof_irrelevance.
Qed.

(* https://coq.discourse.group/t/writing-equality-decision-that-reduces-dec-x-x-for-opaque-x/551/2 *)

Lemma eq_dec_refl A (eq_dec : forall x y : A, {x = y} + {x <> y}) x :
  eq_dec x x = left eq_refl.
Proof.
  destruct (eq_dec x x) as [|[]]; trivial.
  f_equal.
  now apply K_dec_type with (P := fun prf => prf = eq_refl).
Qed.

Instance nat_eq_dec: EqDecision nat := eq_nat_dec.

Definition mid {X Y Z : Type} (xyz : X * Y * Z) : Y :=
  snd (fst xyz).

Lemma or_and_distr_left : forall A B C, (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
  intros; split; intro.
  - split; destruct H as [[HA HB] | HC]; (left; assumption) || right; assumption.
  - destruct H as [Hac Hbc].
    destruct Hac as [Ha | Hc]; try (right; assumption).
    destruct Hbc as [Hb | Hc]; try (right; assumption).
    left. split; assumption.
Qed.

Lemma and_iff_l {P Q R:Prop} : P -> (Q <-> R) -> (P /\ Q <-> P /\ R).
Proof.
  firstorder.
Qed.

Lemma not_ex_all_not
  {A : Type}
  (P : A -> Prop)
  (Hne : ~ (exists a : A, P a))
  : forall a:A, ~ P a.
Proof.
  intros a Hpa.
  apply Hne.
  exists a.
  assumption.
Qed.

Lemma forall_and_commute
  {A : Type}
  (P Q : A -> Prop)
  : ((forall a, P a) /\ (forall a, Q a)) <-> forall a, P a /\ Q a.
Proof.
  firstorder.
Qed.

Lemma mirror_reflect: forall X (f : X -> bool) (P : X -> Prop),
  (forall x : X, f x = true <-> P x) ->
  (forall x : X, f x = false <-> ~P x).
Proof.
  split; repeat intro.
  + rewrite <- H in H1. rewrite H0 in H1. discriminate.
  + specialize (H x). destruct (f x).
    exfalso. apply H0. rewrite <- H. reflexivity.
    reflexivity.
Qed.

Theorem mirror_reflect_curry :
  forall (X Y : Type) (f : X -> Y -> bool) (P : X -> Y -> Prop),
    (forall x y, f x y = true <-> P x y) ->
    (forall x y, f x y = false <-> ~ P x y).
Proof.
  intros.
  split; intros.
  intro H_absurd. apply H in H_absurd.
  rewrite H0 in H_absurd; discriminate.
  apply not_true_is_false.
  intro H_not. apply H in H_not.
  contradiction.
Qed.

Lemma dec_if_true
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t e : B)
  (Hp : P x y)
  : (if dec x y then t else e) = t.
Proof.
  destruct (dec x y) eqn:Hcmp; try reflexivity.
  elim n. assumption.
Qed.

Lemma dec_if_false
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t e : B)
  (Hnp : ~P x y)
  : (if dec x y then t else e) = e.
Proof.
  destruct (dec x y) eqn:Hcmp; try reflexivity.
  elim Hnp. assumption.
Qed.

Lemma eq_dec_if_true {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x = y -> (if eq_dec x y then t else e) = t.
Proof.
  apply dec_if_true.
Qed.

Lemma eq_dec_if_false {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x <> y -> (if eq_dec x y then t else e) = e.
Proof.
  apply dec_if_false.
Qed.

Lemma dec_match_left
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t : P x y -> B) (e : ~P x y -> B)
  (Hp : P x y)
  (Hirrelevance : forall p : P x y, p = Hp)
  : (match dec x y with | left p => t p | right np => e np end) = t Hp.
Proof.
  destruct (dec x y) eqn:Hcmp.
  - rewrite Hirrelevance at 1. reflexivity.
  - elim n. assumption.
Qed.

Lemma dec_match_right
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t : P x y -> B) (e : ~P x y -> B)
  (Hp : ~P x y)
  (Hirrelevance : forall p : ~P x y, p = Hp)
  : (match dec x y with | left p => t p | right np => e np end) = e Hp.
Proof.
  destruct (dec x y) eqn:Hcmp.
  - elim Hp. assumption.
  - rewrite Hirrelevance at 1. reflexivity.
Qed.

Class DecidablePred {A} (r : A -> Prop) :=
  pred_dec : forall (a : A), r a \/ ~ r a.
Hint Mode DecidablePred ! ! : typeclass_instances.

Class PredicateFunction {A} (r : A -> Prop) (r_fn : A -> bool) : Prop :=
  {
    equiv : forall a, r a <-> r_fn a = true;
    predicate_function_dec :> DecidablePred r;
  }.
Hint Mode PredicateFunction ! ! - : typeclass_instances.
Hint Mode PredicateFunction ! - ! : typeclass_instances.

Definition predicate_not {A} (p : A -> Prop) : A -> Prop :=
  fun a => ~ p a.

Lemma predicate_function_neg {A} `{PredicateFunction A} :
  forall a, ~ r a <-> r_fn a = false.
Proof.
  intro a; split; intros.
  apply not_true_iff_false. intro Hnot.
  apply equiv in Hnot. contradiction.
  intro Hnot. apply not_true_iff_false in H0.
  apply H0. apply (equiv a). assumption.
Qed.

Class PredicateFunction2 {A B} (r : A -> B -> Prop) (r_fn : A -> B -> bool) : Prop :=
  predicate_function2 : forall a b, r a b <-> r_fn a b = true.
Hint Mode PredicateFunction2 ! ! ! - : typeclass_instances.
Hint Mode PredicateFunction2 ! ! - ! : typeclass_instances.

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

Lemma bool_decide_predicate_function2 {A B} (P : A -> B -> Prop) {P_dec : RelDecision P}:
  PredicateFunction2 P (fun a b => bool_decide (P a b)).
Proof.
  intros. intros a b. symmetry. apply bool_decide_eq_true.
Qed.

Lemma Is_true_predicate_function2: forall A B (f : A -> B -> bool),
  PredicateFunction2 (fun a b => Is_true (f a b)) f.
Proof.
  intros. intros a b. symmetry. apply Is_true_iff_eq_true.
Qed.

(* Reflexivity of comparison operators *)
Class CompareReflexive {A} (compare : A -> A -> comparison) : Prop :=
    compare_eq : forall x y, compare x y = Eq <-> x = y.
Hint Mode CompareReflexive ! - : typeclass_instances.

(* About reflexive comparison operators *)
Lemma compare_eq_refl {A} `{CompareReflexive A} :
  forall x, compare x x = Eq.
Proof. intros; now apply H. Qed.

Lemma compare_eq_lt {A} `{CompareReflexive A} :
  forall x, ~ compare x x = Lt.
Proof.
  intros x Hnot.
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hnot in H0; discriminate.
Qed.

Lemma compare_lt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Lt -> x <> y.
Proof.
  intros x y Hcomp Hnot.
  subst. now (apply (compare_eq_lt y) in Hcomp).
Qed.

Lemma compare_eq_gt {A} `{CompareReflexive A} :
  forall x, ~ compare x x = Gt.
Proof.
  intros x Hnot.
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hnot in H0; discriminate.
Qed.

Lemma compare_gt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Gt -> x <> y.
Proof.
  intros x y H_comp H_not.
  subst. now apply compare_eq_gt in H_comp.
Qed.

(* Transitivity of comparison operators *)
Class CompareTransitive {A} (compare : A -> A -> comparison) : Prop :=
    compare_transitive : forall x y z comp, compare x y = comp ->
                                       compare y z = comp ->
                                       compare x z = comp.
Hint Mode CompareTransitive ! - : typeclass_instances.

(* Strict-orderedness of comparison operators *)
Class CompareStrictOrder {A} (compare : A -> A -> comparison) : Prop :=
  {
    StrictOrder_Reflexive :> CompareReflexive compare;
    StrictOrder_Transitive :> CompareTransitive compare;
  }.
Hint Mode CompareStrictOrder ! - : typeclass_instances.

(* Strictly-ordered comparisons give decidable equality *)
Lemma compare_eq_dec {A} `{CompareStrictOrder A} :
  EqDecision A.
Proof.
  intros x y.
  destruct (compare x y) eqn:Hxy;
    (left; apply StrictOrder_Reflexive; assumption)
    || (right; intro; subst; [now apply compare_eq_lt in Hxy || now apply compare_eq_gt in Hxy]).
Qed.

Definition eq_bool {X} `{CompareStrictOrder X} (x y : X) : bool :=
  match compare_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Asymmetry of comparison operators *)
Class CompareAsymmetric {A} (compare : A -> A -> comparison) : Prop :=
    compare_asymmetric : forall x y, compare x y = Lt <-> compare y x = Gt.
Hint Mode CompareAsymmetric ! - : typeclass_instances.

(* Strictly-ordered comparisons give asymmetry *)
Lemma compare_asymmetric_intro {A} `{CompareStrictOrder A} :
  CompareAsymmetric compare.
Proof.
  intros. destruct H as [R TR]. intros; split; intros.
  - destruct (compare y x) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. now apply compare_eq_lt in H.
    + apply (TR _ _ _ _ Hyx) in H. now apply compare_eq_lt in H.
  - destruct (compare x y) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. now apply compare_eq_gt in H.
    + apply (TR _ _ _ _ Hyx) in H. now apply compare_eq_gt in H.
Qed.

Instance CompareStrictOrder_Asymmetric {A} (compare : A -> A -> comparison) `{CompareStrictOrder A compare} : CompareAsymmetric compare.
Proof.
  apply compare_asymmetric_intro.
Defined.

(* Defining a compare_lt predicate from a compare operator *)
Definition compare_lt {A} (compare : A -> A -> comparison) (x y : A) : Prop :=
  compare x y = Lt.

(* A series of properties about compare_lt *)
Lemma compare_lt_irreflexive {A} `{CompareReflexive A} :
  Irreflexive (compare_lt compare).
Proof.
  intros x Hlt.
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hlt in H0; discriminate.
Qed.

Lemma compare_lt_transitive {A} `{CompareTransitive A} :
  Transitive (compare_lt compare).
Proof.
  intros x y z Hxy Hyz; now apply (H _ _ _ _ Hxy Hyz).
Qed.

Lemma compare_lt_strict_order {A} `{CompareStrictOrder A} :
  StrictOrder (compare_lt compare).
Proof.
  destruct H as [R T].
  split.
  - now apply compare_lt_irreflexive.
  - now apply compare_lt_transitive.
Qed.

Lemma compare_lt_asymmetric {A} `{CompareStrictOrder A} :
  Asymmetric (compare_lt compare).
Proof.
  intros.
  destruct H as [IR TR].
  intros x y Hxy Hyx. apply (TR _ _ _ _ Hxy) in Hyx.
  assert (compare x x = Eq) by (apply compare_eq; reflexivity).
  rewrite Hyx in H; discriminate.
Qed.

(* We can easily obtain inhabitants of above Typeclasses using Program Definitions, for instance : *)
Program Definition make_compare_lt_asymmetric {A} `{CompareStrictOrder A} : Asymmetric (compare_lt compare).
Proof.
  exact compare_lt_asymmetric.
Defined.

(* A generic type class for inhabited types with a strictly ordered comparison operator *)
Class StrictlyComparable (X : Type) : Type :=
   {
     inhabited : X;
     compare : X -> X -> comparison;
     compare_strictorder :> CompareStrictOrder compare;
   }.
Hint Mode StrictlyComparable ! : typeclass_instances.

Instance strictly_comparable_eq_dec `{StrictlyComparable M}
  : EqDecision M.
Proof.
  intros x y.
  apply compare_eq_dec.
Qed.

Definition comparable
  {A : Type}
  (R : A -> A -> Prop)
  (a b : A)
  : Prop
  :=
  a = b \/ R a b \/ R b a.

Lemma comparable_commutative
   {A : Type}
   (R : A -> A -> Prop)
   (a b : A) :
   comparable R a b <-> comparable R b a.
Proof.
  firstorder.
Qed.

Definition comparableb
  `{EqDecision A}
  (f : A -> A -> bool)
  (a b : A)
  : bool
  :=
  if decide (a = b) then true
  else orb (f a b) (f b a).

Definition incomparableb
  `{EqDecision A}
  (f : A -> A -> bool)
  (a b : A)
  : bool
  :=
  if decide (a = b) then false
  else andb (negb (f a b)) (negb (f b a)).

Lemma negb_comparableb `{EqDecision A} (f : A -> A -> bool) (a b : A):
  incomparableb f a b = negb (comparableb f a b).
Proof.
  unfold incomparableb, comparableb.
  destruct (decide (a = b));[reflexivity|].
  rewrite negb_orb.
  reflexivity.
Qed.

Lemma comparable_function
  {A : Type}
  {eq_A : EqDecision A}
  (f : A -> A -> bool)
  (R : A -> A -> Prop)
  (HR : PredicateFunction2 R f)
  : PredicateFunction2 (comparable R) (comparableb f).
Proof.
  intros a b. unfold comparable. unfold comparableb.
  split; intro.
  - destruct H as [Heq | [Hab | Hba]]; destruct (decide (a = b)); try reflexivity.
    + elim n. assumption.
    + apply HR in Hab. rewrite Hab. reflexivity.
    + apply HR in Hba. rewrite Hba. rewrite orb_comm. reflexivity.
  - destruct (decide (a = b)); try (left; assumption).
    right.
    apply orb_true_iff in H.
    destruct H as [H | H]; apply HR in H.
    + left. assumption.
    + right. assumption.
Qed.

Instance comparable_dec
  {A : Type}
  {eq_A : EqDecision A}
  (R : A -> A -> Prop)
  {HR : RelDecision R}
  : RelDecision (comparable R).
Proof.
  intros a b.
  eapply reflect_dec.
  apply iff_reflect, comparable_function, bool_decide_predicate_function2.
Qed.

Lemma comparable_function_neg
  `{EqDecision A}
  (f : A -> A -> bool)
  (R : A -> A -> Prop)
  (HR : PredicateFunction2 R f)
  (a b : A)
  (Hnc : comparableb f a b = false)
  : a <> b /\ ~R a b /\ ~R b a.
Proof.
  unfold comparableb in Hnc.
  destruct (decide (a = b)); try discriminate Hnc.
  split; try assumption.
  destruct (f a b) eqn:Hab; try discriminate Hnc.
  destruct (f b a) eqn:Hba; try discriminate Hnc.
  apply (predicate_function2_neg _ _ _ _ HR) in Hab.
  apply (predicate_function2_neg _ _ _ _ HR) in Hba.
  split; assumption.
Qed.

Lemma comparable_function_bool
  {A : Type}
  {eq_A : EqDecision A}
  (f : A -> A -> bool)
  : PredicateFunction2 (comparable f) (comparableb f).
Proof.
  apply comparable_function.
  apply Is_true_predicate_function2.
Qed.

Lemma compare_two_cases
  `{Hsc : StrictlyComparable M}
  : forall m1 m2 : M,
    (compare m1 m2 = Eq /\ compare m2 m1 = Eq) \/
    (compare m1 m2 = Lt /\ compare m2 m1 = Gt) \/
    (compare m1 m2 = Gt /\ compare m2 m1 = Lt).
Proof.
  intros m1 m2.
  destruct (compare m1 m2) eqn:H_m.
  left. split; try reflexivity.
  rewrite compare_eq in H_m. subst.
  apply compare_eq_refl.
  right. left; split; try reflexivity.
  now apply compare_asymmetric.
  right; right; split; try reflexivity.
  now apply compare_asymmetric.
Qed.

Tactic Notation "case_pair" constr(about_M) constr(m1) constr(m2) :=
  assert (H_fresh := @compare_two_cases _ about_M m1 m2);
  destruct H_fresh as [[H_eq1 H_eq2] | [[H_lt H_gt] | [H_gt H_lt]]].

Lemma sigify_eq_dec {X : Type} `{StrictlyComparable X} :
  forall (P : X -> Prop),
    forall (x1 x2 : {x | P x}), {x1 = x2} + {x1 <> x2}.
Proof.
  intros P x1 x2;
    destruct x1 as [x1 about_x1];
    destruct x2 as [x2 about_x2].
  simpl.
  destruct (compare_eq_dec x1 x2) as [left | right].
  left. apply exist_eq; assumption.
  right. intro Hnot. apply exist_eq in Hnot.
  contradiction.
Qed.

Program Definition sigify_compare {X} `{StrictlyComparable X} (P : X -> Prop) : {x | P x} -> {x | P x} -> comparison := _.
Next Obligation.
  exact (compare X0 X1).
Defined.

(* StrictlyComparable option type *)
Definition option_compare
  {X : Type}
  (compare : X -> X -> comparison)
  (ox oy : option X)
  : comparison
  :=
  match ox, oy with
  | None, None => Eq
  | None, _ => Lt
  | _, None => Gt
  | Some x, Some y => compare x y
  end.

Lemma option_compare_reflexive
  (X : Type)
  {Xsc : StrictlyComparable X}
  : CompareReflexive (option_compare (@compare X _)).
Proof.
  intros [x|] [y|]; simpl; split; intro H; inversion H; try reflexivity.
  - f_equal. apply StrictOrder_Reflexive in H. assumption.
  - apply StrictOrder_Reflexive. reflexivity.
Qed.

Lemma option_compare_transitive
  (X : Type)
  {Xsc : StrictlyComparable X}
  : CompareTransitive (option_compare (@compare X _)).
Proof.
  intros [x|] [y|] [z|] [| |]; simpl; intros Hxy Hyz; try discriminate; try reflexivity.
  - apply (StrictOrder_Transitive x y z _); assumption.
  - apply (StrictOrder_Transitive x y z _); assumption.
  - apply (StrictOrder_Transitive x y z _); assumption.
Qed.

Lemma strictorder_option
  {X: Type}
  (Xsc : StrictlyComparable X)
  : CompareStrictOrder (option_compare (@compare X _)).
Proof.
  split; exact (option_compare_reflexive X) || exact (option_compare_transitive X).
Qed.

(* Now we can have the following for free : *)
Instance OptionStrictlyComparable
  (X : Type)
  {Xsc : StrictlyComparable X}
  : StrictlyComparable (option X) :=
  { inhabited := None;
    compare := option_compare compare;
    compare_strictorder := strictorder_option Xsc;
  }.

(* Composing StrictlyComparable types *)
(* Constructing the compare function *)
Definition compare_compose (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : (X * Y) -> (X * Y) -> comparison :=
  fun p1 p2 =>
    match p1, p2 with
    | (x1, y1), (x2, y2) => match compare x1 x2 with
                           | Eq => match compare y1 y2 with
                                  | Eq => Eq
                                  | _ => compare y1 y2
                                  end
                           | _ => compare x1 x2
                           end
    end.

(* Constructing the inhabited proof *)
Lemma inhabited_compose {X Y : Type} `{HscX : StrictlyComparable X} `{HscY : StrictlyComparable Y}
  : X * Y.
Proof.
  remember (@inhabited _ HscX ) as x.
  remember (@inhabited _ HscY) as y.
  exact (x,y).
Qed.

(* Constructing the strictorder proof *)
Lemma reflexive_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareReflexive (compare_compose X Y).
Proof.
  intros (x1, y1) (x2, y2).
  split; intros.
  simpl in H1.
  destruct (compare x1 x2) eqn:H_x;
    destruct (compare y1 y2) eqn: H_y;
    try discriminate.
  apply StrictOrder_Reflexive in H_x;
    apply StrictOrder_Reflexive in H_y.
  subst; reflexivity.
  inversion H1; subst.
  simpl; do 2 rewrite compare_eq_refl; reflexivity.
Qed.

Lemma compare_compose_lt {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : forall (x1 x2 : X) (y1 y2 : Y) (c : comparison),
  compare_compose X Y (x1, y1) (x2, y2) = c ->
  compare x1 x2 = c \/
  x1 = x2 /\ compare y1 y2 = c.
Proof.
  intros x1 x2 y1 y2 c H_12.
  simpl in H_12.
  destruct (compare x1 x2) eqn:H_x; try (left; assumption).
  right. split. now apply StrictOrder_Reflexive in H_x.
  destruct (compare y1 y2) eqn:H_y; try discriminate; assumption.
Qed.

Lemma transitive_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareTransitive (compare_compose X Y).
Proof.
  intros (x1, y1) (x2, y2) (x3, y3) comp H12 H23.
  destruct comp eqn:H_comp; try
  (apply reflexive_compose;
   apply reflexive_compose in H12;
     apply reflexive_compose in H23;
     inversion H12; inversion H23; subst; reflexivity).
  - rewrite <- H_comp in *;
    assert (H_useful := compare_compose_lt x1 x2 y1 y2 comp H12);
    assert (H_useful' := compare_compose_lt x2 x3 y2 y3 comp H23).
    destruct H_useful as [left | right];
    destruct H_useful' as [left' | right'].
    assert (compare x1 x3 = comp) by (apply (StrictOrder_Transitive x1 x2 x3 comp left left'); assumption).
    simpl; rewrite H1; subst; reflexivity.
    destruct right'; subst.
    simpl; rewrite left; reflexivity.
    destruct right; subst.
    simpl; rewrite left'; reflexivity.
    destruct right; destruct right'; subst.
    assert (compare y1 y3 = Lt) by (apply (StrictOrder_Transitive y1 y2 y3 Lt); assumption).
    simpl; rewrite compare_eq_refl; simpl in H12; rewrite H1; reflexivity.
  - rewrite <- H_comp in *;
    assert (H_useful := compare_compose_lt x1 x2 y1 y2 comp H12);
    assert (H_useful' := compare_compose_lt x2 x3 y2 y3 comp H23).
    destruct H_useful as [left | right];
    destruct H_useful' as [left' | right'].
    assert (compare x1 x3 = comp) by (apply (StrictOrder_Transitive x1 x2 x3 comp left left'); assumption).
    simpl; rewrite H1; subst; reflexivity.
    destruct right'; subst.
    simpl; rewrite left; reflexivity.
    destruct right; subst.
    simpl; rewrite left'; reflexivity.
    destruct right; destruct right'; subst.
    assert (compare y1 y3 = Gt) by (apply (StrictOrder_Transitive y1 y2 y3 Gt); assumption).
    simpl; rewrite compare_eq_refl; simpl in H12; rewrite H1; reflexivity.
Qed.

Lemma strictorder_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareStrictOrder (compare_compose X Y).
Proof.
  split; exact reflexive_compose || exact transitive_compose.
Qed.

(* Now we can have the following for free : *)
Instance ComposeStrictlyComparable (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : StrictlyComparable (X * Y) :=
  { inhabited := inhabited_compose;
    compare := compare_compose X Y;
    compare_strictorder := strictorder_compose;
  }.

Instance TripleStrictlyComparable (X Y Z : Type) `{StrictlyComparable X} `{StrictlyComparable Y} `{StrictlyComparable Z} : StrictlyComparable (X * Y * Z) :=
  { inhabited := inhabited_compose;
    compare := compare_compose (X * Y) Z;
    compare_strictorder := strictorder_compose;
  }.

Definition triple_strictly_comparable_proj1_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : X.
Proof.
  destruct HscXYZ as [((x, y), z) _ _].
  exact x.
Defined.

Definition triple_strictly_comparable_proj1_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  (x1 x2 : X) : comparison.
Proof.
  destruct HscXYZ as [((x, y), z) compare _].
  exact (compare (x1, y, z) (x2, y, z)).
Defined.

Lemma triple_strictly_comparable_proj1_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj1_compare X Y Z HscXYZ).
Proof.
  split.
  - intros x y.
      unfold triple_strictly_comparable_proj1_compare.
      destruct HscXYZ.
      destruct inhabited0 as [(x0, y0) z0].
    split; intro.
    + apply StrictOrder_Reflexive in H. inversion H. reflexivity.
    + subst. apply StrictOrder_Reflexive . reflexivity.
  - intros x1 x2 x3 cmp.
    unfold triple_strictly_comparable_proj1_compare.
    destruct HscXYZ.
    destruct inhabited0 as [(x0, y0) z0].
    apply StrictOrder_Transitive.
Qed.

Definition triple_strictly_comparable_proj1
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable X
  :=
  {| inhabited := triple_strictly_comparable_proj1_inhabited;
    compare := triple_strictly_comparable_proj1_compare;
    compare_strictorder := triple_strictly_comparable_proj1_strictorder;
  |}.

Definition triple_strictly_comparable_proj2_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : Y.
Proof.
  destruct HscXYZ as [[(x, y) z] _ _].
  exact y.
Defined.

Definition triple_strictly_comparable_proj2_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  (y1 y2 : Y) : comparison.
Proof.
  destruct HscXYZ as [[(x, y) z] compare _].
  exact (compare (x, y1, z) (x, y2, z)).
Defined.

Lemma triple_strictly_comparable_proj2_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj2_compare X Y Z HscXYZ).
Proof.
  split.
  - intros x y.
      unfold triple_strictly_comparable_proj2_compare.
      destruct HscXYZ.
      destruct inhabited0 as [(x0, y0) z0].
    split; intro.
    + apply StrictOrder_Reflexive in H. inversion H. reflexivity.
    + subst. apply StrictOrder_Reflexive . reflexivity.
  - intros x1 x2 x3 cmp.
    unfold triple_strictly_comparable_proj2_compare.
    destruct HscXYZ.
    destruct inhabited0 as [(x0, y0) z0].
    apply StrictOrder_Transitive.
Qed.

Definition triple_strictly_comparable_proj2
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable Y
  :=
  {| inhabited := triple_strictly_comparable_proj2_inhabited;
    compare := triple_strictly_comparable_proj2_compare;
    compare_strictorder := triple_strictly_comparable_proj2_strictorder;
  |}.

Definition triple_strictly_comparable_proj3_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : Z.
Proof.
  destruct HscXYZ as [[(x, y) z] _ _].
  exact z.
Defined.

Definition triple_strictly_comparable_proj3_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  (z1 z2 : Z) : comparison.
Proof.
  destruct HscXYZ as [[(x, y) z] compare _].
  exact (compare (x, y, z1) (x, y, z2)).
Defined.

Lemma triple_strictly_comparable_proj3_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj3_compare X Y Z HscXYZ).
Proof.
  split.
  - intros x y.
      unfold triple_strictly_comparable_proj3_compare.
      destruct HscXYZ.
      destruct inhabited0 as [(x0, y0) z0].
    split; intro.
    + apply StrictOrder_Reflexive in H. inversion H. reflexivity.
    + subst. apply StrictOrder_Reflexive . reflexivity.
  - intros x1 x2 x3 cmp.
    unfold triple_strictly_comparable_proj3_compare.
    destruct HscXYZ.
    destruct inhabited0 as [(x0, y0) z0].
    apply StrictOrder_Transitive.
Qed.

Definition triple_strictly_comparable_proj3
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable Z
  :=
  {| inhabited := triple_strictly_comparable_proj3_inhabited;
    compare := triple_strictly_comparable_proj3_compare;
    compare_strictorder := triple_strictly_comparable_proj3_strictorder;
  |}.


Definition bounding (P : nat -> Prop)
  :=  {n1 : nat | forall (n2 : nat), n1 <= n2 -> ~P n2}.

Definition liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2}.

Definition liveness_dec (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2} + {~exists n2:nat, n1 <= n2 /\ P n2}.

Definition min_liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2
               /\ forall (n3 : nat), n2 <= n3 /\ P n3 -> n2 <= n3}.

Lemma not_bounding_impl_liveness
  (P : nat -> Prop)
  (Hdec : liveness_dec P)
  (Hnbound : ~exists n1:nat, forall (n2:nat), n1 <= n2 -> ~P n2)
  : liveness P.
Proof.
  intros n1.
  specialize (Hdec n1).
  destruct Hdec as [Hex | Hnex]; try assumption.
  specialize (not_ex_all_not _ Hnbound); simpl; clear Hnbound; intro Hnbound.
  specialize (Hnbound n1).
  elim Hnbound.
  intros n2 Hleq HnP.
  apply Hnex.
  exists n2.
  split; assumption.
Qed.

(** optionally extracts an element belonging to first type from a sum type *)
Definition sum_project_left
  {A B : Type}
  (x : A + B)
  : option A
  :=
  match x with
  | inl a => Some a
  | inr _ => None
  end.

(** optionally extracts an element belonging to second type from a sum type *)
Definition sum_project_right
  {A B : Type}
  (x : A + B)
  : option B
  :=
  match x with
  | inl _ => None
  | inr b => Some b
  end.
