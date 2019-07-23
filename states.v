Require Import Bool.
Require Import Coq.Classes.RelationClasses.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.


Module States 
        (PCons : Consensus_Values) 
        (PVal : Validators)
        .

Import PCons.
Import PVal.

Module PConsensus_Values_Properties := Consensus_Values_Properties PCons.
Export PConsensus_Values_Properties .

Module PValidators_Properties := Validators_Properties PVal.
Export PValidators_Properties.


(************)
(** States **)
(************)

Inductive state : Set :=
  | Empty : state
  | Next : C ->  V -> state -> state -> state.


Notation "'add' ( c , v , j ) 'to' sigma" :=
  (Next c v j sigma)
  (at level 20).

(********************)
(* State properties *)
(********************)

Fixpoint state_compare (sigma1 sigma2 : state) : comparison :=
  match sigma1, sigma2 with
  | Empty, Empty => Eq
  | Empty, _ => Lt
  | _, Empty => Gt
  | add (c1, v1, j1) to sigma1, add (c2, v2, j2) to sigma2 =>
    match c_compare c1 c2 with
    | Eq =>
      match v_compare v1 v2 with
      | Eq =>
        match state_compare j1 j2 with
        | Eq => state_compare sigma1 sigma2
        | cmp_j => cmp_j
        end
      | cmp_v => cmp_v
      end
    | cmp_c => cmp_c
    end
  end.

Lemma state_compare_reflexive : CompareReflexive state_compare.
Proof.
  destruct c_compare_strict_order as [Rc _].
  destruct v_compare_strict_order as [Rv _].
  intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
  - simpl in H.
    destruct (c_compare c c0) eqn:Hcmp; try discriminate.
    apply Rc in Hcmp; subst.
    destruct (v_compare v v0) eqn:Hcmp; try discriminate.
    apply Rv in Hcmp; subst.
    destruct (state_compare x1 y1) eqn:Hcmp; try discriminate.
    apply IHx1 in Hcmp. apply IHx2 in H. subst.
    reflexivity.
  - inversion H; subst. simpl.
    rewrite compare_eq_refl; try apply Rc.
    rewrite compare_eq_refl; try apply Rv.
    assert (state_compare y1 y1 = Eq). { apply IHx1. reflexivity. }
    assert (state_compare y2 y2 = Eq). { apply IHx2. reflexivity. }
    rewrite H0. assumption.
Qed.

Lemma state_compare_transitive : CompareTransitive state_compare.
Proof.
  destruct c_compare_strict_order as [Rc Tc].
  destruct v_compare_strict_order as [Rv Tv].
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; simpl
    ; inversion H; clear H
    ; destruct (c_compare c0 c) eqn:Hc0; try discriminate
    ; inversion H0; clear H0
    ; destruct (c_compare c c1) eqn:Hc1; try discriminate
    ; try (apply (Tc c0 c c1 _ Hc0) in Hc1 ; rewrite Hc1; reflexivity)
    ; try (apply Rc in Hc0; subst; rewrite Hc1; try reflexivity)
    ; try (apply Rc in Hc1; subst; rewrite Hc0; try reflexivity)
    ; destruct (v_compare v0 v) eqn:Hv0; try discriminate
    ; destruct (v_compare v v1) eqn:Hv1; try discriminate
    ; try (apply (Tv v0 v v1 _ Hv0) in Hv1; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv0; subst; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv1; subst; rewrite Hv0; try reflexivity)
    ; destruct (state_compare x1 y1) eqn:Hj0; try discriminate
    ; destruct (state_compare y1 z1) eqn:Hj1; try discriminate
    ; try (apply (IHy1 x1 z1 _ Hj0) in Hj1; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj0; subst; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj1; subst; rewrite Hj0; try reflexivity)
    ; try rewrite H1; try rewrite H2
    ; try (apply (IHy2 x2 z2 _ H2) in H1; rewrite H1; try reflexivity)
    .
Qed.

Lemma state_compare_strict_order : CompareStrictOrder state_compare.
Proof.
  split.
  - apply state_compare_reflexive.
  - apply state_compare_transitive.
Qed.

Definition state_lt := compare_lt state_compare.

Definition state_lt_irreflexive : Irreflexive state_lt :=
  compare_lt_irreflexive state state_compare state_compare_reflexive.

Definition state_lt_transitive: Transitive state_lt :=
  compare_lt_transitive state state_compare state_compare_transitive.

Definition state_lt_strict_order: StrictOrder state_lt :=
  compare_lt_strict_order state state_compare state_compare_strict_order.

Definition state_lt_total_order: TotalOrder state_lt :=
  compare_lt_total_order state state_compare state_compare_strict_order.

Definition state_eq_dec : forall x y : state, {x = y} + {x <> y} :=
  compare_eq_dec state state_compare state_compare_strict_order.


(**************)
(** Messages **)
(**************)

Definition message := (C * V * state)%type.

Definition estimate (msg : message) : C :=
  match msg with (c, _ , _) => c end.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : state :=
  match msg with (_, _, sigma) => sigma end.

Fixpoint get_messages (sigma : state) : list message :=
  match sigma with
  | Empty => []
  | add (c, v, j) to sigma' => (c,v,j) :: get_messages sigma'
  end.

Definition observed (sigma:state) : list V :=
  set_map v_eq_dec sender (get_messages sigma)
  .

Definition next (msg : message) (sigma : state) : state :=
  match msg with
  | (c, v, j) => add (c, v, j) to sigma
  end.

Lemma get_messages_next : forall msg sigma,
  get_messages (next msg sigma) = msg :: get_messages sigma.
Proof.
  destruct msg as [(c, v) j]. simpl. reflexivity.
Qed.

Lemma add_is_next : forall c v j sigma,
  add (c, v, j)to sigma = next (c, v, j) sigma.
Proof.
  intros. unfold next. reflexivity.
Qed.

Lemma no_confusion_next : forall msg1 msg2 sigma1 sigma2,
  next msg1 sigma1 = next msg2 sigma2 ->
  msg1 = msg2 /\ sigma1 = sigma2.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  inversion H; subst; clear H.
  split; reflexivity.
Qed.

Lemma no_confusion_next_empty : forall msg sigma,
  next msg sigma <> Empty.
Proof.
  intros. intro. destruct msg as [(c, v) j]. inversion H.
Qed.

Definition message_compare  (msg1 msg2 : message) : comparison :=
  state_compare (next msg1 Empty) (next msg2 Empty).

Lemma message_compare_strict_order : CompareStrictOrder message_compare.
Proof.
  split.
  - intros msg1 msg2. unfold message_compare.
    rewrite (state_compare_reflexive (next msg1 Empty) (next msg2 Empty)).
    split; intros; subst; try reflexivity.
    apply no_confusion_next in H. destruct H. assumption.
  - intros msg1 msg2 msg3. unfold message_compare. apply state_compare_transitive.
Qed.

Lemma message_compare_reflexive : forall msg,
  message_compare msg msg = Eq.
Proof.
  intros. apply (proj1 message_compare_strict_order). reflexivity.
Qed.

Definition message_compare_asymmetric : CompareAsymmetric message_compare :=
  compare_asymmetric_intro message message_compare message_compare_strict_order.

Definition message_lt := compare_lt message_compare.

Definition message_lt_irreflexive : Irreflexive message_lt :=
  compare_lt_irreflexive message message_compare (proj1 message_compare_strict_order).

Definition message_lt_transitive: Transitive message_lt :=
  compare_lt_transitive message message_compare (proj2 message_compare_strict_order).

Definition message_lt_strict_order: StrictOrder message_lt :=
  compare_lt_strict_order message message_compare message_compare_strict_order.

Definition message_lt_total_order: TotalOrder message_lt :=
  compare_lt_total_order message message_compare message_compare_strict_order.

Definition message_eq_dec : forall x y : message, {x = y} + {x <> y} :=
  compare_eq_dec message message_compare message_compare_strict_order.

Definition messages_union : set message -> set message -> set message :=
  set_union message_eq_dec.



(************************************)
(** Syntactic membership predicate **)
(**       In_states                **)
(************************************)

Definition in_state (msg : message) (sigma : state) : Prop :=
  In msg (get_messages sigma).

Definition syntactic_state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  incl (get_messages sigma1) (get_messages sigma2).

Lemma in_empty_state : forall msg,
  ~ in_state msg Empty.
Proof.
  intros. intro. inversion H.
Qed.

Lemma in_state_dec : forall msg sigma, 
  {in_state msg sigma} + {~ in_state msg sigma}.
Proof.
  intros. apply in_dec. apply message_eq_dec.
Qed.

Lemma in_state_dec_if_true {A} : forall msg sigma (T E : A),
  in_state msg sigma ->
  (if in_state_dec msg sigma then T else E) = T.
Proof.
  intros. destruct (in_state_dec msg sigma); try reflexivity.
  exfalso. apply n. apply H.
Qed.

Lemma in_state_dec_if_false {A} : forall msg sigma (T E : A),
  ~ in_state msg sigma ->
  (if in_state_dec msg sigma then T else E) = E.
Proof.
  intros. destruct (in_state_dec msg sigma); try reflexivity.
  exfalso. apply H. apply i.
Qed.

Definition in_state_fn  (msg : message) (sigma : state) : bool :=
  match in_state_dec msg sigma with
  | left _ => true
  | right _ => false
  end.

Lemma in_state_function : PredicateFunction2 in_state in_state_fn.
Proof.
  intros msg sigma; split; intro; destruct (in_state_dec msg sigma) eqn:Hin;
  unfold in_state_fn in *.
  - rewrite Hin. reflexivity.
  - exfalso; apply n; apply H.
  - assumption.
  - exfalso. rewrite Hin in H. discriminate.
Qed.

Lemma in_state_iff : forall msg msg1 sigma1,
  in_state msg (next msg1 sigma1) <-> msg1 = msg \/ in_state msg sigma1.
Proof.
  unfold in_state. intros. rewrite get_messages_next. simpl.
  split; intros; destruct H; (left; assumption) || (right; assumption).
Qed.

Lemma in_singleton_state : forall msg msg',
  in_state msg (next msg' Empty) -> msg = msg'.
Proof.
  intros. apply in_state_iff in H.
  destruct H; subst; try reflexivity.
  exfalso. apply (in_empty_state _ H).
Qed.

(** More properties of messages **)

(** Messages from a sender in a state **)
Definition from_sender (v:V) (sigma:state) : list message :=
  filter (fun msg' => v_eq_fn (sender msg') v)
    (get_messages sigma).

(** Later messages for a message and a sender in a state **)
Definition later_from (msg:message) (v:V) (sigma:state) : list message :=
  filter 
    (fun msg' => (in_state_fn msg (justification msg')) && 
                 (v_eq_fn (sender msg') v))
    (get_messages sigma)
  .

(** Latest messages from senders in a state **)
(** note: there cannot be duplicates in the result **)
Definition latest_messages (sigma:state) : V -> list message :=
  fun v => filter 
            (fun msg => is_nil_fn (later_from msg v sigma))
            (from_sender v sigma)
  .

(** Latest estimates from senders in a state **)
(** note: there can be duplicates in the result **)
Definition latest_estimates (sigma:state) : V -> list C :=
  fun v => set_map c_eq_dec estimate (latest_messages sigma v)
  .

Definition validators_latest_estimates (c:C) (sigma:state) : list V :=
    filter (fun v => in_fn c_eq_dec c (latest_estimates sigma v)) (observed sigma)
  .

End States.