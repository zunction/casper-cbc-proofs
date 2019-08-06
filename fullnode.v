Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.  
From Casper
     Require Import preamble ListExtras ListSetExtras RealsExtras protocol.

Require Import Omega.
 
(* Proof irrelevance states that all proofs of the same proposition are equal *) 
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
 
Lemma proj1_sig_injective {X : Type} :
    forall (P : X -> Prop)
      (x1 x2 : X) (H1 : P x1) (H2 : P x2),
      (exist P x1 H1) = (exist P x2 H2) <-> x1 = x2. 
Proof.
  intros P x1 x2 H1 H2; split.  
  - intro H_eq_dep.
    apply eq_sig_fst in H_eq_dep; assumption.
  - intro H_eq.
    subst. assert (H1 = H2) by eapply proof_irrelevance.
    rewrite H. reflexivity.
Qed.

(** Building blocks for instancing CBC_protocol with full node version **)
(** Syntactic equality on states **) 


Variables C V : Type. 
Context (about_C : `{StrictlyComparable C})
        (about_V : `{StrictlyComparable V}). 

Parameter weight : V -> {r : R | (r > 0)%R}.
Definition sum_weights (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l. 

Parameters (t_full : {r | (r >= 0)%R})
           (suff_val_full : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t_full))%R).

Inductive state : Type :=
  | Empty : state
  | Next : C ->  V -> state -> state -> state.

Definition state0 : state := Empty. 

Notation "'add' ( c , v , j ) 'to' sigma" :=
  (Next c v j sigma)
  (at level 20).

(* Constructing a StrictlyComparable state type *) 
Lemma state_inhabited : exists (s : state), True. 
Proof. 
  destruct about_C, about_V.
  destruct inhabited, inhabited0.
  exists (Next x x0 Empty Empty).  auto.
Qed.

Fixpoint state_compare (sigma1 sigma2 : state) : comparison :=
  match sigma1, sigma2 with
  | Empty, Empty => Eq
  | Empty, _ => Lt
  | _, Empty => Gt
  | add (c1, v1, j1) to sigma1, add (c2, v2, j2) to sigma2 =>
    match compare c1 c2 with
    | Eq =>
      match compare v1 v2 with
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
  intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
  - simpl in H.
    destruct (compare c c0) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    destruct (compare v v0) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    destruct (state_compare x1 y1) eqn:Hcmp; try discriminate.
    apply IHx1 in Hcmp. apply IHx2 in H. subst.
    reflexivity.
  - inversion H; subst. simpl.
    repeat rewrite compare_eq_refl.
    assert (state_compare y1 y1 = Eq).
    { apply IHx1. reflexivity. }
    assert (state_compare y2 y2 = Eq).
    { apply IHx2. reflexivity. }
    rewrite H0. assumption.
Qed.     

Lemma state_compare_transitive : CompareTransitive state_compare.
Proof.
  destruct (@compare_strictorder C about_C) as [Rc Tc].
  destruct (@compare_strictorder V about_V) as [Rv Tv].
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; simpl
    ; inversion H; clear H
    ; destruct (compare c0 c) eqn:Hc0; try discriminate
    ; inversion H0; clear H0
    ; destruct (compare c c1) eqn:Hc1; try discriminate
    ; try (apply (Tc c0 c c1 _ Hc0) in Hc1 ; rewrite Hc1; reflexivity)
    ; try (apply Rc in Hc0; subst; rewrite Hc1; try reflexivity)
    ; try (apply Rc in Hc1; subst; rewrite Hc0; try reflexivity)
    ; destruct (compare v0 v) eqn:Hv0; try discriminate
    ; destruct (compare v v1) eqn:Hv1; try discriminate
    ; try (apply (Tv v0 v v1 _ Hv0) in Hv1; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv0; subst; rewrite Hv1; try reflexivity)
    ; try (apply Rv in Hv1; subst; rewrite Hv0; try reflexivity)
    ; destruct (state_compare x1 y1) eqn:Hj0; try discriminate
    ; destruct (state_compare y1 z1) eqn:Hj1; try discriminate
    ; try (apply (IHy1 x1 z1 _ Hj0) in Hj1; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj0; subst; rewrite Hj1; try reflexivity)
    ; try (apply state_compare_reflexive in Hj1; subst; rewrite Hj0; try reflexivity)
    ; try rewrite H1; try rewrite H2
    ; try (apply (IHy2 x2 z2 _ H2) in H1; rewrite H1; try reflexivity).
Qed.

Lemma state_compare_strict_order : CompareStrictOrder state_compare.
Proof.
  split.
  - apply state_compare_reflexive.
  - apply state_compare_transitive.
Qed.

Instance state_type : StrictlyComparable state :=
  {
    inhabited := state_inhabited;
    compare := state_compare;
    compare_strictorder := state_compare_strict_order;
  }.

(* Keeping the definitions of messages for now : *)
(* Constructing a StrictlyComparable type for message *) 
Definition message : Type := (C * V * state).

Lemma message_inhabited : exists (m : message), True. 
Proof.
  destruct about_C, about_V.
  destruct inhabited, inhabited0.
  destruct (state_inhabited).
  exists (x,x0,x1); auto.
Qed.

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
  set_map compare_eq_dec sender (get_messages sigma).

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

Instance message_strictorder : CompareStrictOrder message_compare := _. 
split.
  - intros msg1 msg2. unfold message_compare.
    rewrite (state_compare_reflexive (next msg1 Empty) (next msg2 Empty)).
    split; intros; subst; try reflexivity.
    apply no_confusion_next in H. destruct H. assumption.
  - intros msg1 msg2 msg3. unfold message_compare. apply state_compare_transitive.
Defined.

Instance message_type : StrictlyComparable message :=
  { inhabited := message_inhabited;
    compare := message_compare;
    compare_strictorder := message_compare_strict_order;
  }.

(* Constructing a StrictOrder type for message_lt *) 

Definition message_lt := compare_lt message_compare. 

Instance message_lt_strictorder : StrictOrder message_lt :=
  _. 
split. apply compare_lt_irreflexive.
apply compare_lt_transitive.
Defined.

(* Defining state_union using messages *)

(* Library for state type *)

(* State membership *) 
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
  intros. apply in_dec. apply compare_eq_dec.
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

(* Ordering on states *) 
Inductive locally_sorted : state -> Prop :=
  | LSorted_Empty : locally_sorted Empty
  | LSorted_Singleton : forall c v j,
          locally_sorted j ->
          locally_sorted (next (c, v, j) Empty)
  | LSorted_Next : forall c v j msg' sigma, 
          locally_sorted j  ->
          message_lt (c, v, j) msg' -> 
          locally_sorted (next msg' sigma) -> 
          locally_sorted (next (c, v, j) (next msg' sigma))
  .

Definition locally_sorted_msg (msg : message) : Prop :=
  locally_sorted (next msg Empty).

Lemma locally_sorted_message_justification : forall c v j,
  locally_sorted_msg (c,v,j) <-> locally_sorted j.
Proof.
  intros; split; intro.
  - inversion H; subst; assumption.
  - apply LSorted_Singleton. assumption.
Qed.

Lemma locally_sorted_message_characterization : forall sigma,
  locally_sorted sigma <->
  sigma = Empty
  \/
  (exists msg, locally_sorted_msg msg /\ sigma = next msg Empty)
  \/
  (exists msg1 msg2 sigma',
    sigma = next msg1 (next msg2 sigma') 
    /\ locally_sorted (next msg2 sigma')
    /\ locally_sorted_msg msg1
    /\ message_lt msg1 msg2
  ).
Proof.
  split; intros.
  { inversion H; subst.
    - left. reflexivity.
    - right. left. exists (c,v,j).
      split; try reflexivity.
      apply locally_sorted_message_justification. assumption.
    - right. right. exists (c, v, j). exists msg'. exists sigma0.
      split; try reflexivity.
      repeat (split; try assumption).
      apply locally_sorted_message_justification. assumption.
  }
  { destruct H as [H | [H | H]]; subst; try constructor.
    - destruct H as [msg [LSmsg EQ]]; subst.
      destruct msg as [(c,v) j]. apply locally_sorted_message_justification in LSmsg.
      constructor. assumption.
    - destruct H as [msg1 [msg2 [sigma' [EQ [LS2' [LSmsg1 LT]]]]]]; subst.
      destruct msg1 as [(c1,v1) j1]. apply locally_sorted_message_justification in LSmsg1.
      constructor; assumption.
  }
Qed.

Lemma locally_sorted_next_next : forall msg1 msg2 sigma,
  locally_sorted (next msg1 (next msg2 sigma)) ->
  message_lt msg1 msg2.
Proof.
  intros. apply locally_sorted_message_characterization in H.
  destruct H as [H | [[msg [_ H]] | [msg1' [msg2' [sigma' [H [_ [_ Hlt]]]]]]]].
  - exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [_ H].
    exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [Heq H]; subst.
    apply no_confusion_next in H. destruct H as [Heq H]; subst.
    assumption.
Qed.

Lemma locally_sorted_remove_second : forall msg1 msg2 sigma,
  locally_sorted (next msg1 (next msg2 sigma)) ->
  locally_sorted (next msg1 sigma).
Proof.
  intros.
  apply locally_sorted_message_characterization in H.
  destruct H as [H | [[msg [_ H]] | [msg1' [msg2' [sigma' [Heq [H [Hj Hlt]]]]]]]].
  - exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [_ H].
    exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in Heq. destruct Heq as [Heq' Heq]; subst.
    apply no_confusion_next in Heq. destruct Heq as [Heq' Heq]; subst.
    apply locally_sorted_message_characterization in H.
    destruct H as [H | [[msg [_ H]] | [msg2'' [msg3 [sigma'' [Heq [H [_ Hlt2]]]]]]]].
    + exfalso. apply (no_confusion_next_empty _ _ H).
    + apply no_confusion_next in H. destruct H; subst. apply Hj.
    + apply no_confusion_next in Heq. destruct Heq; subst.
      assert (CompareTransitive message_compare) by
          apply message_type.
      apply (compare_lt_transitive  _ _ _ Hlt) in Hlt2.
      clear Hlt.
      destruct msg1' as [(c1', v1') j1']. destruct msg3 as [(c3, v3) j3].
      apply locally_sorted_message_justification in Hj.
      apply LSorted_Next; assumption. 
Qed.

Lemma locally_sorted_head : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted_msg msg.
Proof.
  intros [(c, v) j] sigma H. inversion H; subst; apply locally_sorted_message_justification; assumption.
Qed.

Lemma locally_sorted_tail : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted sigma.
Proof.
  intros.
  apply locally_sorted_message_characterization in H.
  destruct H as 
    [ Hcempty
    | [[cmsg0 [LScmsg0 Hcnext]]
    | [cmsg1 [cmsg2 [csigma' [Hcnext [LScnext [LScmsg1 LTc]]]]]]
    ]]; subst
    ; try (apply no_confusion_next in Hcnext; destruct Hcnext; subst)
    .
  - exfalso; apply (no_confusion_next_empty _ _ Hcempty).
  - constructor.
  - assumption.
Qed.

Lemma locally_sorted_all : forall sigma,
  locally_sorted sigma ->
  Forall locally_sorted_msg (get_messages sigma).
Proof.
  intros. rewrite Forall_forall. induction H; simpl; intros msg Hin.
  - inversion Hin.
  - destruct Hin as [Hin | Hin] ; subst; try inversion Hin.
    apply locally_sorted_message_justification. assumption.
  - destruct Hin as [Heq | Hin]; subst.
    + apply locally_sorted_message_justification. assumption.
    + apply IHlocally_sorted2. assumption.
Qed.

Lemma locally_sorted_first : forall msg sigma,
  locally_sorted (next msg sigma) ->
  forall msg',
  in_state msg' sigma ->
  message_lt msg msg'.
Proof.
  intros msg sigma. generalize dependent msg. induction sigma; intros.
  - inversion H0.
  - rewrite add_is_next in *. apply locally_sorted_next_next in H as H1.
    rewrite in_state_iff in H0. destruct H0; subst.
    + assumption.
    + apply locally_sorted_remove_second in H. apply IHsigma2; assumption.
Qed.

Lemma sorted_syntactic_state_inclusion_first_equal : forall sigma sigma' msg,
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg sigma') ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros.
  intros msg' Hin.
  apply (locally_sorted_first msg) in Hin as Hlt; try assumption.
  unfold syntactic_state_inclusion in H1. 
  assert (Hin' : In msg' (get_messages (next msg sigma))).
  { rewrite get_messages_next. right. assumption. }
  apply H1 in Hin'. rewrite get_messages_next in Hin'.
  destruct Hin'; try assumption; subst.
  exfalso.
  assert (CompareReflexive message_compare) by apply message_type. apply (compare_lt_irreflexive _ Hlt).
Qed.

Lemma sorted_syntactic_state_inclusion : forall sigma sigma' msg msg',
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg' sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg' sigma') ->
  (msg = msg' /\ syntactic_state_inclusion sigma sigma')
  \/
  (message_lt msg' msg /\ syntactic_state_inclusion (next msg sigma) sigma').
Proof.
  intros. unfold syntactic_state_inclusion in H1.
  assert (Hin : In msg (get_messages (next msg' sigma'))).
  { apply H1. rewrite get_messages_next. left. reflexivity. }
  rewrite get_messages_next in Hin.  simpl in Hin.
  destruct Hin.
  - left. subst. split; try reflexivity.
    apply sorted_syntactic_state_inclusion_first_equal with msg; assumption.
  - right. apply (locally_sorted_first msg') in H2 as Hlt; try assumption.
    split; try assumption.
    intros msg1 Hin1.
    apply H1 in Hin1 as H1in'.
    rewrite get_messages_next in H1in'.  simpl in H1in'.
    rewrite get_messages_next in Hin1.  simpl in Hin1.
    assert (Hlt1 : message_lt msg' msg1).
    { destruct Hin1; subst; try assumption.
      apply (locally_sorted_first msg) in H3; try assumption.
      assert (CompareTransitive message_compare) by apply message_type. 
      apply compare_lt_transitive with msg; assumption.
    }
    destruct H1in'; try assumption; subst.
    exfalso. assert (CompareReflexive message_compare) by apply message_type. apply (compare_lt_irreflexive _ Hlt1).
Qed.

Lemma sorted_syntactic_state_inclusion_eq_ind : forall sigma1 sigma2 msg1 msg2,
  locally_sorted (next msg1 sigma1) ->
  locally_sorted (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg1 sigma1) (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg2 sigma2) (next msg1 sigma1) ->
  msg1 = msg2 /\ syntactic_state_inclusion sigma1 sigma2 /\ syntactic_state_inclusion sigma2 sigma1.
Proof.
  intros.
  apply sorted_syntactic_state_inclusion in H1; try assumption.
  apply sorted_syntactic_state_inclusion in H2; try assumption.
  destruct H1; destruct H2; destruct H1; destruct H2; subst.
  - repeat (split; try reflexivity; try assumption).
  - exfalso. apply (compare_lt_irreflexive _ H2).
  - exfalso. apply (compare_lt_irreflexive _ H1).
  - exfalso. apply (compare_lt_transitive _ _ _ H1) in H2.
    apply (compare_lt_irreflexive _ H2).
Qed.

Lemma sorted_syntactic_state_inclusion_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  syntactic_state_inclusion sigma1 sigma2 ->
  syntactic_state_inclusion sigma2 sigma1 ->
  sigma1 = sigma2.
Proof.
  induction sigma1; intros; destruct sigma2; repeat rewrite add_is_next in *.
  - reflexivity.
  - unfold syntactic_state_inclusion in H2. rewrite get_messages_next in H2.
    simpl in H2. apply incl_empty in H2. discriminate.
  - unfold syntactic_state_inclusion in H1. rewrite get_messages_next in H1.
    simpl in H1. apply incl_empty in H1. discriminate.
  - apply sorted_syntactic_state_inclusion_eq_ind in H2; try assumption.
    destruct H2 as [Heq [Hin12 Hin21]].
    inversion Heq; subst; clear Heq.
    apply locally_sorted_tail in H.
    apply locally_sorted_tail in H0.
    apply IHsigma1_2 in Hin21; try assumption.
    subst.
    reflexivity.
Qed.

(* Constructing ordered states *) 
Fixpoint add_in_sorted_fn (msg: message) (sigma: state) : state :=
  match msg, sigma with
  | _, Empty => next msg Empty
  | msg, add (c, v, j) to sigma' =>
    match message_compare msg (c, v, j) with
    | Eq => sigma
    | Lt => next msg sigma
    | Gt => next (c, v, j) (add_in_sorted_fn msg sigma')
    end
  end.

Lemma set_eq_add_in_sorted : forall msg sigma,
  set_eq (get_messages (add_in_sorted_fn msg sigma)) (msg :: (get_messages sigma)).
Proof.
  induction sigma.
  - simpl. rewrite get_messages_next.
    simpl. split; apply incl_refl.
  - clear IHsigma1. simpl.
    destruct (message_compare msg (c, v, sigma1)) eqn:Hcmp.
    + simpl. apply StrictOrder_Reflexive in Hcmp. subst.
      split; intros x H.
      * right. assumption.
      * destruct H; try assumption; subst. left. reflexivity.
    + rewrite get_messages_next. simpl. split; apply incl_refl.
    + simpl. split; intros x Hin.
      * destruct Hin; try (right; left; assumption).
        apply IHsigma2 in H. destruct H; try (left; assumption).
        right; right; assumption.
      * { destruct Hin as [Hmsg | [H1 | H2]]
        ; (left; assumption) || (right; apply IHsigma2)
        .
        - left; assumption.
        - right; assumption.
        }
Qed.

Lemma in_state_add_in_sorted_iff : forall msg msg' sigma',
  in_state msg (add_in_sorted_fn msg' sigma') <->
  msg = msg' \/ in_state msg sigma'.
Proof.
  intros.
  destruct (set_eq_add_in_sorted msg' sigma') as [Hincl1 Hincl2].
  split; intros.
  - apply Hincl1 in H. destruct H.
    + subst. left. reflexivity.
    + right. assumption.
  - apply Hincl2. destruct H; subst.
    + left. reflexivity.
    + right. assumption.
Qed.

Lemma add_in_sorted_next : forall msg1 msg2 sigma,
  add_in_sorted_fn msg1 (next msg2 sigma) =
    match message_compare msg1 msg2 with
    | Eq => next msg2 sigma
    | Lt => next msg1 (next msg2 sigma)
    | Gt => next msg2 (add_in_sorted_fn msg1 sigma)
    end.
Proof.
  intros msg1 [(c, v) j] sigma. reflexivity.
Qed.

Lemma add_in_sorted_non_empty : forall msg sigma,
  add_in_sorted_fn msg sigma <> Empty.
Proof.
  intros. intro Hadd.
  destruct sigma; inversion Hadd.
  - apply (no_confusion_next_empty _ _ H0).
  - destruct (message_compare msg (c, v, sigma1)); inversion H0.
    apply (no_confusion_next_empty _ _ H0).
Qed.

Lemma add_in_sorted_inv1 : forall msg msg' sigma,
  add_in_sorted_fn msg sigma = next msg' Empty -> msg = msg'.
Proof.
  intros [(c, v) j] msg' sigma AddA.
  destruct sigma.
  - simpl in AddA. rewrite add_is_next in AddA. apply no_confusion_next in AddA.
    destruct AddA. assumption.
  - simpl in AddA. destruct (message_compare (c, v, j) (c0, v0, sigma1)) eqn:Hcmp
    ; rewrite add_is_next in AddA; apply no_confusion_next in AddA; destruct AddA; subst;
    try reflexivity.
    + apply StrictOrder_Reflexive in Hcmp; inversion Hcmp; subst; clear Hcmp.
      reflexivity.
    + exfalso. apply (add_in_sorted_non_empty _ _ H0).
Qed.

Lemma add_in_sorted_sorted : forall msg sigma,
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  locally_sorted (add_in_sorted_fn msg sigma).
Proof.
  intros msg sigma. generalize dependent msg.
  induction sigma; intros.
  - simpl. assumption.
  - clear IHsigma1; rename sigma1 into j; rename sigma2 into sigma; rename IHsigma2 into IHsigma.
    simpl. destruct msg as [(mc, mv) mj].
    apply locally_sorted_message_justification in H0 as Hmj.
    repeat rewrite add_is_next in *.
    apply locally_sorted_tail in H as Hsigma.
    apply locally_sorted_head in H as Hcvj. apply locally_sorted_message_justification in Hcvj as Hj.
    apply (IHsigma _ Hsigma) in H0 as HLSadd.
    destruct (message_compare (mc, mv, mj) (c, v, j)) eqn:Hcmp.
    + assumption.
    + constructor; assumption.
    + apply compare_asymmetric in Hcmp.
      apply locally_sorted_message_characterization in HLSadd as Hadd.
      destruct Hadd as [Hadd | [Hadd | Hadd]].
      * exfalso. apply (add_in_sorted_non_empty _ _ Hadd).
      * destruct Hadd as [msg' [Hmsg' Hadd]]. rewrite Hadd.
        apply add_in_sorted_inv1 in Hadd; subst.
        constructor; assumption.
      * destruct Hadd as [msg1 [msg2 [sigma' [Hadd [HLS' [H1 Hlt12]]]]]].
        rewrite Hadd in *. constructor; try assumption.
        assert (Forall (message_lt (c, v, j)) (get_messages (add_in_sorted_fn (mc, mv, mj) sigma))).
        { apply Forall_forall. intros. apply set_eq_add_in_sorted in H2.
          destruct H2 as [Heq | Hin]; subst; try assumption.
          apply locally_sorted_first with sigma; assumption.
        }
        rewrite Hadd in H2. rewrite get_messages_next in H2. apply Forall_inv in H2. assumption.
Qed.

(* Constructing an ordered state from messages *) 
Definition list_to_state (msgs : list message) : state :=
  fold_right add_in_sorted_fn Empty msgs.

Lemma list_to_state_locally_sorted : forall msgs,
  Forall locally_sorted_msg msgs ->
  locally_sorted (list_to_state msgs).
Proof.
  induction msgs; simpl; try constructor; intros.
  apply add_in_sorted_sorted.
  - apply IHmsgs. apply Forall_forall. intros msg Hin.
    rewrite Forall_forall in H. apply H. right. assumption.
  - apply Forall_inv with msgs. assumption.
Qed.

Lemma list_to_state_iff : forall msgs : list message,
  set_eq (get_messages (list_to_state msgs)) msgs.
Proof.
  induction msgs; intros.
  - simpl. split; apply incl_refl.
  - simpl. apply set_eq_tran with (a :: (get_messages (list_to_state msgs))).
    + apply set_eq_add_in_sorted.
    + apply set_eq_cons. assumption.
Qed.

Lemma list_to_state_sorted : forall sigma,
  locally_sorted sigma ->
  list_to_state (get_messages sigma) = sigma.
Proof.
  intros. induction H; try reflexivity.
  rewrite get_messages_next. simpl. rewrite IHlocally_sorted2.
  rewrite add_in_sorted_next. rewrite H0. reflexivity.
Qed.

(* Defining state_union *) 
Definition messages_union (m1 m2 : list message) := m1 ++ m2. 

Definition state_union (sigma1 sigma2 : state) : state :=
  (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))).

Definition sorted_state : Type :=
  { s : state | locally_sorted s }. 

Definition sorted_state_proj1 (s : sorted_state) := proj1_sig s.

Coercion sorted_state_proj1 : sorted_state >-> state.

Lemma state0_neutral :
  forall (s : sorted_state),
    state_union s Empty = s.
Proof.
  intros s. unfold state_union.
  simpl. unfold messages_union.
  rewrite app_nil_r. apply list_to_state_sorted.
  destruct s. assumption.
Qed.

Definition sorted_state0 : sorted_state :=
  exist (fun s => locally_sorted s) Empty LSorted_Empty.

(* Commence add_in_sorted_fn tedium *) 
Lemma add_in_sorted_ignore_repeat :
  forall msg c v j,
    msg = (c, v, j) ->
    forall s,
      add_in_sorted_fn msg (add (c,v,j) to s) =
      add (c,v,j) to s. 
Proof.     
  intros.
  simpl.
  replace (message_compare msg (c,v,j)) with Eq.
  reflexivity. subst. rewrite compare_eq_refl.
  reflexivity. 
Qed.

Lemma message_two_cases :
  forall m1 m2,
    (message_compare m1 m2 = Eq /\ message_compare m2 m1 = Eq) \/
    (message_compare m1 m2 = Lt /\ message_compare m2 m1 = Gt) \/
    (message_compare m1 m2 = Gt /\ message_compare m2 m1 = Lt). 
Proof.
  intros m1 m2.
  destruct (message_compare m1 m2) eqn:H_m.
  left. split; try reflexivity.
  rewrite compare_eq in H_m. subst.
  apply compare_eq_refl.
  right. left; split; try reflexivity.
  now apply compare_asymmetric.
  right; right; split; try reflexivity.
  now apply compare_asymmetric.
Qed.

Tactic Notation "case_pair" constr(m1) constr(m2) :=
  assert (H_fresh := message_two_cases m1 m2);
  destruct H_fresh as [[H_eq1 H_eq2] | [[H_lt H_gt] | [H_gt H_lt]]]. 

Lemma add_in_sorted_swap_base :
  forall x y,
    add_in_sorted_fn y (add_in_sorted_fn x Empty) =
    add_in_sorted_fn x (add_in_sorted_fn y Empty).
Proof. 
  intros x y.
  destruct x; destruct p.
  destruct y; destruct p.
  simpl.
  case_pair (c0,v0,s0) (c,v,s). 
  - rewrite H_eq1, H_eq2.
    apply compare_eq in H_eq2.
    inversion H_eq2; subst. reflexivity.
  - rewrite H_lt, H_gt. reflexivity.
  - rewrite H_gt, H_lt. reflexivity.
Qed.

Lemma add_in_sorted_swap_succ :
  forall x y s,
    add_in_sorted_fn y (add_in_sorted_fn x s) =
    add_in_sorted_fn x (add_in_sorted_fn y s).
Proof. 
  intros x y; induction s as [|c v j IHj prev IHs]. 
  - apply add_in_sorted_swap_base. 
  - simpl.
    destruct (message_compare x (c,v,j)) eqn:H_x.
    apply compare_eq in H_x.
    destruct (message_compare y (c,v,j)) eqn:H_y.
    apply compare_eq in H_y. subst; reflexivity.
    rewrite add_in_sorted_next.
    assert (H_y_copy := H_y). 
    rewrite <- H_x in H_y.
    apply compare_asymmetric in H_y. rewrite H_y.
    simpl. rewrite H_y_copy.
    rewrite H_x. rewrite compare_eq_refl. reflexivity.
    simpl. rewrite H_y. rewrite H_x; rewrite compare_eq_refl; simpl; reflexivity.
    destruct (message_compare y (c,v,j)) eqn:H_y.
    simpl. rewrite H_x.
    apply compare_eq in H_y. subst.
    rewrite add_is_next.
    rewrite add_in_sorted_next.
    apply compare_asymmetric in H_x. 
    rewrite H_x. simpl. rewrite compare_eq_refl.
    reflexivity. rewrite add_in_sorted_next.
    destruct (message_compare y x) eqn:H_yx.
    apply compare_eq in H_yx. subst.
    rewrite add_in_sorted_next. rewrite compare_eq_refl.
    reflexivity.
    rewrite add_in_sorted_next.
    apply compare_asymmetric in H_yx. rewrite H_yx.
    simpl. rewrite H_x. reflexivity.
    rewrite add_in_sorted_next.
    apply compare_asymmetric in H_yx. rewrite H_yx.
    simpl. rewrite H_y. reflexivity.
    simpl. rewrite H_x.
    rewrite add_in_sorted_next.
     destruct (message_compare y x) eqn:H_yx.
    apply compare_eq in H_yx. subst.
    simpl. rewrite H_x in H_y; inversion H_y.
    assert (message_compare y (c,v,j) = Lt). eapply StrictOrder_Transitive. exact H_yx. exact H_x. rewrite H_y in H; inversion H. simpl. rewrite H_y. reflexivity.
    simpl.
    destruct (message_compare y (c,v,j)) eqn:H_y.
    apply compare_eq in H_y. subst. simpl. rewrite H_x.
    reflexivity. rewrite add_in_sorted_next.
    destruct (message_compare x y) eqn:H_xy.
    apply compare_eq in H_xy. subst.
    simpl. rewrite H_x in H_y; inversion H_y.
    assert (message_compare x (c,v,j) = Lt). 
    eapply StrictOrder_Transitive. apply H_xy. assumption.
    rewrite H_x in H; inversion H. simpl. rewrite H_x.
    reflexivity. simpl.
    rewrite H_x.
    (* Finally, the induction hypothesis is used *)
    rewrite IHs. reflexivity.
Qed.

Lemma add_in_sorted_head :
  forall msg c v j,
    msg = (c, v, j) ->
    forall s,
      add_in_sorted_fn msg (add (c,v,j) to s) =
      add (c,v,j) to s. 
Proof.     
  intros.
  simpl.
  replace (message_compare msg (c,v,j)) with Eq.
  reflexivity. subst. rewrite compare_eq_refl.
  reflexivity. 
Qed.

Tactic Notation "next" :=
  try rewrite add_is_next, add_in_sorted_next; simpl.

(* The following is from adequacy's sort.v *)
Inductive add_in_sorted : message -> state -> state -> Prop :=
   | add_in_Empty : forall msg,
          add_in_sorted msg Empty (next msg Empty)
   | add_in_Next_eq : forall msg sigma,
          add_in_sorted msg (next msg sigma) (next msg sigma)
   | add_in_Next_lt : forall msg msg' sigma,
          message_lt msg msg' ->  
          add_in_sorted msg (next msg' sigma) (next msg (next msg' sigma))
   | add_in_Next_gt : forall msg msg' sigma sigma',
          message_lt msg' msg ->
          add_in_sorted msg sigma sigma' ->
          add_in_sorted msg (next msg' sigma) (next msg' sigma').

Lemma add_in_empty : forall msg sigma,
  add_in_sorted msg Empty sigma -> sigma = (next msg Empty).
Proof.
  intros [(c, v) j] sigma AddA. 
  inversion AddA as 
    [ [(ca, va) ja] A AEmpty C'
    | [(ca, va) ja] sigmaA A ANext C'
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA smsg smsg' smsg1
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddA' A B C]
  ; clear AddA.
  subst. reflexivity.
Qed.

Lemma add_in_sorted_correct :
  forall msg s1 s2, add_in_sorted msg s1 s2 <-> add_in_sorted_fn msg s1 = s2.
Proof.
  intros msg sigma1 sigma2; generalize dependent sigma2.
  induction sigma1; intros; split; intros.
  - apply add_in_empty in H. subst. reflexivity.
  - simpl in H. subst. constructor.
  - inversion H; subst; repeat rewrite add_is_next in *. 
    + apply no_confusion_next in H2; destruct H2; subst; simpl.
      rewrite compare_eq_refl. reflexivity.
    + apply no_confusion_next in H0; destruct H0; subst; simpl.
      unfold message_lt in H2. unfold compare_lt in H2. rewrite H2. reflexivity.
    + apply no_confusion_next in H0; destruct H0; subst; simpl.
      unfold message_lt in H1. unfold compare_lt in H1.
      apply compare_asymmetric in H1. rewrite H1.
      apply IHsigma1_2 in H3. rewrite H3. reflexivity.
  - simpl in H. destruct (message_compare msg (c, v, sigma1_1)) eqn:Hcmp; subst; repeat rewrite add_is_next.
    + apply StrictOrder_Reflexive in Hcmp; subst.
      apply add_in_Next_eq.
    + apply add_in_Next_lt. assumption.
    + apply add_in_Next_gt.
      * apply compare_asymmetric in Hcmp. assumption.
      * apply IHsigma1_2. reflexivity.
Qed.

Lemma add_in_sorted_sorted' : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  add_in_sorted msg sigma sigma' ->
  locally_sorted sigma'.
Proof.
  intros. apply add_in_sorted_correct in H1; subst.
  apply add_in_sorted_sorted; assumption.
Qed.

Lemma no_confusion_add_in_sorted_empty : forall msg sigma,
  ~ add_in_sorted msg sigma Empty.
Proof.
  intros. intro.
  apply add_in_sorted_correct in H.
  destruct sigma.
  - simpl in H. apply (no_confusion_next_empty _ _ H).
  - simpl in H. 
    destruct (message_compare msg (c, v, sigma1))
    ; rewrite add_is_next in *
    ; apply (no_confusion_next_empty _ _ H)
    .
Qed.

Lemma add_in_sorted_functional : forall msg sigma1 sigma2 sigma2',
  add_in_sorted msg sigma1 sigma2 ->
  add_in_sorted msg sigma1 sigma2' ->
  sigma2 = sigma2'.
Proof.
  intros; f_equal.
  apply add_in_sorted_correct in H.
  apply add_in_sorted_correct in H0.
  subst. reflexivity.
Qed.

Lemma add_in_sorted_message_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  in_state msg sigma'.
Proof.
  intros. unfold in_state.
  induction H; rewrite get_messages_next; simpl; try (left; reflexivity).
  right. assumption.
Qed.

Lemma add_in_sorted_no_junk : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  forall msg', in_state msg' sigma' -> msg' = msg \/ in_state msg' sigma.
Proof.
  intros msg sigma sigma' H.
  induction H as
  [ [(hc, hv) hj]
  | [(hc, hv) hj] Hsigma
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma HLT
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma Hsigma' HGT HAdd H_H 
  ]; intros [(c', v') j'] HIn; rewrite in_state_iff in HIn
  ; destruct HIn as [Hin1 | Hin2]
  ; try (right; assumption)
  ; try (inversion Hin1; subst; left; reflexivity)
  .
  - right. apply in_state_iff. right. assumption.
  - right. apply in_state_iff. inversion Hin1; clear Hin1; subst. left. reflexivity.
  - apply H_H in Hin2. destruct Hin2 as [HInEq | HIn'].
    + left. assumption.
    + right. apply in_state_iff. right. assumption.
Qed.

Lemma add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
  induction sigma; intros; repeat rewrite add_is_next in *.
  - exfalso. apply (in_empty_state _ H0).
  - rewrite in_state_iff in H0. destruct H0.
    + subst. constructor.
    + apply (locally_sorted_first (c, v, sigma1)) in H0 as Hlt; try assumption.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.
(* End from adequacy, sort.v *)

Lemma add_in_sorted_ignore :
  forall msg (s : sorted_state),
    in_state msg s ->
    add_in_sorted_fn msg s = s. 
Proof.
  intros.
  apply add_in_sorted_correct.
  apply add_sorted.
  destruct s; assumption.
  assumption.
Qed.

Lemma add_in_sorted_fn_in :
  forall s1 s2,
    add_in_sorted_fn s1 (next s1 s2) = next s1 s2.
Proof.
  intros; destruct s1; destruct p.
  simpl. rewrite compare_eq_refl. reflexivity.
Qed.

Lemma state_union_comm_swap :
  forall x y s, 
    add_in_sorted_fn y (add_in_sorted_fn x s) =
    add_in_sorted_fn x (add_in_sorted_fn y s).
Proof.                      
  intros.
  induction s. 
  - apply add_in_sorted_swap_base.
  - apply add_in_sorted_swap_succ.
Qed.

Lemma state_union_comm_helper_helper :
  forall (l1 l2 : list message),
    Permutation l1 l2 ->
    list_to_state l1 = list_to_state l2. 
Proof. 
  intros.
  induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation.
    reflexivity.
  - simpl.
    apply state_union_comm_swap. 
  - rewrite IHPermutation1, IHPermutation2.
    reflexivity.
Qed. 

Lemma sorted_state_union_comm :
  forall (s1 s2 : sorted_state),
    state_union s1 s2 = state_union s2 s1.
Proof.
  intros s1 s2;
  destruct s1 as [s1 about_s1];
  destruct s2 as [s2 about_s2];
  simpl.
  assert (H_useful := list_to_state_sorted s1 about_s1).
  assert (H_useful' := locally_sorted_all s1 about_s1).
  unfold state_union.
  assert (H_duh : Permutation (messages_union (get_messages s1) (get_messages s2))
                              (messages_union (get_messages s2) (get_messages s1))).
  unfold messages_union. rewrite Permutation_app_comm.
  reflexivity. now apply state_union_comm_helper_helper.
Qed.

Lemma state_union_messages : forall sigma1 sigma2,
  set_eq (get_messages (state_union sigma1 sigma2)) (messages_union (get_messages sigma1) (get_messages sigma2)).
Proof.
  intros.
  apply list_to_state_iff.
Qed.

Lemma state_union_incl_right : forall sigma1 sigma2,
  syntactic_state_inclusion sigma2 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages.
  unfold messages_union; apply in_app_iff; right; assumption.
Qed.

Lemma state_union_incl_left : forall sigma1 sigma2,
  syntactic_state_inclusion sigma1 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages.
  unfold messages_union; apply in_app_iff; left; assumption.
Qed.

Lemma state_union_iff : forall msg sigma1 sigma2,
  in_state msg (state_union sigma1 sigma2) <-> in_state msg sigma1 \/ in_state msg sigma2.
Proof.
  intros; unfold state_union; unfold in_state; split; intros.
  - apply state_union_messages in H. unfold messages_union in H.
    apply in_app_iff; assumption. 
  - apply state_union_messages. unfold messages_union.
    rewrite in_app_iff; assumption. 
Qed.

Lemma state_union_incl_iterated : forall sigmas sigma,
  In sigma sigmas ->
  syntactic_state_inclusion sigma (fold_right state_union Empty sigmas).
Proof.
  induction sigmas; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. apply state_union_incl_left.
    + apply IHsigmas in H. apply incl_tran with (get_messages (fold_right state_union Empty sigmas)); try assumption.
      apply state_union_incl_right.
Qed.

Lemma state_union_sorted : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted (state_union sigma1 sigma2).
Proof.
  intros.
  apply locally_sorted_all in H as Hall1. rewrite Forall_forall in Hall1.
  apply locally_sorted_all in H0 as Hall2. rewrite Forall_forall in Hall2.
  apply list_to_state_locally_sorted. apply Forall_forall. intros msg Hin.
  unfold messages_union in Hin.
  rewrite in_app_iff in Hin. destruct Hin.
  - apply Hall1. assumption.
  - apply Hall2. assumption.
Qed.

Lemma state_union_add_in_sorted : forall sigma1 msg2 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted_msg msg2 ->
  state_union sigma1 (add_in_sorted_fn msg2 sigma2) = add_in_sorted_fn msg2 (state_union sigma1 sigma2).
Proof.
  intros.
  apply sorted_syntactic_state_inclusion_equality_predicate.
  - apply state_union_sorted; try assumption. 
    apply add_in_sorted_sorted; assumption.
  - apply add_in_sorted_sorted; try assumption.
    apply state_union_sorted; assumption.
  - intros msg Hin. 
    apply state_union_iff in Hin.
    apply set_eq_add_in_sorted.
    destruct Hin as [Hin | Hin].
    + right. apply state_union_iff. left; assumption.
    + apply set_eq_add_in_sorted in Hin. destruct Hin as [Heq | Hin]; subst.
      * left; reflexivity.
      * right.  apply state_union_iff. right; assumption.
  - intros msg Hin.
    apply set_eq_add_in_sorted in Hin.
    apply state_union_iff.
    destruct Hin as [Heq | Hin]; subst.
    + right. apply set_eq_add_in_sorted. left; reflexivity.
    + apply state_union_iff in Hin.
      destruct Hin.
      * left; assumption.
      * right. apply set_eq_add_in_sorted. 
      right; assumption.
Qed.

Program Definition sorted_state_union (sigma1 sigma2 : sorted_state) : sorted_state :=
  exist _ (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))) _.
Next Obligation.
  apply state_union_sorted.
  destruct sigma1; assumption.
  destruct sigma2; assumption. 
Defined.

Lemma sorted_state_sorted_union_comm :
  forall (s1 s2 : sorted_state),
    sorted_state_union s1 s2 = sorted_state_union s2 s1.
Proof.
  intros s1 s2.
  assert (H_useful := sorted_state_union_comm s1 s2).
  unfold sorted_state_union. 
  now apply proj1_sig_injective.
Qed.

(* Defining the reachability relation *) 
Definition reachable (s1 s2 : sorted_state) :=
  syntactic_state_inclusion (sorted_state_proj1 s1) (sorted_state_proj1 s2).

Notation "sigma2 'in_Futures' sigma1" :=
  (reachable sigma1 sigma2)
  (at level 20).

Lemma reachable_trans : forall sigma1 sigma2 sigma3,
  reachable sigma1 sigma2 ->
  reachable sigma2 sigma3 ->
  reachable sigma1 sigma3.
Proof.
  intros.
  repeat (split; try assumption). apply incl_tran with (get_messages sigma2); assumption.
Qed.

Lemma reach_union : forall (s1 s2 : sorted_state), reachable s1 (sorted_state_union s1 s2).   
Proof. 
  intros s1 s2. unfold state_union. 
  intros x H_in.
  assert (H_incl := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_incl as [_ useful]. 
  spec useful x. spec useful.
  apply in_app_iff. tauto.
  assumption.
Qed.

Lemma reachable_morphism : forall s1 s2 s3, reachable s1 s2 -> s2 = s3 -> reachable s1 s3.  
Proof. intros; subst; assumption. Qed. 

(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> C -> Prop)
           (estimator_total : forall s : state, exists c : C, estimator s c). 

(* Defining protocol states as predicates *) 
Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _ => false
  | _ => match msg1, msg2 with (c1, v1, j1), (c2, v2, j2) =>
      match compare_eq_dec v1 v2 with
      | left _ => negb (in_state_fn msg1 j2) && negb (in_state_fn msg2 j1)
      | right _ => false
      end
    end
  end.

Lemma equivocating_messages_comm : forall msg1 msg2,
  equivocating_messages msg1 msg2 = equivocating_messages msg2 msg1.
Proof.
  intros [(c1, v1) sigma1] [(c2, v2) sigma2].
  unfold equivocating_messages.
  destruct (compare_eq_dec (c1, v1, sigma1) (c2, v2, sigma2)).
  subst. rewrite eq_dec_if_true.
  rewrite eq_dec_if_true. reflexivity.
  symmetry; assumption.
  assumption. 
  rewrite (eq_dec_if_false compare_eq_dec). 
  destruct (compare_eq_dec v1 v2). 
  rewrite eq_dec_if_false.
  rewrite e. rewrite eq_dec_if_true.
  rewrite andb_comm. reflexivity. reflexivity.
  intro Hnot; symmetry in Hnot; tauto.
  rewrite eq_dec_if_false.
  rewrite eq_dec_if_false. reflexivity.
  intro Hnot; symmetry in Hnot; tauto.
  intro Hnot; symmetry in Hnot; tauto.
  assumption. 
Qed. 

Lemma non_equivocating_messages_extend : forall msg sigma1 c v,
  In msg (get_messages sigma1) ->
  equivocating_messages msg (c, v, sigma1) = false.
Proof.
  intros [(c0, v0) sigma']; intros.
  unfold equivocating_messages.
  destruct (compare_eq_dec (c0, v0, sigma') (c, v, sigma1)); try reflexivity.
  rewrite eq_dec_if_true. reflexivity. assumption.
  rewrite eq_dec_if_false.
  destruct (compare_eq_dec v0 v); try reflexivity.
  subst. 2 : assumption.
  assert (Hin : in_state_fn (c0, v, sigma') sigma1 = true).
  { apply in_state_function. assumption. }
  rewrite Hin. simpl. reflexivity.
Qed.

Lemma non_equivocating_messages_sender : forall msg1 msg2,
  sender msg1 <> sender msg2 ->
  equivocating_messages msg1 msg2 = false.
Proof.
  intros [(c1, v1) j1] [(c2, v2) j2] Hneq. simpl in Hneq.
  unfold equivocating_messages.
  rewrite eq_dec_if_false.
  - rewrite eq_dec_if_false; try reflexivity. assumption.
  - intro Heq. inversion Heq; subst; clear Heq. apply Hneq. reflexivity.
Qed.

Lemma equivocating_messages_sender : forall msg1 msg2,
  equivocating_messages msg1 msg2 = true ->
  sender msg1 = sender msg2.
Proof.
  unfold equivocating_messages.
  intros [(c1, v1) j1] [(c2, v2) j2] Hequiv.
  simpl. 
  destruct (compare_eq_dec (c1, v1, j1) (c2, v2, j2)).
  - rewrite eq_dec_if_true in Hequiv; try discriminate. 
    assumption.
  - rewrite eq_dec_if_false in Hequiv; try discriminate; try assumption.
    destruct (compare_eq_dec v1 v2); try discriminate; try assumption. 
Qed.

Definition equivocating_message_state (msg : message) (sigma : state) : bool :=
  existsb (equivocating_messages msg) (get_messages sigma).

Lemma equivocating_message_state_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  forall msg,
  equivocating_message_state msg sigma = true -> equivocating_message_state msg sigma' = true.
Proof.
  unfold equivocating_message_state. 
  intros. rewrite existsb_exists in *. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma non_equivocating_extend : forall sigma sigma' c v,
  syntactic_state_inclusion sigma sigma' ->
  equivocating_message_state (c, v, sigma') sigma = false.
Proof.
  unfold equivocating_message_state.
  induction sigma; intros.
  - reflexivity.
  - simpl. rewrite IHsigma2.
    + rewrite equivocating_messages_comm.
      rewrite non_equivocating_messages_extend; try reflexivity.
      apply H. left. reflexivity.
    + intros x Hin. apply H. right. assumption.
Qed.

Lemma equivocating_message_state_notIn : forall msg sigma,
  ~In (sender msg) (set_map compare_eq_dec sender (get_messages sigma)) ->
  equivocating_message_state msg sigma = false.
Proof.
  intros [(c, v) j] sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  unfold equivocating_message_state. apply existsb_forall.
  intros [(cx, vx) jx] Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists (cx, vx, jx). split; try assumption. reflexivity.
Qed.

Definition equivocating_senders (sigma : state) : set V :=
  set_map compare_eq_dec sender
    (filter (fun msg => equivocating_message_state msg sigma)
      (get_messages sigma)).

Lemma equivocating_senders_nodup : forall sigma,
  NoDup (equivocating_senders sigma).
Proof.
  intros. apply set_map_nodup.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_message_state msg sigma) (get_messages sigma')).
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_message_state_incl. assumption.
Qed.

Lemma equivocating_senders_extend : forall sigma c v,
  equivocating_senders (add (c, v, sigma) to sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  assert (Heq :
    (filter (fun msg : message => equivocating_message_state msg (add (c, v, sigma)to sigma))
      (get_messages (add (c, v, sigma)to sigma))) = 
    (filter (fun msg : message => equivocating_message_state msg sigma)
      (get_messages sigma))); try (rewrite Heq; reflexivity).
    simpl.
  assert
    (Hequiv : equivocating_message_state (c, v, sigma) (add (c, v, sigma)to sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros. rewrite equivocating_messages_comm.
    destruct H as [Heq | Hin].
    - subst. unfold equivocating_messages.
      rewrite eq_dec_if_true; reflexivity.
    - apply non_equivocating_messages_extend. assumption.
  }
  apply filter_eq_fn. intros. unfold equivocating_message_state. split; intros
  ; apply existsb_exists in H0; apply existsb_exists
  ; destruct H0 as [msg [Hin Hmsg]]; exists msg; split; try assumption.
  - simpl in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    exfalso. subst.
    apply (non_equivocating_messages_extend _ _ c v) in H.
    rewrite Hmsg in H. inversion H.
  - right. assumption.
Qed.

Lemma equivocating_senders_single : forall sigma c v j,
  ~In v (set_map compare_eq_dec sender (get_messages sigma)) ->
  set_eq (equivocating_senders (add_in_sorted_fn (c, v, j) sigma)) (equivocating_senders sigma).
Proof.
  intros.
  unfold equivocating_senders. intros.
  split; intros v' Hin
  ; apply set_map_exists; apply set_map_exists in Hin
  ; destruct Hin as [[(cx, vx) jx] [Hin Heq]]
  ; simpl in Heq; subst
  ; exists (cx, v', jx)
  ; simpl; split; try reflexivity
  ; apply filter_In; apply filter_In in Hin
  ; destruct Hin as [Hin HEquiv]
  ; unfold equivocating_message_state in HEquiv
  ; apply existsb_exists in HEquiv
  ; destruct HEquiv as [[(cy, vy) jy] [Hiny HEquiv]]
  .
  - apply in_state_add_in_sorted_iff in Hiny. apply in_state_add_in_sorted_iff in Hin.
    destruct Hin.
    + exfalso. inversion H0; subst; clear H0.
      assert (Hnequiv : equivocating_messages (c, v, j) (cy, vy, jy) = false)
      ;try (rewrite Hnequiv  in HEquiv; inversion HEquiv); clear HEquiv.
      destruct Hiny.
      * rewrite H0. unfold equivocating_messages. rewrite eq_dec_if_true; reflexivity.
      * apply non_equivocating_messages_sender. simpl. intro; subst. apply H.
        apply set_map_exists. exists (cy, vy, jy). split; try reflexivity; assumption.
    + split; try assumption. unfold equivocating_message_state.
      apply existsb_exists. exists (cy, vy, jy).
      destruct Hiny.
      * exfalso. inversion H1; subst; clear H1. apply H.
        apply set_map_exists. exists (cx, v', jx). split; try assumption. simpl.
        apply equivocating_messages_sender in HEquiv. simpl in HEquiv. assumption.
      * split; assumption.
  -  split.
    + apply in_state_add_in_sorted_iff. right. assumption.
    + unfold equivocating_message_state. apply existsb_exists.
      exists (cy, vy, jy). split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.



Definition fault_weight_state (sigma : state) : R := sum_weights (equivocating_senders sigma).

Lemma sum_weights_in : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove compare_eq_dec v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (eq_dec_left compare_eq_dec v). rewrite H. reflexivity.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (compare_eq_dec v a); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc. 
    apply Rplus_eq_compat_l. apply IHvs; assumption.
Qed.

Lemma sum_weights_incl : forall vs vs',
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  intros vs vs'. generalize dependent vs.
  induction vs'; intros.
  - apply incl_empty in H1; subst. apply Rle_refl.
  - inversion H0; subst; clear H0.
    destruct (in_dec compare_eq_dec a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup compare_eq_dec a). assumption.
      * assumption.
      * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
        destruct Hrem as [Hin Hxa].
        apply H1 in Hin. destruct Hin; try assumption.
        exfalso; subst. apply Hxa. reflexivity.
      * assumption.
    + simpl. apply Rle_trans with (sum_weights vs').
      * apply IHvs'; try assumption.
        intros x Hin. apply H1 in Hin as Hin'. destruct Hin'; try assumption.
        exfalso; subst. apply n. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. destruct weight. simpl. auto. 
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

(** Proof obligations from CBC_protocol **)
Lemma equivocation_weight_compat : forall (s1 s2 : sorted_state), (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R. 
Proof. 
  intros s1 s2.
  assert (H_useful := fault_weight_state_incl s1 (state_union s1 s2)).
  spec H_useful.
  red. unfold state_union.
  assert (H_useful' := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_useful' as [_ useful]. intros x H_in.
  spec useful x. spec useful. unfold messages_union.
  rewrite in_app_iff. tauto.
  assumption.
  replace (state_union s2 s1) with (state_union s1 s2) by apply sorted_state_union_comm.
  assumption. 
Qed.

(* From protocol_states.v *)
Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    syntactic_state_inclusion sigma1 sigma2.

(** The valid message condition **)

Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(** The fault tolerance condition **)

Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition (next msg Empty).
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_message_state. simpl.
  unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. destruct t_full.
  simpl; auto.
Qed.

Lemma fault_tolerance_condition_subset : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall c v sigma sigma',
      protocol_state sigma -> 
      protocol_state sigma' ->
      full_node_condition sigma sigma' ->
      valid_estimate_condition c sigma ->
      fault_tolerance_condition (add_in_sorted_fn (c, v, sigma) sigma') ->
      protocol_state (add_in_sorted_fn (c, v, sigma) sigma').

Lemma about_sorted_state0 : protocol_state sorted_state0.
Proof.
  unfold sorted_state0. 
  simpl. apply protocol_state_empty.
Qed. 

Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition sigma.
Proof.
  intros.
  inversion H.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    simpl. apply Rge_le. destruct t_full; simpl; auto. 
  - assumption.
Qed.

Lemma protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, sigma) sigma'); try assumption.
    apply locally_sorted_message_justification. assumption.
Qed.

Lemma protocol_state_singleton : forall c v,
  valid_estimate_condition c Empty ->
  protocol_state (next (c, v, Empty) Empty).
Proof.
  intros.
  assert (Heq : add_in_sorted_fn (c, v, Empty) Empty = (next (c, v, Empty) Empty))
  ; try reflexivity.
  rewrite <- Heq.
  apply protocol_state_next; try assumption; try apply protocol_state_empty.
  - apply incl_refl. 
  - simpl. rewrite add_is_next. apply fault_tolerance_condition_singleton.
Qed.

Definition estimator_functional : Prop :=
  forall sigma c1 c2, estimator sigma c1 -> estimator sigma c2 -> c1 = c2.

Lemma protocol_state_empty_justification : forall sigma,
  protocol_state sigma ->
  sigma = Empty \/ exists msg, in_state msg sigma /\ justification msg = Empty.
Proof.
  intros. induction H; try (left; reflexivity). right.
  destruct sigma.
  - exists (c, v, Empty). split; try reflexivity.
    apply in_state_add_in_sorted_iff. left. reflexivity.
  - destruct IHprotocol_state2.
    + subst. exfalso. apply (in_empty_state (c0, v0, sigma1)). apply H1. 
      simpl. left. reflexivity.
    + destruct H4 as [msg [Hin Hj]].
      exists msg. split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.

Lemma extend_protocol_state : forall sigma,
  protocol_state sigma ->
  forall c,
  valid_estimate_condition c sigma ->
  forall v,
  protocol_state (add_in_sorted_fn (c, v, sigma) sigma).
Proof.
  intros sigma Hps c Hc v.
  constructor; try assumption; try apply incl_refl.
  unfold fault_tolerance_condition.
  apply fault_tolerance_condition_subset with (add (c,v,sigma) to sigma).
  - unfold syntactic_state_inclusion. apply set_eq_add_in_sorted.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    rewrite equivocating_senders_extend.
    apply protocol_state_fault_tolerance in Hps. assumption.
Qed.

(* This proof is taken from common_futures.v*)
Lemma about_prot_state :
  forall (s1 s2 : sorted_state),
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
    protocol_state (state_union s1 s2). 
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - unfold state_union. simpl.
    unfold messages_union. rewrite app_nil_r.
    rewrite list_to_state_sorted. assumption.
    apply protocol_state_sorted. assumption.
  - clear IHHps2_1.
    rewrite (state_union_add_in_sorted sig1 (c, v, sigma) sigma') in *
    ; try (apply (locally_sorted_message_justification c v sigma))
    ; try (apply protocol_state_sorted; assumption)
    .
    assert (protocol_state (state_union sig1 sigma')).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with
        (add_in_sorted_fn (c, v, sigma) (state_union sig1 sigma'))
      ; try assumption.
      intros msg Hin. apply set_eq_add_in_sorted. right. assumption.
    }
    constructor; try assumption.
    + intros msg Hin. apply state_union_iff.
      right. apply H. assumption.
Qed.

(* First trying to construct something of this type : *)
Class PartialOrder :=
  { A : Type;
    A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True;
    R : A -> A -> Prop;
    R_refl :> Reflexive R;
    R_trans :> Transitive R;
  }.

(* Using only an abstract instance of CBC_protocol *) 
(* Won't work because we need more stuff than is in there 
Context (H_prot : `{CBC_protocol}). *)

(* All protocol states are locally sorted, so we only need the strongest predicate here *)

Definition pstate : Type := {s : state | protocol_state s}. 

Definition pstate_proj1 (p : pstate) : state :=
  proj1_sig p. 

Coercion pstate_proj1 : pstate >-> state.

Lemma pstate_eq_dec : forall (p1 p2 : pstate), {p1 = p2} + {p1 <> p2}.
  induction p1. destruct p2.
  - destruct x.
    * destruct x0.
      + assert (p = p0) by apply proof_irrelevance; subst. left; auto.
      + right; intros contra; inversion contra.
    * destruct x0.
      + right; intros contra; inversion contra.
      + destruct (compare_eq_dec c c0), (compare_eq_dec v v0),
                 (compare_eq_dec x1 x0_1), (compare_eq_dec x2, x0_2).
        specialize (s x0_2); destruct s; subst.
        assert (p = p0) by apply proof_irrelevance; subst. left; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
        right; intros contra; inversion contra; auto.
Qed.

Lemma pstate_inhabited : exists (p1 : pstate), True.
Proof. now exists (exist protocol_state Empty protocol_state_empty). Qed. 

Definition pstate_rel : pstate -> pstate -> Prop :=
  fun p1 p2 => syntactic_state_inclusion (pstate_proj1 p1) (pstate_proj1 p2).

Lemma pstate_rel_refl : Reflexive pstate_rel.
Proof.
  red. intro p.
  destruct p as [p about_p].
  red. simpl. easy. Qed.

Lemma pstate_rel_trans : Transitive pstate_rel. 
Proof. 
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  unfold pstate_rel in *; simpl in *.
  now eapply incl_tran with (get_messages p2).
Qed.

Instance level0 : PartialOrder :=
  { A := pstate;
    A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    R := pstate_rel;
    R_refl := pstate_rel_refl;
    R_trans := pstate_rel_trans;
  }.

Class PartialOrderNonLCish `{PartialOrder} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        R a a1 /\ R a a2 /\
        ~ exists (a' : A), R a1 a' /\ R a2 a';
  }.

Instance FullNode_syntactic : CBC_protocol :=
  { consensus_values := C;  
    about_consensus_values := about_C;
    validators := V;
    about_validators := about_V;
    weight := weight;
    t := t_full;
    suff_val := suff_val_full;
    reach := reachable; 
    reach_trans := reachable_trans;
    reach_union := reach_union;
    state := sorted_state;
    state0 := sorted_state0;
    state_union_comm := sorted_state_sorted_union_comm;
    E := estimator;
    estimator_total := estimator_total; 
    prot_state := protocol_state;
    about_state0 := about_sorted_state0;
    equivocation_weight := fault_weight_state; 
    equivocation_weight_compat := equivocation_weight_compat; 
    about_prot_state := about_prot_state;
    }. 
 
(* From threshold.v *)
Lemma sufficient_validators_pivotal_ind : forall vss,
  NoDup vss ->
  (sum_weights vss > proj1_sig t_full)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights vs > proj1_sig t_full)%R /\
  exists v,
    In v vs /\
    (sum_weights (set_remove compare_eq_dec v vs) <= proj1_sig t_full)%R.
Proof.
  destruct t_full as [t about_t]; simpl in *. 
  induction vss; intros.
  simpl in H0.
  - exfalso. apply (Rge_gt_trans t) in H0; try apply threshold_nonnegative.
    apply Rgt_not_eq in H0. apply H0. reflexivity.
    destruct t_full; easy. 
  - simpl in H0. destruct (Rtotal_le_gt (sum_weights vss) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + apply NoDup_cons_iff in H. destruct H as [Hnin Hvss]. apply IHvss in H1; try assumption.
      destruct H1 as [vs [Hvs [Hincl H]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.

Lemma sufficient_validators_pivotal :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > proj1_sig t_full)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove compare_eq_dec v vs) <= proj1_sig t_full)%R.
Proof.
  destruct suff_val as [vs [Hvs Hweight]].
  apply (sufficient_validators_pivotal_ind vs Hvs) in Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  destruct t_full as [t about_t]; simpl in *.
  exists vs'. repeat (split; try assumption).
Qed.

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= proj1_sig t_full)%R /\
      (sum_weights vs > proj1_sig t_full - (proj1_sig (weight v)))%R.

Definition at_least_two_validators : Prop :=
  forall v1 : V, exists v2 : V, v1 <> v2.

Lemma exists_pivotal_message : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists v.
  subst. exists (set_remove compare_eq_dec v vs). repeat split.
  - apply set_remove_nodup. assumption.
  - intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
  - assumption.
  - rewrite (sum_weights_in v) in Hgt; try assumption.
    rewrite Rplus_comm in Hgt.
    apply (Rplus_gt_compat_r (- (proj1_sig (weight v))%R)) in Hgt.
    rewrite Rplus_assoc in Hgt.
    rewrite Rplus_opp_r in Hgt.
    rewrite Rplus_0_r in Hgt.
    assumption.
Qed.

(* This definition is doing what exactly? *) 
Definition valid_protocol_state (sigma : state) (csigma cempty : C) (vs : list V) : state :=
  fold_right
    (fun v sigma' =>
      add_in_sorted_fn (csigma, v, sigma) (add_in_sorted_fn (cempty, v, Empty) sigma'))
    sigma
    vs.

Lemma in_valid_protocol_state : forall msg sigma csigma cempty vs,
  in_state msg (valid_protocol_state sigma csigma cempty vs) ->
  in_state msg sigma \/
  exists v, In v vs /\ (msg = (csigma, v, sigma) \/ (msg = (cempty, v, Empty))).
Proof.
  intros. induction vs.
  - simpl in H. left. assumption.
  - simpl in H. rewrite in_state_add_in_sorted_iff in H. rewrite in_state_add_in_sorted_iff in H.
    destruct H as [Heq | [Heq | Hin]];
    try (right; exists a; split; try (left; reflexivity); (left; assumption) || (right; assumption)).
    apply IHvs in Hin. destruct Hin; try (left; assumption). right.
    destruct H as [v [Hin H]].
    exists v. split; try assumption. right; assumption.
Qed.

Lemma in_valid_protocol_state_rev_sigma : forall sigma csigma cempty vs,
  syntactic_state_inclusion sigma (valid_protocol_state sigma csigma cempty vs).
Proof.
  intros. intros msg Hin.
  induction vs.
  - assumption.
  - simpl. apply in_state_add_in_sorted_iff. right.
    apply in_state_add_in_sorted_iff. right.
    assumption.
Qed.

Lemma in_valid_protocol_state_rev_csigma : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (csigma, v, sigma) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Lemma in_valid_protocol_state_rev_cempty : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (cempty, v, Empty) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. right.
       apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Lemma valid_protocol_state_equivocating_senders :
  forall cempty,
  estimator Empty cempty ->
  forall v vs,
  ~ In v vs ->
  forall csigma,
  estimator (next (cempty, v, Empty) Empty) csigma ->
  set_eq (equivocating_senders (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty vs)) vs.
Proof.
  intros.
  remember (next (cempty, v, Empty) Empty) as sigma.
  remember (valid_protocol_state sigma csigma cempty vs) as sigma2.
  unfold equivocating_senders. split; intros; intros x Hin.
  - apply (set_map_exists compare_eq_dec sender)  in Hin.
    destruct Hin as [[(cx, vx) jx] [Hin Hsend]].
    simpl in Hsend. rewrite <- Hsend.
    apply filter_In in Hin. destruct Hin as [Hin Hequiv].
    apply existsb_exists in Hequiv.
    destruct Hequiv as [[(cy, vy) jy] [Hiny Hequiv]].
    rewrite Heqsigma2 in Hin.
    apply in_valid_protocol_state in Hin.
    destruct Hin as [Hin | [vv [Hin [Heq | Heq]]]]; try (inversion Heq; subst; assumption).
    exfalso. unfold equivocating_messages in Hequiv.
    rewrite Heqsigma in Hin. apply in_singleton_state in Hin.
    rewrite Heqsigma2 in Hiny.
    apply in_valid_protocol_state in Hiny.
    destruct Hiny as [Hiny | [vv [Hiny [Heq | Heq]]]].
    + rewrite Heqsigma in Hiny. apply in_singleton_state in Hiny.
      rewrite Hin in Hequiv. rewrite Hiny in Hequiv.
      rewrite eq_dec_if_true in Hequiv; try reflexivity.
      inversion Hequiv.
    + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
      rewrite eq_dec_if_false in Hequiv.
      * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
        intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
        apply H0. assumption.
      * intro. inversion H2; subst; clear H2. apply H0. assumption.
    + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
      rewrite eq_dec_if_false in Hequiv.
      * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
        intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
        apply H0. assumption.
      * intro. inversion H2; subst; clear H2. apply H0. assumption.
  - apply (set_map_exists compare_eq_dec sender).
    exists (cempty, x, Empty). simpl. split; try reflexivity.
    apply filter_In. split.
    + rewrite Heqsigma2. apply in_valid_protocol_state_rev_cempty. assumption.
    + apply existsb_exists. exists (csigma, x, sigma). split.
      * rewrite Heqsigma2. apply in_valid_protocol_state_rev_csigma. assumption.
      * unfold equivocating_messages.
        { rewrite eq_dec_if_false.
          - rewrite eq_dec_if_true; try reflexivity. apply andb_true_iff. split.
            + apply negb_true_iff. unfold in_state_fn. 
              rewrite in_state_dec_if_false; try reflexivity.
              rewrite Heqsigma. intro. apply in_singleton_state in H2.
              apply H0. inversion H2; subst; clear H2. assumption.
            + apply negb_true_iff. unfold in_state_fn. 
              rewrite in_state_dec_if_false; try reflexivity.
              apply in_empty_state.
          - intro. inversion H2; subst. inversion H5.
        }
Qed.

Lemma valid_protocol_state_ps :
  forall cempty,
  estimator Empty cempty ->
  forall vs,
  NoDup vs ->
  (sum_weights vs <= proj1_sig t_full)%R ->
  forall v,
  ~ In v vs ->
  forall csigma,
  estimator (next (cempty, v, Empty) Empty) csigma ->
  protocol_state (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty vs).
Proof.
  intros. induction vs.
  - simpl. apply protocol_state_singleton. assumption.
  - simpl. constructor.
    + apply protocol_state_singleton. assumption.
    + constructor.
      * constructor.
      * { apply IHvs.
        - apply NoDup_cons_iff in H0. destruct H0. assumption.
        - simpl in H1. apply Rle_trans with (proj1_sig (weight a) + sum_weights vs)%R; try assumption.
          rewrite <- (Rplus_0_l (sum_weights vs))  at 1.
          apply Rplus_le_compat_r.
          apply Rge_le. left. destruct (weight a). simpl. auto. 
        - intro.  apply H2. right. assumption.
        }
      * intro. simpl. intro. inversion H4.
      * assumption.
      * unfold fault_tolerance_condition. unfold fault_weight_state.
        apply Rle_trans with (sum_weights (a :: vs)); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        rewrite add_is_next.
        remember (next (cempty, v, Empty) Empty) as sigma.
        remember (valid_protocol_state sigma csigma cempty vs) as sigma2.
        { apply incl_tran with (equivocating_senders sigma2).
        - apply set_eq_proj1. apply equivocating_senders_single.
          intro. apply set_map_exists in H4.
          destruct H4 as [[(cx, vx) jx] [Hin Heq]].
          simpl in Heq. rewrite Heq in Hin. clear Heq.
          rewrite Heqsigma2 in Hin. apply in_valid_protocol_state in Hin.
          destruct Hin.
          + rewrite Heqsigma in H4. apply in_singleton_state in H4.
            apply H2. inversion H4. left; reflexivity.
          + destruct H4 as [vv [Hin Heq]]. apply NoDup_cons_iff in H0.
            destruct H0 as [Hnin Hnodup]. apply Hnin.
            destruct Heq as [Heq | Heq]; inversion Heq; subst; assumption.
        - apply incl_tran with vs.
          + apply set_eq_proj1. subst.
            apply valid_protocol_state_equivocating_senders; try assumption.
            intro. apply H2. right. assumption.
          + intros x Hin. right. assumption.
        }
    + intros msg Hin. simpl in Hin.
      destruct Hin as [Heq | Hcontra]; try inversion Hcontra; subst.
      apply in_state_add_in_sorted_iff. right.
      rewrite add_is_next.
      apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
    + assumption.
    + unfold fault_tolerance_condition. unfold fault_weight_state.
      apply Rle_trans with (sum_weights (a :: vs)); try assumption.
      apply sum_weights_incl; try assumption; try apply set_map_nodup.
      apply incl_tran with (equivocating_senders (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty (a :: vs)))
      ; try  apply incl_refl.
      apply set_eq_proj1.
      apply valid_protocol_state_equivocating_senders; try assumption.
Qed.

Definition non_trivial_pstate (P : pstate -> Prop) :=
  (exists (s1 : pstate), forall (s : pstate), pstate_rel s1 s -> P s)
  /\
  (exists (s2 : pstate), forall (s : pstate), pstate_rel s2 s -> (P s -> False)).

Program Definition singleton_pstate (c : C) (v : V) (H : valid_estimate_condition c Empty) : pstate := _.
Next Obligation. 
  exists (next (c,v,Empty) Empty).
  now apply protocol_state_singleton.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  at_least_two_validators ->
  exists (p : pstate -> Prop) , non_trivial_pstate p.
Proof.
  intro H2v. 

  (* Because E is total, we can have some consensus value for the Empty state *)
  destruct (estimator_total Empty) as [c Hc].
  
  (* There exists a configuration of pivotal validator and set of remaining validators *) 
  destruct exists_pivotal_message as [v [vs [Hnodup [Hnin [Hlt Hgt]]]]].
  (* Case analysis on this configuration of validator + rest *) 
  destruct vs as [ | v' vs].
  - (* When there is just one heavy validator *)
    (* The non-trivial property is that the lone heavy validator has sent a message *) 
    exists (in_state (c,v,Empty)).
    split.
    + assert (bleh : protocol_state (next (c,v,Empty) Empty)) by now apply protocol_state_singleton. 
      exists (exist protocol_state (next (c,v,Empty) Empty) bleh).      intros sigma H. apply H. simpl. left. reflexivity.
    + (* There must be one other validator *)
      destruct (H2v v) as [v' Hv'].
      (* The other state is one in which that validator has sent a good message *) 
      remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0) by (subst; now apply protocol_state_singleton).
      destruct (estimator_total sigma0) as [c0 Hc0].
      assert (bleh : protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0)) by (apply extend_protocol_state; assumption). 
      exists (exist protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0) bleh).
      intros sigma' H'. 
      intro.
      apply protocol_state_fault_tolerance in bleh as Hft'.
      unfold fault_tolerance_condition in Hft'.
      assert (Hnft' : (fault_weight_state sigma' > proj1_sig t_full)%R).
      { apply Rlt_le_trans with (fault_weight_state (add (c, v, Empty) to (add (c0, v, sigma0) to Empty))).
        - unfold fault_weight_state. unfold equivocating_senders. simpl.
          assert ( Hequiv : equivocating_message_state (c, v, Empty)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c0, v, sigma0). 
            split.
            - right. left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv.
          assert ( Hequiv0 : equivocating_message_state (c0, v, sigma0)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c, v, Empty). 
            split.
            - left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv0. simpl. rewrite eq_dec_if_true; try reflexivity.
          simpl. simpl in Hgt. unfold Rminus in Hgt.
          apply (Rplus_gt_compat_r (proj1_sig (weight v))) in Hgt. rewrite Rplus_assoc in Hgt.
          rewrite Rplus_0_r. rewrite Rplus_0_l in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt.
          apply Rgt_lt. assumption.
        - apply fault_weight_state_incl. unfold syntactic_state_inclusion. simpl.
          intros x Hin. destruct Hin as [Hin | [Hin | Hcontra]]; try inversion Hcontra; subst
          ; try assumption.
          unfold pstate_rel in H'. apply H'. apply in_state_add_in_sorted_iff. left. reflexivity.
      }
      unfold Rgt in Hnft'.
      apply (Rlt_irrefl (proj1_sig t_full)).
      apply Rlt_le_trans with (fault_weight_state sigma'). assumption. destruct sigma' as [sigma' about_sigma'].
      inversion about_sigma'. subst. assumption.
      simpl in *. subst. assumption. 
  - remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
    assert (Hps0 : protocol_state sigma0) by (subst; now apply protocol_state_singleton).
    destruct (estimator_total sigma0) as [c0 Hc0].
    exists (in_state (c0,v,sigma0)).
    split.
    + assert (bleh : protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0)) by (apply extend_protocol_state; assumption).
      exists (exist protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0) bleh).
      intros sigma' H'. 
      red in H'; apply H'. apply in_state_add_in_sorted_iff. left. reflexivity.
    + remember (add_in_sorted_fn (c, v, Empty) Empty) as sigma.
      simpl in Heqsigma. rewrite add_is_next in Heqsigma.
      destruct (estimator_total sigma) as [csigma Hcsigma].
      remember (valid_protocol_state sigma csigma c (v' :: vs)) as sigma2.
      assert (Hequiv2 : set_eq (equivocating_senders sigma2) (v' :: vs)). 
      { rewrite Heqsigma2. rewrite Heqsigma in *.
        apply valid_protocol_state_equivocating_senders; assumption.
      }
      assert (bleh : protocol_state sigma2) by (subst; now apply valid_protocol_state_ps).
      exists (exist protocol_state sigma2 bleh). 
      intros sigma' Hfutures.
      unfold predicate_not. intro Hin.
      red in Hfutures.
      destruct sigma' as [sigma' about_sigma']. 
      assert (Hps' := about_sigma').
      apply protocol_state_fault_tolerance in Hps'.
      { apply (fault_tolerance_condition_subset (add (c0, v, sigma0) to sigma2)) in Hps'.
        - unfold fault_tolerance_condition in Hps'.
          apply Rlt_irrefl with (proj1_sig t_full).
          apply Rlt_le_trans with (fault_weight_state (add (c0, v, sigma0)to sigma2)); try assumption.
          unfold fault_weight_state.
          unfold Rminus in Hgt. apply (Rplus_gt_compat_r (proj1_sig (weight v))) in Hgt.
          rewrite Rplus_assoc in Hgt. rewrite Rplus_opp_l, Rplus_0_r in Hgt.
          apply Rgt_lt. apply Rge_gt_trans with (sum_weights (v' :: vs) + (proj1_sig (weight v)))%R; try assumption.
          rewrite Rplus_comm.
          assert (Hsum : (proj1_sig (weight v) + sum_weights (v' :: vs))%R = sum_weights (v :: v' :: vs))
          ; try reflexivity; try rewrite Hsum.
          apply Rle_ge. apply sum_weights_incl; try apply set_map_nodup; try (constructor; assumption).
          intros vv Hvin. unfold equivocating_senders.
          apply set_map_exists.
          exists (c, vv, Empty).
          split; try reflexivity.
          apply filter_In.
          split; destruct Hvin as [Heq | Hvin]; subst; apply existsb_exists || right.
          + apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
          + apply in_valid_protocol_state_rev_cempty; assumption.
          + exists (c0, vv, add_in_sorted_fn (c, v', Empty) Empty).
            split ; try (left; reflexivity).
            simpl. unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
                   ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * rewrite add_is_next in H. apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. left. reflexivity.
            * inversion H.
            * intro. inversion H.
          + exists (csigma, vv, (next (c, v, Empty) Empty)). split
                                                        ; try (right; apply in_valid_protocol_state_rev_csigma; assumption).
            unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
            ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. assumption.
            * inversion H.
            * intro. inversion H.
        - intros msg Hmin.
          destruct Hmin as [Heq | Hmin].
          * subst. assumption.
          * now apply Hfutures. 
   }
Qed.

Theorem no_local_confluence_prot_state :
  at_least_two_validators -> 
  exists (a a1 a2 : pstate),
        pstate_rel a a1 /\ pstate_rel a a2 /\
        ~ exists (a' : pstate), pstate_rel a1 a' /\ pstate_rel a2 a'. 
Proof.
  intro H_vals. 
  assert (H_useful := non_triviality_decisions_on_properties_of_protocol_states H_vals).
  destruct H_useful as [P [[ps1 about_ps1] [ps2 about_ps2]]].
  exists (exist protocol_state Empty protocol_state_empty).
  exists ps1, ps2. repeat split; try (red; simpl; easy).
  intro Habsurd. destruct Habsurd as [s [Hs1 Hs2]].
  spec about_ps1 s Hs1.
  spec about_ps2 s Hs2. contradiction.
Qed.

Parameter inhabited_two : at_least_two_validators. 

Instance level1 : PartialOrderNonLCish :=
  { no_local_confluence_ish := no_local_confluence_prot_state inhabited_two; }.




