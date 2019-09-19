Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts Classical.
Import ListNotations.   
From Casper  
Require Import preamble ListExtras ListSetExtras RealsExtras.

Variables (C V : Type).
Variables (about_C : `{StrictlyComparable C})
          (about_V : `{StrictlyComparable V}). 

Parameter two_senders : exists (v1 v2 : V), v1 <> v2.

Lemma distinct_sender_total : forall v1 : V, exists v2 : V, v1 <> v2.
Proof.
  intros.
  destruct two_senders  as [v1' [v2' Hneq]].
  destruct (compare_eq_dec v1 v1') eqn:Heq.
  - subst. exists v2'. assumption.
  - exists v1'. assumption.
Qed.

Definition get_distinct_sender (v : V) :=
  proj1_sig (choice V (fun v' => v <> v') (distinct_sender_total v)).

Definition get_distinct_sender_correct (v : V) :=
  proj2_sig (choice V (fun v' => v <> v') (distinct_sender_total v)).

Lemma get_distinct_sender_correct' :
  forall v, get_distinct_sender v <> v. 
Proof.
  intros. unfold get_distinct_sender.
  assert (H_useful := get_distinct_sender_correct v).
  simpl in *.
  intro H_absurd.
  apply H_useful; symmetry; assumption.
Qed.

Definition pos_R := {r : R | (r > 0)%R}.

Parameter weight : V -> pos_R.

Definition weight_proj1_sig (w : pos_R) : R := proj1_sig w.

Coercion weight_proj1_sig : pos_R >-> R.

Definition sum_weights (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l. 

Parameters (t_full : {r | (r >= 0)%R})
           (suff_val_full : exists vs, NoDup vs /\ (sum_weights vs > (proj1_sig t_full))%R).

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

(* Constructing a StrictlyComparable message type *) 
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

Definition in_state_fn (msg : message) (sigma : state) : bool :=
  match in_state_dec msg sigma with
  | left _ => true
  | right _ => false
  end.

Lemma in_state_correct :
  forall msg s,
    in_state_fn msg s = true <-> in_state msg s.
Proof.
  intros msg sigma; split; intro; destruct (in_state_dec msg sigma) eqn:Hin;
  unfold in_state_fn in *.
  - assumption.
  - exfalso. rewrite Hin in H. discriminate.
  - rewrite Hin. reflexivity.
  - exfalso; apply n; apply H.
Qed.

Lemma in_state_correct' :
  forall msg s,
    in_state_fn msg s = false <-> ~ in_state msg s. 
Proof.
  intros; assert (H_useful := in_state_correct).
  now apply mirror_reflect_curry. 
Qed.

Lemma in_state_next_iff : forall msg msg1 sigma1,
  in_state msg (next msg1 sigma1) <-> msg1 = msg \/ in_state msg sigma1.
Proof.
  unfold in_state. intros. rewrite get_messages_next. simpl.
  split; intros; destruct H; (left; assumption) || (right; assumption).
Qed.

Lemma in_singleton_state : forall msg msg',
  in_state msg (next msg' Empty) -> msg = msg'.
Proof.
  intros. apply in_state_next_iff in H.
  destruct H; subst; try reflexivity.
  exfalso. apply (in_empty_state _ H).
Qed.

Lemma not_extx_in_x : forall c v j j',
  syntactic_state_inclusion j' j ->
   ~ in_state (c, v, j) j'.
Proof.
  induction j'; intros;  unfold in_state; simpl; intro; try assumption.
  destruct H0.
  - inversion H0; subst; clear H0.
    apply IHj'1; try apply incl_refl. apply H. left. reflexivity.
  - apply IHj'2; try assumption.
    intros msg Hin. apply H. right. assumption.
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
    rewrite in_state_next_iff in H0. destruct H0; subst.
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

Lemma add_preserves_message_membership :
  forall msg s,
    in_state msg s ->
    forall c v j,
      in_state msg (add_in_sorted_fn (c,v,j) s). 
Proof.
  intros.
  assert (H_useful := set_eq_add_in_sorted (c,v,j) s).
  destruct H_useful as [_ H_useful].
  spec H_useful msg; spec H_useful. 
  right; assumption.
  assumption.
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
  ]; intros [(c', v') j'] HIn; rewrite in_state_next_iff in HIn
  ; destruct HIn as [Hin1 | Hin2]
  ; try (right; assumption)
  ; try (inversion Hin1; subst; left; reflexivity)
  .
  - right. apply in_state_next_iff. right. assumption.
  - right. apply in_state_next_iff. inversion Hin1; clear Hin1; subst. left. reflexivity.
  - apply H_H in Hin2. destruct Hin2 as [HInEq | HIn'].
    + left. assumption.
    + right. apply in_state_next_iff. right. assumption.
Qed.

Lemma add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
  induction sigma; intros; repeat rewrite add_is_next in *.
  - exfalso. apply (in_empty_state _ H0).
  - rewrite in_state_next_iff in H0. destruct H0.
    + subst. constructor.
    + apply (locally_sorted_first (c, v, sigma1)) in H0 as Hlt; try assumption.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.
(* End from adequacy, sort.v *)

Lemma add_in_sorted_ignore :
  forall msg (s : state),
    locally_sorted s -> 
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

(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> C -> Prop)
           (estimator_total : forall s : state, exists c : C, estimator s c). 

Definition get_estimate (s : state) :=
  proj1_sig (choice C (estimator s) (estimator_total s)).

Definition get_estimate_correct (s : state) :=
  proj2_sig (choice C (estimator s) (estimator_total s)). 

(* Defining message equivocation, computationally and propositionally *) 
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

Definition equivocating_messages_prop (msg1 msg2 : message) : Prop :=
  msg1 <> msg2 /\ sender msg1 = sender msg2 /\ ~ in_state msg1 (justification msg2) /\ ~ in_state msg2 (justification msg1).

Lemma equivocating_messages_sender :
  forall msg1 msg2,
    equivocating_messages msg1 msg2 = true -> sender msg1 = sender msg2. 
Proof.
  unfold equivocating_messages. 
  intros [(c1, v1) j1] [(c2, v2) j2] H. 
  simpl.
  destruct (compare_eq_dec (c1, v1, j1) (c2, v2, j2)).
  rewrite eq_dec_if_true in H. 
  inversion H.
  assumption. 
  rewrite eq_dec_if_false in H.
  destruct (compare_eq_dec v1 v2).
  assumption. inversion H. assumption.
Qed.

Lemma equivocating_messages_correct :
  forall (msg1 msg2 : message),
    equivocating_messages msg1 msg2 = true <-> equivocating_messages_prop msg1 msg2. 
Proof. 
  intros [[c1 v1] j1] [[c2 v2] j2]; split; intro H.
  - repeat split.
    + (* Proving inequality obligation *)
      intro H_absurd.
      unfold equivocating_messages in H.
      rewrite eq_dec_if_true in H.
      inversion H. assumption. 
    + (* Proving sender obligation *)
      now apply equivocating_messages_sender.
    + (* Proving msg1 is not in msg2's justification *)
      intro H_absurd.
      apply in_state_correct in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd. rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      simpl in H. inversion H.
      inversion H. assumption.
    + (* Proving msg2 is not in msg1's justification *)
      intro H_absurd. apply in_state_correct in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd. rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      rewrite andb_false_r in H. inversion H.
      inversion H. assumption. 
  - destruct H as [H_neq [H_sender [H_in1 H_in2]]].
    apply in_state_correct' in H_in1.
    apply in_state_correct' in H_in2.
    simpl in H_sender.
    unfold equivocating_messages.
    destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
    contradiction.
    rewrite eq_dec_if_false.
    destruct (compare_eq_dec v1 v2).
    simpl in H_in1. simpl in H_in2.
    rewrite H_in1. rewrite H_in2.
    tauto. contradiction. assumption.
Qed.

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

Lemma equivocating_messages_prop_swap :
  forall msg1 msg2,
    equivocating_messages_prop msg1 msg2 <-> equivocating_messages_prop msg2 msg1.
Proof.
  intros; rewrite <- equivocating_messages_correct.
  rewrite <- equivocating_messages_correct.
  rewrite equivocating_messages_comm.
  tauto.
Qed. 
  
(* The intuition is we can never satisfy that neither messages are contained in each other's justifications. *) 
Lemma non_equivocating_messages_extend : forall msg sigma1 c v,
  In msg (get_messages sigma1) ->
  equivocating_messages msg (c, v, sigma1) = false.
Proof.
  intros [(c0, v0) sigma']; intros.
  unfold equivocating_messages.
  destruct (compare_eq_dec (c0, v0, sigma') (c, v, sigma1)).  
  - (* In the case that these two messages are equal, they cannot be equivocating *)
    now rewrite eq_dec_if_true. 
  - (* In the case that these messages are not equal, *)
    rewrite eq_dec_if_false.
    (* When their senders are equal *)
    destruct (compare_eq_dec v0 v).  
    + subst. apply in_state_correct in H.
      rewrite H. tauto.
    + reflexivity.
    + assumption. 
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

Definition equivocating_in_state (msg : message) (sigma : state) : bool :=
  existsb (equivocating_messages msg) (get_messages sigma).

Definition equivocating_in_state_prop (msg : message) (s : state) : Prop :=
  exists msg', in_state msg' s /\ equivocating_messages_prop msg msg'. 

Lemma equivocating_in_state_correct :
  forall msg s, equivocating_in_state msg s = true <-> equivocating_in_state_prop msg s.
Proof.
  intros msg s.
  split; intro H.
  - unfold equivocating_in_state in H.
    rewrite existsb_exists in H.
    destruct H as [msg' [H_in H_equiv]].
    exists msg'. split. assumption. rewrite <- equivocating_messages_correct. assumption.
  - destruct H as [msg' [H_in H_equiv]].
    apply existsb_exists.
    exists msg'; split. assumption.
    rewrite equivocating_messages_correct. assumption.
Qed.

Lemma equivocating_in_state_correct' :
  forall msg s, equivocating_in_state msg s = false <-> ~ equivocating_in_state_prop msg s.
Proof.
  intros. 
  apply mirror_reflect_curry.
  exact equivocating_in_state_correct.
Qed.

Lemma equivocating_in_state_incl :
  forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  forall msg,
    equivocating_in_state_prop msg sigma ->
    equivocating_in_state_prop msg sigma'.
Proof.
  intros. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma equivocating_in_state_not_seen :
  forall msg sigma,
  ~ In (sender msg) (set_map compare_eq_dec sender (get_messages sigma)) ->
  ~ equivocating_in_state_prop msg sigma.  
Proof.
  intros [(c, v) j] sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  rewrite <- equivocating_in_state_correct'. 
  apply existsb_forall.
  intros [(cx, vx) jx] Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists (cx, vx, jx). split; try assumption. reflexivity.
Qed.

Definition equivocating_senders (sigma : state) : set V :=
  set_map compare_eq_dec sender
    (filter (fun msg => equivocating_in_state msg sigma)
      (get_messages sigma)).

Definition equivocating_senders_prop (s : state) (lv : set V) :=
  forall v, In v lv <-> exists msg, in_state msg s /\ sender msg = v /\ equivocating_in_state_prop msg s. 

Lemma equivocating_senders_correct : forall s,
    equivocating_senders_prop s (equivocating_senders s).
Proof.
  intros s v; split; intro H. 
  - (* Left direction *)
    apply set_map_exists in H.
    destruct H as [msg [H_in H_sender]].
    exists msg.
    apply filter_In in H_in.
    destruct H_in. repeat split; try assumption.
    rewrite <- equivocating_in_state_correct.
    assumption.
  - destruct H as [msg [H_in [H_sender H_equiv]]]. 
    unfold equivocating_senders.
    rewrite <- H_sender.
    apply set_map_in.
    rewrite filter_In. split.
    assumption. rewrite equivocating_in_state_correct.
    assumption.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl.
  apply incl_tran with (filter (fun msg : message => equivocating_in_state msg sigma) (get_messages sigma')).
  - apply filter_incl; assumption.
  - intros v H_in.
    rewrite filter_In in *.
    destruct H_in. split. assumption.
    rewrite equivocating_in_state_correct in *.
    now apply equivocating_in_state_incl with sigma.
Qed. 

Lemma equivocating_senders_extend : forall sigma c v,
  equivocating_senders (add (c, v, sigma) to sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  (* Why doesn't the suff tactic work *)
  assert (H_suff : 
    (filter (fun msg : message => equivocating_in_state msg (add (c, v, sigma)to sigma))
      (get_messages (add (c, v, sigma)to sigma))) = 
    (filter (fun msg : message => equivocating_in_state msg sigma)
      (get_messages sigma))); try (rewrite H_suff; reflexivity).
  simpl.
  assert
    (Hequiv : equivocating_in_state (c, v, sigma) (add (c, v, sigma) to sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros.
    rewrite equivocating_messages_comm.
    destruct H as [Heq | Hin].
    - subst. unfold equivocating_messages.
      rewrite eq_dec_if_true; reflexivity.
    - apply non_equivocating_messages_extend. assumption.
  }
  apply filter_eq_fn. intros. unfold equivocating_in_state. split; intros
  ; apply existsb_exists in H0; apply existsb_exists
  ; destruct H0 as [msg [Hin Hmsg]]; exists msg; split; try assumption.
  - simpl in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    exfalso. subst.
    apply (non_equivocating_messages_extend _ _ c v) in H.
    rewrite Hmsg in H. inversion H.
  - right. assumption.
Qed.

Lemma equivocating_senders_unseen : forall sigma c v j,
  ~ In v (set_map compare_eq_dec sender (get_messages sigma)) ->
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
  ; unfold equivocating_in_state in HEquiv
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
    + split; try assumption. unfold equivocating_in_state.
      apply existsb_exists. exists (cy, vy, jy).
      destruct Hiny.
      * exfalso. inversion H1; subst; clear H1. apply H.
        apply set_map_exists. exists (cx, v', jx). split; try assumption. simpl.
        apply equivocating_messages_sender in HEquiv. simpl in HEquiv. assumption.
      * split; assumption.
  -  split.
    + apply in_state_add_in_sorted_iff. right. assumption.
    + unfold equivocating_in_state. apply existsb_exists.
      exists (cy, vy, jy). split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.

(* Lifting parameterization from set V to states *) 
Definition fault_weight_state (sigma : state) : R :=
  sum_weights (equivocating_senders sigma).

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

Lemma sum_weights_app : forall vs vs',
  sum_weights (vs ++ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  induction vs; intros; simpl.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite IHvs. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply set_map_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

(* Justification subset condition *) 
Definition incl_messages (s1 s2 : state) : Prop :=
  incl (get_messages s1) (get_messages s2).

(* Estimator approval condition *) 
Definition valid_estimate (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(* The not overweight condition *)
Definition not_heavy (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

(* States following Empty states are never overweight *) 
Lemma not_heavy_single : forall msg,
  not_heavy (next msg Empty).
Proof.
  intros [(c, v) j].
  unfold not_heavy, fault_weight_state, equivocating_senders.
  simpl. unfold equivocating_in_state. simpl.
  unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. destruct t_full.
  simpl; auto.
Qed.

(* If a state is not overweight, none of its subsets are *) 
Lemma not_heavy_subset : forall s s',
  syntactic_state_inclusion s s' ->
  not_heavy s' ->
  not_heavy s.
Proof.
  red.
  intros.
  apply Rle_trans with (fault_weight_state s'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

(* Valid protocol state definition *) 
Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall s j, protocol_state s ->
                                  protocol_state j ->
                                  incl_messages j s ->
                                  forall c v,
                                    valid_estimate c j ->
                                    not_heavy (add_in_sorted_fn (c,v,j) s) ->
                                    protocol_state (add_in_sorted_fn (c,v,j) s).

Lemma nil_empty_state :
  forall s, get_messages s = [] -> s = Empty. 
Proof.
  intros s H_nil.
  induction s. reflexivity.
  inversion H_nil.
Qed.

(** Facts about protocol states as traces **)
(* All protocol states are sorted by construction *) 
Lemma protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, j) s); try assumption.
    apply locally_sorted_message_justification. assumption.
Qed.

(* All protocol states are not too heavy *) 
Lemma protocol_state_not_heavy : forall s,
  protocol_state s ->
  not_heavy s.
Proof.
  intros.
  inversion H.
  - unfold not_heavy. unfold fault_weight_state.
    simpl. apply Rge_le. destruct t_full; simpl; auto. 
  - assumption.
Qed.

(* All messages in protocol states are estimator approved *) 
Lemma protocol_state_valid_estimate :
  forall s,
    protocol_state s ->
    forall msg,
      in_state msg s ->
      valid_estimate (estimate msg) (justification msg).
Proof.
  intros s H_ps msg H_in.
  induction H_ps. 
  inversion H_in.
  rewrite in_state_add_in_sorted_iff in H_in.
  destruct H_in as [H_eq | H_in].
  subst.
  assumption.
  now apply IHH_ps1.
Qed.

(* All singleton states are protocol states *) 
Lemma protocol_state_singleton : forall c v,
  estimator Empty c ->
  protocol_state (next (c, v, Empty) Empty).
Proof.
  intros.
  assert (Heq : add_in_sorted_fn (c, v, Empty) Empty = (next (c, v, Empty) Empty)); try reflexivity.
  rewrite <- Heq.
  apply protocol_state_next; try assumption; try apply protocol_state_empty.
  - apply incl_refl. 
  - simpl. rewrite add_is_next. apply not_heavy_single.
Qed.

(* All protocol states are either empty or contain a message with an empty justification *) 
Lemma protocol_state_start_from_empty : forall s,
  protocol_state s ->
  s = Empty \/ exists msg, in_state msg s /\ justification msg = Empty.
Proof.
  intros. induction H; try (left; reflexivity). right.
  destruct s.
  - exists (c, v, Empty). split; try reflexivity.
    apply in_state_add_in_sorted_iff. left.
    red in H1; simpl in H1.
    apply incl_empty in H1.
    apply nil_empty_state in H1.
    subst; reflexivity.
  - destruct IHprotocol_state2.
    + subst. destruct IHprotocol_state1.
      inversion H4.
      destruct H4 as [msg [H_in H_empty]].
      exists msg. 
      repeat split. apply in_state_add_in_sorted_iff.
      right; assumption. assumption.
    + destruct H4 as [msg [H_in H_empty]].
      exists msg. 
      repeat split. apply in_state_add_in_sorted_iff.
      right. apply H1. assumption. assumption.
Qed. 

(* Recording entire histories preserves protocol state-ness *)
Lemma copy_protocol_state : forall s,
  protocol_state s ->
  forall c,
    estimator s c->
    forall v,
      protocol_state (add_in_sorted_fn (c, v, s) s).
Proof.
  intros sigma Hps c Hc v.
  constructor; try assumption; try apply incl_refl.
  unfold not_heavy.
  apply not_heavy_subset with (add (c,v,sigma) to sigma).
  - unfold syntactic_state_inclusion. apply set_eq_add_in_sorted.
  - unfold not_heavy. unfold fault_weight_state.
    rewrite equivocating_senders_extend.
    apply protocol_state_not_heavy in Hps. assumption.
Qed. 

(* Two protocol states if not too heavy combined can be combined into a protocol state. *) 
Lemma union_protocol_states :
  forall (s1 s2 : state),
    locally_sorted s1 ->
    locally_sorted s2 -> 
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
    protocol_state (state_union s1 s2). 
Proof.
  intros s1 s2 about_s1 about_s2 Hps1 Hps2.
  induction Hps2; intros.
  - unfold state_union. simpl. 
    unfold messages_union. rewrite app_nil_r.
    rewrite list_to_state_sorted. assumption.
    apply protocol_state_sorted. assumption.
  - replace (state_union s1 (add_in_sorted_fn (c,v,j) s)) with (add_in_sorted_fn (c,v,j) (state_union s1 s)) in *.
    2 : { rewrite (state_union_add_in_sorted s1 (c, v, j) s).
          reflexivity. 
          now apply protocol_state_sorted.
          now apply protocol_state_sorted.
          apply (locally_sorted_message_justification c v j).
          now apply protocol_state_sorted. }
    apply protocol_state_next; try assumption. 
    apply IHHps2_1. 
    now apply protocol_state_sorted. apply not_heavy_subset with (add_in_sorted_fn (c, v, j) (state_union s1 s)); try assumption.
    intros msg H_in. apply set_eq_add_in_sorted.
    right; assumption.
    intros msg H_in. 
    apply state_union_iff.
    right. apply H. assumption.
Qed.

(* All messages in a protocol state have correct subsetted justifications *)
Lemma message_subset_correct :
  forall s, protocol_state s ->
       forall msg, In msg (get_messages s) ->
              incl_messages (justification msg) s.  
Proof.
  intros s H_ps msg H_in_msg m H_in.
  induction H_ps; subst. 
  inversion H_in_msg.
  assert (H_useful := in_state_add_in_sorted_iff m (c,v,j) s).
  rewrite H_useful. clear H_useful.
  apply in_state_add_in_sorted_iff in H_in_msg. 
  destruct H_in_msg as [H_eq | H_in_msg].
  - right. subst; simpl in H_in.
    spec H m H_in.
    assert (H_useful := set_eq_add_in_sorted (c,v,j) s).
    destruct H_useful as [H_left H_right].
    spec H_right (c,v,j) (in_eq (c,v,j) (get_messages s)).
    assumption. 
  - right; apply IHH_ps1.
    assumption.
Qed.

(** Lemmas about justifications of messages contained within protocol states, i.e. "past" protocol states **) 
(* Any justification of protocol state messages are themselves protocol states *) 
Lemma protocol_state_justification :
  forall s, protocol_state s ->
       forall msg, in_state msg s ->
              protocol_state (justification msg). 
Proof.
  intros s H_ps msg H_in.
  induction H_ps.
  - inversion H_in. 
  - apply in_state_add_in_sorted_iff in H_in.
    destruct H_in as [left | right].
    + subst. simpl. assumption. 
    + now apply IHH_ps1.
Qed.

(* All justifications of protocol state messages are themselves protocol states *) 
Lemma protocol_state_all_justifications :
  forall s, protocol_state s ->
       Forall protocol_state (map justification (get_messages s)).
Proof.
  intros s H_ps.
  induction H_ps; apply Forall_forall; intros x H_in.  
  - inversion H_in. 
  - rewrite in_map_iff in H_in.
    destruct H_in as [msg [H_justif H_justif_in]].
    subst.
    apply (protocol_state_justification (add_in_sorted_fn (c,v,j) s)); try constructor; assumption. 
Qed.

(* No protocol state can contain a message that contains itself as the justification *) 
Theorem no_self_justification :
  forall j, protocol_state j ->
       forall c v, in_state (c, v, j) j -> False. 
Proof.
  intros j H_prot c v H_in.
  induction H_prot.
  - inversion H_in. 
  - rewrite in_state_add_in_sorted_iff in H_in. 
    destruct H_in as [H_eq | H_in].
    + inversion H_eq.
      subst. apply IHH_prot2. rewrite <- H5 at 2.
      unfold in_state.
      assert (H_useful := set_eq_add_in_sorted (c0,v0,j) s).
      red in H_useful. destruct H_useful as [H_left H_right].
      spec H_right (c0,v0,j) (in_eq (c0,v0,j) (get_messages s)).
      assumption.
    + apply (not_extx_in_x c v (add_in_sorted_fn (c0,v0,j) s) s).
      red. intros msg H_msg_in.
      assert (H_useful := set_eq_add_in_sorted (c0,v0,j) s).
      destruct H_useful as [_ H_useful].
      spec H_useful msg. spec H_useful.
      right; assumption. assumption.
      assumption.
Qed.

Lemma messages_equivocating_senders_eq :
  forall s1 s2,
    set_eq (get_messages s1) (get_messages s2) ->
    set_eq (equivocating_senders s1) (equivocating_senders s2). 
Proof.
  intros s1 s2 [H_eq1 H_eq2].
  apply set_map_eq.
  assert (H_equiv1 := equivocating_in_state_incl s1 s2 H_eq1).
  assert (H_equiv2 := equivocating_in_state_incl s2 s1 H_eq2).
  split; intros msg H_msg_in.
  - apply filter_in.
    spec H_eq1 msg. spec H_eq1.
    apply filter_In in H_msg_in.
    destruct H_msg_in as [H_goal _]; assumption.
    assumption.
    apply filter_In in H_msg_in.
    destruct H_msg_in as [_ H_useful].
    rewrite equivocating_in_state_correct in H_useful.
    spec H_equiv1 msg H_useful.
    rewrite equivocating_in_state_correct.
    assumption.
  - apply filter_in.
    spec H_eq2 msg. spec H_eq2.
    apply filter_In in H_msg_in.
    destruct H_msg_in as [H_goal _]; assumption.
    assumption.
    apply filter_In in H_msg_in.
    destruct H_msg_in as [_ H_useful].
    rewrite equivocating_in_state_correct in H_useful.
    spec H_equiv2 msg H_useful.
    rewrite equivocating_in_state_correct.
    assumption.
Qed.

Lemma set_eq_empty :
  forall (lv : list V),
    set_eq lv [] -> lv = [].
Proof.
  intros.
  destruct lv as [|hd tl].
  - reflexivity. 
  - destruct H.
    spec H hd (in_eq hd tl).
    inversion H.
Qed.

Lemma equivocating_senders_empty :
  equivocating_senders Empty = []. 
Proof.
  unfold equivocating_senders.
  simpl. reflexivity.
Qed.

Lemma equivocating_senders_extend' :
  forall (s : state) (c : C) (v : V) (j : state),
    In v (equivocating_senders s) ->
    set_eq (equivocating_senders (add (c, v, j) to s))
           (equivocating_senders s). 
Proof.
  intros.
  unfold equivocating_senders.
  split; intros v0 H_in; apply set_map_exists.
  - (* Arbitrary v0 is an equivocating sender in the new state *)
    apply set_map_exists in H_in.
    (* Arbitrary v0 has sent an equivocating_in_state message in the new state *) 
    destruct H_in as [msg [H_in H_sender]].
    apply filter_In in H_in.
    simpl in H_in.
    destruct H_in as [H_in H_equiv].
    rewrite equivocating_in_state_correct in H_equiv.
    destruct H_equiv as [msg' [H_in' H_equiv]].
    (* This message has an equivocation partner *)
    (* Both of these messages are in the new state - case analysis on each of them with the hd element *) 
    destruct H_in as [H_hd | H_tl].
    + (* In the case that the first equivocating message is the hd  *) 
      subst.
      destruct H_in' as [H_absurd | H_in'].
      * (* In the case that the second equivocating message is also the hd, we have a contradiction *)
        subst. inversion H_equiv; contradiction.
      * (* In the case that the second equivocarting message is in the tl, *)
        apply equivocating_senders_correct in H.
        destruct H as [msg0 [H_in0 [H_sender0 H_equiv0]]].
        exists msg0. rewrite filter_In.
        repeat split; try assumption.
        apply equivocating_in_state_correct.
        assumption.
    + (* In the case that the first equivocating message is in the tl, *)
      destruct H_in' as [H_hd' | H_tl'].
      * (* In the case that the second equivocating message is the hd, *)
        subst.
        apply equivocating_senders_correct in H.
        destruct H as [msg0 [H_in0 [H_sender0 H_equiv0]]].
        exists msg0. rewrite filter_In.
        repeat split; try assumption.
        apply equivocating_in_state_correct.
        assumption. subst.
        destruct H_equiv as [_ [H_sender _]].
        simpl in H_sender. symmetry; assumption.
      * (* In the case that the second equivocating message is in the tl, *)
        exists msg. 
        rewrite filter_In.
        repeat split; try assumption.
        rewrite equivocating_in_state_correct.
        exists msg'; split; try assumption.
  - (* Arbitrary v0 is an equivocating sender in the old state *)
    apply set_map_exists in H_in. 
    destruct H_in as [msg0 [H_in0 H_sender0]].
    apply filter_In in H_in0. 
    destruct H_in0 as [H_in0 H_equiv0].
    exists msg0. rewrite filter_In.
    repeat split.
    right. assumption.
    apply equivocating_in_state_correct.
    apply equivocating_in_state_incl with s.
    { intros msg H_msg_in.
      right; assumption. }
    apply equivocating_in_state_correct.
    assumption.
    assumption.
Qed.

Lemma set_eq_nodup_sum_weight_eq :
  forall (lv1 lv2 : list V),
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2. 
Proof.
  intros lv1 lv2 H_nodup1 H_nodup2 [H_eq_l H_eq_r].
  assert (H_useful := sum_weights_incl lv1 lv2 H_nodup1 H_nodup2 H_eq_l).
  assert (H_useful' := sum_weights_incl lv2 lv1 H_nodup2 H_nodup1 H_eq_r).
  now apply Rle_antisym. 
Qed.

Lemma equivocating_senders_fault_weight_eq :
  forall s1 s2,
    set_eq (equivocating_senders s1) (equivocating_senders s2) ->
    fault_weight_state s1 = fault_weight_state s2. 
Proof.
  intros s1 s2 H_eq. 
  apply set_eq_nodup_sum_weight_eq; try apply set_map_nodup.
  assumption.
Qed.

Lemma messages_fault_weight_eq :
  forall s1 s2,
    set_eq (get_messages s1) (get_messages s2) ->
    fault_weight_state s1 = fault_weight_state s2. 
Proof. 
  intros s1 s2 H_eq.
  apply equivocating_senders_fault_weight_eq.
  now apply messages_equivocating_senders_eq.
Qed.

Lemma add_next_equivocating_senders_eq :
  forall c v j s,
    set_eq (equivocating_senders (add_in_sorted_fn (c,v,j) s))
           (equivocating_senders (next (c,v,j) s)). 
Proof.
  intros.
  assert (H_obv : set_eq (get_messages (add_in_sorted_fn (c,v,j) s))
                         (get_messages (next (c,v,j) s))).
  { split; intros msg H_in. 
    - apply in_state_add_in_sorted_iff in H_in.
      destruct H_in. subst. simpl. tauto.
      right. assumption.
    - apply in_state_add_in_sorted_iff.
      inversion H_in. subst. tauto.
      right; assumption. }
  now apply messages_equivocating_senders_eq.
Qed. 

Lemma senders_fault_weight_eq :
  forall lv1 lv2,
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2. 
Proof.
  induction lv1 as [|hd tl IHlv1]; intros lv2 H_lv1 H_lv2 H_eq.
  - destruct lv2.
    reflexivity.
    inversion H_eq.
    spec H0 v (in_eq v lv2).
    inversion H0.
  - simpl.
    (* hd must be in duplicate-free lv2 *)
    spec IHlv1 (set_remove compare_eq_dec hd lv2).
    spec IHlv1.
    apply NoDup_cons_iff in H_lv1. tauto.
    spec IHlv1.
    now apply set_remove_nodup.
    spec IHlv1.
    replace tl with (set_remove compare_eq_dec hd (hd :: tl)). 
    apply set_eq_remove; try assumption.
    now rewrite set_remove_first.
    (* Now. *) 
    rewrite IHlv1.
    symmetry.
    apply sum_weights_in. assumption.
    destruct H_eq as [H_eq _].
    spec H_eq hd (in_eq hd tl). assumption.
Qed.

(* A new equivocation from a sender inducts it into the set of equivocating_senders *)
(* This says nothing about protocol state validity *)
Lemma add_already_equivocating_sender :
  forall (s : state),
    protocol_state s ->
    forall (msg : message),
      In (sender msg) (equivocating_senders s) ->
        set_eq (equivocating_senders s)
               (equivocating_senders (add_in_sorted_fn msg s)). 
Proof.
  intros s about_s msg H_in.
  split; intros v H_v_in.
  - unfold equivocating_senders.
    apply set_map_exists in H_v_in.
    destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
    apply filter_In in H_v_in.
    rewrite <- H_msg'_sender.
    apply set_map_in.
    apply filter_in. apply in_state_add_in_sorted_iff.
    right. 
    tauto.
    rewrite equivocating_in_state_correct.
    destruct H_v_in.
    rewrite equivocating_in_state_correct in H0.
    destruct H0 as [msg'_partner H0].
    red. exists msg'_partner. split.
    destruct H0.
    rewrite in_state_add_in_sorted_iff.
    right; assumption.
    tauto.
  - destruct (classic (v = sender msg)).
    + subst. assumption.
    + unfold equivocating_senders in H_v_in.
      apply set_map_exists in H_v_in.
      destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
      apply filter_In in H_v_in.
      destruct H_v_in as [H_v_in H_equiv].
      rewrite equivocating_in_state_correct in H_equiv.
      destruct H_equiv as [msg'_partner [H_msg'_partner_in H_equiv]].
      rewrite <- H_msg'_sender.
      apply set_map_in.
      apply filter_in.
      apply in_state_add_in_sorted_iff in H_v_in.
      destruct H_v_in.
      subst.
      contradiction.
      assumption.
      rewrite equivocating_in_state_correct.
      exists msg'_partner.
      split. rewrite in_state_add_in_sorted_iff in H_msg'_partner_in. destruct H_msg'_partner_in.
      subst. destruct H_equiv.
      destruct H1. contradiction.
      assumption. assumption.
Qed. 

Lemma equivocating_sender_add_in_sorted_iff :
  forall (s : state) (msg : message) (v : V),
    In v (equivocating_senders (add_in_sorted_fn msg s)) <->
    (v = sender msg /\ equivocating_in_state_prop msg s) \/
    In v (equivocating_senders s). 
Proof.
  intros s msg v. split; intros.
  -  apply equivocating_senders_correct in H.
     destruct H as [msg' [H_in [H_sender H_equiv]]].
     apply in_state_add_in_sorted_iff in H_in.
     destruct H_in as [H_eq | H_noteq].
     + subst.
       destruct H_equiv as [msg_partner [H_msg_partner H_equiv]].
       left. split. reflexivity.
       exists msg_partner.
       rewrite in_state_add_in_sorted_iff in H_msg_partner.
       destruct H_msg_partner. subst. inversion H_equiv.
       contradiction. tauto. 
     + destruct H_equiv as [msg'_partner [H_msg'_partner H_equiv]].
       apply in_state_add_in_sorted_iff in H_msg'_partner. 
       destruct H_msg'_partner as [H_eq' | H_noteq'].
       * subst. left. destruct H_equiv. split. tauto.
         exists msg'. split.
         assumption. split.
         auto. split. easy. tauto. 
       * right.
         apply equivocating_senders_correct.
         exists msg'_partner. split. assumption.
         destruct H_equiv. split. subst; symmetry; tauto.
         red. exists msg'. split. assumption.
         apply equivocating_messages_prop_swap.
         red; tauto.
  - destruct H as [[H_sender H_equiv] | H_noteq].
    + subst. 
      apply equivocating_senders_correct.
      destruct H_equiv as [msg_partner [H_msg_partner H_equiv]].
      exists msg_partner.
      split. apply in_state_add_in_sorted_iff.
      right; assumption.
      split. destruct H_equiv. symmetry; tauto.
      exists msg. split. rewrite in_state_add_in_sorted_iff; tauto.
      rewrite equivocating_messages_prop_swap. assumption.
    + apply set_map_exists.
      apply set_map_exists in H_noteq.
      destruct H_noteq as [msg' [H_in H_sender]].
      exists msg'. split.
      rewrite filter_In.
      apply filter_In in H_in.
      split.
      apply in_state_add_in_sorted_iff.
      tauto. 2 : assumption.
      destruct H_in.
      apply equivocating_in_state_correct in H0.
      destruct H0 as [msg'_partner about_msg'_partner].
      apply equivocating_in_state_correct.
      exists msg'_partner. split.
      rewrite in_state_add_in_sorted_iff; tauto.
      tauto.
Qed. 

Lemma add_equivocating_sender :
  forall (s : state),
    protocol_state s ->
    forall (msg : message),
      (exists msg',
          in_state msg' s /\
          equivocating_messages_prop msg msg') ->
      set_eq (equivocating_senders (add_in_sorted_fn msg s))
             (set_add compare_eq_dec (sender msg) (equivocating_senders s)).
Proof.
  (* Because we're using set_add, we don't need to care about whether (sender msg) is already in (equivocating_senders s) *) 
  intros s about_s msg [msg' [H_in H_equiv]]. 
  destruct (classic (in_state msg s)) as [H_msg_in | H_msg_out].
  - (* In the case that msg is already in s, *)
    (* Adding it does nothing to the state *)
    assert (s_sorted := protocol_state_sorted s about_s).
    assert (H_ignore := add_in_sorted_ignore msg s s_sorted H_msg_in).
    simpl in *. rewrite H_ignore.
    clear H_ignore s_sorted.
    (* Adding the sender should do nothing to (equivocating_senders s) *) 
    split.
    + intros v0 H_mem.
      (* The following is winding and painful *) 
      unfold equivocating_senders in H_mem.
      rewrite set_map_exists in H_mem.
      destruct H_mem as [msg0 [H0_in H0_sender]].
      rewrite filter_In in H0_in.
      assert (H_senders := equivocating_senders_correct s). 
      red in H_senders.
      destruct H0_in as [H0_in H0_equiv].
      apply set_add_iff. 
      destruct (classic (msg = msg0)).
      * subst.
        left; reflexivity. 
      * right. spec H_senders v0.
        apply H_senders.
        rewrite equivocating_in_state_correct in H0_equiv. 
        destruct H0_equiv as [msg0_partner [H0_equivl H0_equivr]].
        exists msg0_partner. repeat split; try assumption.
        rewrite <- H0_sender.
        destruct H0_equivr as [_ [H_goal _]].
        symmetry; assumption.
        red. exists msg0. split.
        red; exact H0_in.
        apply equivocating_messages_prop_swap.
        assumption.
    + intros v0 H_mem.
      (* The following will also be winding and painful *)
      destruct (classic (v0 = sender msg)).
      * subst.
        clear H_mem.
        apply set_map_in.
        apply filter_in.
        assumption.
        rewrite equivocating_in_state_correct.
        exists msg'. split; assumption.
      * rewrite set_add_iff in H_mem.
        destruct H_mem.
        contradiction. assumption.
  - (* In the case that msg is not already in s, *)
    (* For all we know (sender msg) could already be in (equivocating_senders s) *)  
    destruct (classic (In (sender msg) (equivocating_senders s))).
    + (* If (sender msg) is already in there, then adding it again does nothing *)
      assert (H_ignore : set_eq (set_add compare_eq_dec (sender msg) (equivocating_senders s)) (equivocating_senders s)).
      {  split; intros v H_v_in. 
         apply set_add_iff in H_v_in.
         destruct H_v_in.
         subst; assumption.
         assumption.
         apply set_add_iff. right; assumption. }
      apply set_eq_comm in H_ignore. 
      eapply set_eq_tran. 
      2 : exact H_ignore.
      apply set_eq_comm.
      now apply add_already_equivocating_sender.
    + (* If (sender msg) is not already in there *)
      split; intros.  
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)). 
        ** subst.
           apply set_add_iff.
           tauto.
        ** apply set_add_iff.
           right.
           destruct msg as [[c v] j].
           apply equivocating_sender_add_in_sorted_iff in H_in0. 
           destruct H_in0.
           destruct H1; contradiction.
           assumption.
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)). 
        ** subst.
           apply set_add_iff in H_in0.
           destruct H_in0.
           apply set_map_in.
           apply filter_in.
           apply in_state_add_in_sorted_iff.
           tauto.
           rewrite equivocating_in_state_correct.
           red. exists msg'.
           split. rewrite in_state_add_in_sorted_iff.
           tauto. assumption.
           contradiction. 
        ** apply set_add_iff in H_in0.
           destruct H_in0.
           contradiction.
           apply set_map_exists in H1.
           destruct H1 as [msg0 [H_in0 H_sender0]].
           apply set_map_exists. exists msg0.
           split. 2 : assumption.
           apply filter_in.
           apply filter_In in H_in0.
           destruct H_in0.
           apply in_state_add_in_sorted_iff.
           right; assumption.
           apply filter_In in H_in0.
           destruct H_in0.
           rewrite equivocating_in_state_correct.
           red. rewrite equivocating_in_state_correct in H2.
           red in H2.
           destruct H2 as [msg0_partner [H_in0 H_equiv0]].
           exists msg0_partner.
           split.
           rewrite in_state_add_in_sorted_iff; right; assumption.
           assumption.
Qed.

Lemma pivotal_validator_extension : forall vsfix vss,
  NoDup vsfix ->
  (* and whose added weight does not pass the threshold *)
  (sum_weights vsfix <= proj1_sig t_full)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights (vss ++ vsfix) > proj1_sig t_full)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights (vs ++ vsfix) > proj1_sig t_full)%R /\
  exists v,
    In v vs /\
    (sum_weights ((set_remove compare_eq_dec v vs) ++ vsfix) <= proj1_sig t_full)%R.
Proof.
  destruct t_full as [t about_t]; simpl in *.
  intro.  induction vss; intros.
  - simpl in H2. exfalso. apply (Rge_gt_trans t) in H2; try (apply Rle_ge; assumption).
    apply Rgt_not_eq in H2. apply H2. reflexivity.
  - simpl in H2. destruct (Rtotal_le_gt (sum_weights (vss ++ vsfix)) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply append_nodup_left in H1. assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + simpl in H1. apply NoDup_cons_iff in H1. destruct H1 as [Hnin Hvss]. apply IHvss in H3; try assumption.
      destruct H3 as [vs [Hvs [Hincl Hex]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.


(* From threshold.v *)
Lemma validators_pivotal_ind : forall vss,
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
  intros.
  rewrite <- (app_nil_r vss) in H.   rewrite <- (app_nil_r vss) in H0.
  apply (pivotal_validator_extension [] vss) in H0; try assumption.
  - destruct H0 as [vs [NoDupvs [Inclvs [Gt [v [Inv Lt]]]]]].
    rewrite app_nil_r in Lt. rewrite app_nil_r in Gt.
    exists vs. repeat (split; try assumption).
    exists v. repeat (split; try assumption).
  - constructor.
  - destruct t_full as [t about_t]; simpl in *.
    apply Rge_le; assumption.
Qed.

Lemma sufficient_validators_pivotal :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > proj1_sig t_full)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove compare_eq_dec v vs) <= proj1_sig t_full)%R.
Proof.
  destruct suff_val_full as [vs [Hvs Hweight]].
  apply (validators_pivotal_ind vs Hvs) in Hweight.
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

Lemma exists_pivotal_validator : exists v, potentially_pivotal v.
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
    + constructor.
      apply IHvs.
      apply NoDup_cons_iff in H0.
      tauto.
      simpl in H1.
      apply Rle_trans with (proj1_sig (weight a) + sum_weights vs)%R; try assumption.
      rewrite <- (Rplus_0_l (sum_weights vs)) at 1.
      apply Rplus_le_compat_r.
      apply Rge_le. left. destruct (weight a). simpl.
      auto.
      intro. apply H2. right; assumption.
      constructor.
      intros m H_in. inversion H_in.
      assumption.
      red. unfold fault_weight_state.
      apply Rle_trans with (sum_weights (a :: vs)); try assumption.
      apply sum_weights_incl; try assumption; try apply set_map_nodup.
      rewrite add_is_next.
      remember (next (cempty, v, Empty) Empty) as sigma.
      remember (valid_protocol_state sigma csigma cempty vs) as sigma2.
      { apply incl_tran with (equivocating_senders sigma2).
        - apply set_eq_proj1.
          apply equivocating_senders_unseen.
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
    + apply protocol_state_singleton; assumption.
    + intros msg Hin. simpl in Hin.
      destruct Hin as [Heq | Hcontra]; try inversion Hcontra; subst.
      apply in_state_add_in_sorted_iff. right.
      rewrite add_is_next.
      apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
    + assumption.
    + red; unfold fault_weight_state.
      apply Rle_trans with (sum_weights (a :: vs)); try assumption.
      apply sum_weights_incl; try assumption; try apply set_map_nodup.
      apply incl_tran with (equivocating_senders (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty (a :: vs)))
      ; try  apply incl_refl.
      apply set_eq_proj1.
      apply valid_protocol_state_equivocating_senders; try assumption.
Qed.


