Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.   
From Casper 
Require Import preamble RealsExtras ListExtras ListSetExtras protocol_eq.

(** Building blocks for instancing CBC_protocol with full node version **)
(** Set equality on states **) 

Section States. 

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

Fixpoint state_from_messages (l : list message) : state :=
  match l with
  | [] => Empty
  | (c, v, j) :: tl => Next c v j (state_from_messages tl)
  end. 

Lemma state_message_swap : forall (s : state),
    state_from_messages (get_messages s) = s. 
Proof.
  intros s. induction s.
  - reflexivity.
  - simpl. rewrite IHs2. reflexivity.
Qed.

Lemma message_state_swap : forall (l : list (C * V * state)),
    get_messages (state_from_messages l) = l.
Proof.
  intros l; induction l as [|hd tl IHtl].
  - reflexivity.
  - destruct hd as [c_and_v j].
    destruct c_and_v as [c v].
    simpl. rewrite IHtl.
    reflexivity.
Qed.

Definition state_eq : relation state :=
  fun s1 s2 => incl (get_messages s1) (get_messages s2) /\
            incl (get_messages s2) (get_messages s1). 

Definition state_union (s1 s2 : state) : state :=
  state_from_messages (get_messages s1 ++ get_messages s2). 

Lemma eq_state_refl : reflexive state state_eq. 
Proof. easy. Qed.

Lemma eq_state_sym : symmetric state state_eq. 
Proof.
  intros s1 s2 H_sym. 
  red in H_sym. destruct H_sym as [H1 H2].
  split; intros x H_in.
  spec H2 x H_in; assumption.
  spec H1 x H_in; assumption.
Qed.

Lemma eq_state_trans : transitive state state_eq.
Proof.
  intros s1 s2 s3 [H_12 H_21] [H_23 H_32]. 
  split; intros x H_in.
  apply H_23; apply H_12; assumption.
  apply H_21; apply H_32; assumption.
Qed.

Lemma state0_neutral : forall s, state_eq (state_union s state0) s.
Proof. 
  intros s; split; intros x H_in;
  unfold state_union in *; simpl in *;
  rewrite app_nil_r in *;
  rewrite state_message_swap in *; assumption.
Qed.

Lemma state_union_compat :
  forall s1 s2,
    state_eq s1 s2 ->
    forall t1 t2,
      state_eq t1 t2 ->
      state_eq (state_union s1 t1) (state_union s2 t2). 
Proof.
  intros s1 s2 [Hs_12 Hs_21] t1 t2 [Ht_12 Ht_21];split; intros x H_in;
  unfold state_union in *;
  rewrite message_state_swap in *;
  apply in_or_app;
  apply in_app_or in H_in;
    destruct H_in as [H_in_left | H_in_right].
  left; apply Hs_12; assumption.
  right; apply Ht_12; assumption.
  left; apply Hs_21; assumption.
  right; apply Ht_21; assumption.
Qed.

Add Parametric Relation : state state_eq 
  reflexivity proved by (eq_state_refl)
  symmetry proved by (eq_state_sym)
  transitivity proved by (eq_state_trans)
  as eq_state_rel.

Add Parametric Morphism : state_union
  with signature state_eq ==> state_eq ==> state_eq as state_union_mor.
Proof. exact state_union_compat. Qed. 

Definition reach (s1 s2 : state) := incl (get_messages s1) (get_messages s2). 

Lemma reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3. 
Proof.
  intros s1 s2 s3 H_12 H_23. 
  intros x H_in. 
  spec H_12 x H_in.
  spec H_23 x H_12. assumption.
Qed.

Lemma state_union_comm :
  forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1).
Proof. 
  intros s1 s2;
  split; unfold state_union in *;
  rewrite message_state_swap in *;
  intros x H_in;
  rewrite message_state_swap;
  apply In_app_comm; assumption. 
Qed.

Lemma reach_union :
  forall s1 s2, reach s1 (state_union s1 s2).
Proof.
  intros s1 s2. unfold reach.
  unfold state_union. rewrite message_state_swap.
  intros x H_in; apply in_or_app; left; assumption .
Qed.

Lemma reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3.
Proof.
  intros s1 s2 s3 H_12 H_23. 
  intros x H_in.
  spec H_12 x H_in. 
  destruct H_23 as [H_useful _]. 
  spec H_useful x H_12; assumption.
Qed.

(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> C -> Prop)
           (estimator_total : forall s : state, exists c : C, estimator s c). 

(* Defining protocol states as predicates *)
Definition in_state (msg : message) (sigma : state) : Prop :=
  In msg (get_messages sigma).

Definition in_stateb (msg : message) (s : state) : bool :=
  is_member msg (get_messages s).

Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _ => false
  | _ => match msg1, msg2 with (c1, v1, j1), (c2, v2, j2) =>
      match compare_eq_dec v1 v2 with
      | left _ => negb (in_stateb msg1 j2) && negb (in_stateb msg2 j1)
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
  assert (Hin : in_stateb (c0, v, sigma') sigma1 = true).
  { apply is_member_correct. assumption. }
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

Definition is_equivocating_messages (msg : message) (lm : list message) : bool :=
  existsb (equivocating_messages msg) lm. 

Definition is_equivocating_state (msg : message) (sigma : state) : bool :=
  existsb (equivocating_messages msg) (get_messages sigma).

Lemma equivocating_state_incl : forall sigma sigma',
  reach sigma sigma' ->
  forall msg,
    is_equivocating_state msg sigma = true ->
    is_equivocating_state msg sigma' = true.
Proof.
  unfold is_equivocating_state. 
  intros. rewrite existsb_exists in *. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma equivocating_messages_incl : forall (lm lm' : list message),
    incl lm lm' ->
    forall msg,
      is_equivocating_messages msg lm = true ->
      is_equivocating_messages msg lm' = true. 
Proof.
  unfold is_equivocating_messages.
  intros. rewrite existsb_exists in *. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma non_equivocating_extend : forall sigma sigma' c v,
  reach sigma sigma' ->
  is_equivocating_state (c, v, sigma') sigma = false.
Proof.
  unfold is_equivocating_state.
  induction sigma; intros.
  - reflexivity.
  - simpl. rewrite IHsigma2.
    + rewrite equivocating_messages_comm.
      rewrite non_equivocating_messages_extend; try reflexivity.
      apply H. left. reflexivity.
    + intros x Hin. apply H. right. assumption.
Qed.

Lemma is_equivocating_state_notIn : forall msg sigma,
  ~In (sender msg) (set_map compare_eq_dec sender (get_messages sigma)) ->
  is_equivocating_state msg sigma = false.
Proof.
  intros [(c, v) j] sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  unfold is_equivocating_state. apply existsb_forall.
  intros [(cx, vx) jx] Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists (cx, vx, jx). split; try assumption. reflexivity.
Qed.

Definition equivocating_senders (sigma : state) : list V :=
  set_map compare_eq_dec sender
    (filter (fun msg => is_equivocating_state msg sigma)
            (get_messages sigma)).

Definition equivocating_senders_messages (lm : list message) : list V :=
  set_map compare_eq_dec sender (filter (fun msg => is_equivocating_messages msg lm) lm).

Lemma equivocating_senders_nodup : forall sigma,
  NoDup (equivocating_senders sigma).
Proof.
  intros. apply set_map_nodup.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  reach sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => is_equivocating_state msg sigma) (get_messages sigma')).
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_state_incl. assumption.
Qed.

Lemma equivocating_senders_messages_incl : forall lm lm',
    incl lm lm' ->
    incl (equivocating_senders_messages lm) (equivocating_senders_messages lm'). 
Proof. 
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => is_equivocating_messages msg lm) lm').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_messages_incl. assumption.
Qed.

Lemma equivocating_senders_extend : forall sigma c v,
  equivocating_senders (add (c, v, sigma) to sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  assert (Heq :
    (filter (fun msg : message => is_equivocating_state msg (add (c, v, sigma)to sigma))
      (get_messages (add (c, v, sigma)to sigma))) = 
    (filter (fun msg : message => is_equivocating_state msg sigma)
      (get_messages sigma))); try (rewrite Heq; reflexivity).
    simpl.
  assert
    (Hequiv : is_equivocating_state (c, v, sigma) (add (c, v, sigma)to sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros. rewrite equivocating_messages_comm.
    destruct H as [Heq | Hin].
    - subst. unfold equivocating_messages.
      rewrite eq_dec_if_true; reflexivity.
    - apply non_equivocating_messages_extend. assumption.
  }
  apply filter_eq_fn. intros. unfold is_equivocating_state. split; intros
  ; apply existsb_exists in H0; apply existsb_exists
  ; destruct H0 as [msg [Hin Hmsg]]; exists msg; split; try assumption.
  - simpl in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    exfalso. subst.
    apply (non_equivocating_messages_extend _ _ c v) in H.
    rewrite Hmsg in H. inversion H.
  - right. assumption.
Qed.

Definition fault_weight_messages (lm : list message) : R :=
  sum_weights (equivocating_senders_messages lm). 

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

Lemma sum_weights_messages_incl : forall lm1 lm2,
    incl lm1 lm2 -> 
    (fault_weight_messages lm1 <= fault_weight_messages lm2)%R.
Proof.
  intros lm1 lm2.
  unfold fault_weight_messages.
  assert (H_nodup1 : NoDup (equivocating_senders_messages lm1)) by apply set_map_nodup. 
  assert (H_nodup2 : NoDup (equivocating_senders_messages lm2)) by apply set_map_nodup. intro H_incl. 
  assert (H_incl' : incl (equivocating_senders_messages lm1) (equivocating_senders_messages lm2)) by now apply equivocating_senders_messages_incl.
  now apply sum_weights_incl. 
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  reach sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

Lemma equivocation_weight_compat : forall (s1 s2 : state), (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R. 
Proof. 
  intros s1 s2.
  assert (H_useful := fault_weight_state_incl s1 (state_union s2 s1)).
  spec H_useful.
  red. unfold state_union.
  rewrite message_state_swap.
  now apply incl_appr.
  assumption.
Qed.

(* Continuing the change from state to message *) 
Definition valid_estimate_condition (lm : list message) : Prop := 
  Forall (fun m => estimator (justification m) (estimate m)) lm.

Definition fault_tolerance_condition (lm : list message) : Prop :=
  (fault_weight_messages lm <= proj1_sig t_full)%R.

Lemma fault_tolerance_condition_empty : 
  fault_tolerance_condition [].
Proof.
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold is_equivocating_state. simpl.
  unfold equivocating_messages. 
  simpl. 
  apply Rge_le. destruct t_full.
  simpl; auto.
Qed.

Lemma fault_tolerance_condition_subset : forall lm lm',
  incl lm lm' ->
  fault_tolerance_condition lm' ->
  fault_tolerance_condition lm.
Proof.
  unfold fault_tolerance_condition; intros.
  apply Rle_trans with (fault_weight_messages lm'); try assumption.
  now apply sum_weights_messages_incl. 
Qed.

(* Continuing the abandonment of state for message *) 
Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall sigma sigma',
      protocol_state sigma -> 
      reach sigma sigma' ->
      valid_estimate_condition (get_messages sigma') ->
      fault_tolerance_condition (get_messages sigma') ->
      protocol_state sigma'.

Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition (get_messages sigma).
Proof.
  intros.
  inversion H.
  - unfold fault_tolerance_condition.
    simpl. apply Rge_le. destruct t_full; simpl; auto. 
  - assumption.
Qed.

Lemma incl_preserves_forall {X} :
  forall (l1 l2 : list X) (P : X -> Prop),
    Forall P l1 ->
    incl l2 l1 ->
    Forall P l2. 
Proof.
  intros.
  rewrite Forall_forall in *. intros.
  spec H0 x H1.
  spec H x H0. assumption.
Qed.

Lemma protocol_state_valid_estimates : forall sigma,
  protocol_state sigma ->
  valid_estimate_condition (get_messages sigma).
Proof.
  intros.
  inversion H.
  - subst. simpl.
    apply Forall_nil.
  - unfold reach in H0.
    subst.  
    eapply incl_preserves_forall.
    apply H2. apply incl_refl.
Qed. 

Lemma app_preserves_forall {X} :
  forall (l1 l2 : list X) (P : X -> Prop),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2). 
Proof.
  intros.
  rewrite Forall_forall in *.
  intros. apply in_app_or in H1.
  destruct H1; eauto.
Qed.

Lemma about_prot_state :
  forall (s1 s2 : state),
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
    protocol_state (state_union s1 s2). 
Proof.
  intros s1 s2 Hps1 Hps2 H_weight.
  apply (protocol_state_next s1 (state_union s1 s2)); try assumption. 
  apply reach_union.
  apply protocol_state_valid_estimates in Hps1.
  apply protocol_state_valid_estimates in Hps2.
  unfold state_union.
  rewrite message_state_swap.
  now apply app_preserves_forall.
Qed.

Instance FullNode_seteq : CBC_protocol_eq :=
  { consensus_values := C;  
    about_consensus_values := about_C;
    validators := V;
    about_validators := about_V;
    weight := weight;
    t := t_full;
    suff_val := suff_val_full;
    state := state;
    state0 := Empty;
    (* >> *) state_eq := state_eq;
    state_union := state_union;
    state_union_comm := state_union_comm;
    reach := reach; 
    reach_trans := reach_trans;
    reach_union := reach_union;
    (* >> *) reach_morphism := reach_morphism;
    E := estimator;
    estimator_total := estimator_total; 
    prot_state := protocol_state;
    about_state0 := protocol_state_empty;
    equivocation_weight := fault_weight_state; 
    equivocation_weight_compat := equivocation_weight_compat; 
    about_prot_state := about_prot_state;
  }.

(** Nontriviality **)

Definition non_trivial_state (p : state -> Prop) :=
  (exists sigma1, protocol_state sigma1 /\ decided sigma1 p)
  /\
  (exists sigma2, protocol_state sigma2 /\ decided sigma2 (predicate_not p)).

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= proj1_sig t)%R /\
      (sum_weights vs > proj1_sig t - (proj1_sig (weight v)))%R.

Definition at_least_two_validators : Prop :=
  forall v1 : V, exists v2 : V, v1 <> v2.

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
  induction vss; intros.
  simpl in H0.
  - exfalso. apply (Rge_gt_trans (proj1_sig t)) in H0; try apply threshold_nonnegative.
    apply Rgt_not_eq in H0. apply H0. reflexivity. destruct t. easy.  
  - simpl in H0. destruct (Rtotal_le_gt (sum_weights vss) (proj1_sig t)).
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
    (sum_weights vs > (proj1_sig t_full))%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove compare_eq_dec v vs) <= (proj1_sig t_full))%R.
Proof.
  destruct suff_val as [vs [Hvs Hweight]].
  apply (sufficient_validators_pivotal_ind vs Hvs) in  Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  exists vs'. repeat (split; try assumption).
Qed.

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

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  at_least_two_validators ->
  exists p, non_trivial_state p.
Proof.
  intro H2v.
  destruct exists_pivotal_message as [v Hpivotal].
  destruct (estimator_total Empty) as [c Hc].
  destruct Hpivotal as [vs [Hnodup [Hnin [Hlt Hgt]]]].
  destruct vs as [ | v' vs].
  - exists (in_state (c,v,Empty)).
    split.
    + exists (next (c,v,Empty) Empty); split; try apply protocol_state_singleton; try assumption.
      replace (next (c, v, Empty) Empty) with (state_union Empty (state_from_messages [(c,v,Empty)])).
      2 : compute; reflexivity.
      apply (protocol_state_next Empty _).
      constructor. 
      intros x H_in. inversion H_in.
      simpl. admit. admit. admit. 
    + destruct (H2v v) as [v' Hv'].
      remember (next (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0).
      { subst. admit. } 
      destruct (estimator_total sigma0) as [c0 Hc0].
      exists (next (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      admit.
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      intro.
      apply protocol_state_fault_tolerance in Hps' as Hft'.
      unfold fault_tolerance_condition in Hft'.
      assert (Hnft' : (fault_weight_state sigma' > t)%R).
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
          apply (Rplus_gt_compat_r (weight v)) in Hgt. rewrite Rplus_assoc in Hgt.
          rewrite Rplus_0_r. rewrite Rplus_0_l in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt.
          apply Rgt_lt. assumption.
        - apply fault_weight_state_incl. unfold syntactic_state_inclusion. simpl.
          intros x Hin. destruct Hin as [Hin | [Hin | Hcontra]]; try inversion Hcontra; subst
          ; try assumption.
          apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
      }
      unfold Rgt in Hnft'. apply (Rlt_irrefl t).
      apply Rlt_le_trans with (fault_weight_state sigma'); assumption.
  - remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
    assert (Hps0 : protocol_state sigma0).
    { subst. apply protocol_state_singleton. assumption. }
    destruct (estimator_total sigma0) as [c0 Hc0].
    exists (in_state (c0,v,sigma0)).
    split.
    + exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + remember (add_in_sorted_fn (c, v, Empty) Empty) as sigma.
      simpl in Heqsigma. rewrite add_is_next in Heqsigma.
      destruct (estimator_total sigma) as [csigma Hcsigma].
      remember (valid_protocol_state sigma csigma c (v' :: vs)) as sigma2.
      assert (Hequiv2 : set_eq (equivocating_senders sigma2) (v' :: vs)). 
      { rewrite Heqsigma2. rewrite Heqsigma in *.
        apply valid_protocol_state_equivocating_senders; assumption.
      }
      exists sigma2. split.
      * subst. apply valid_protocol_state_ps; assumption.
      * unfold decided_state. intros sigma' Hfutures.
        unfold predicate_not. intro Hin.
        destruct Hfutures as [Hps2 [Hps' Hincl]].
        apply protocol_state_fault_tolerance in Hps'.
        { apply (fault_tolerance_condition_subset (add (c0, v, sigma0) to sigma2)) in Hps'.
        - unfold fault_tolerance_condition in Hps'.
          apply Rlt_irrefl with t.
          apply Rlt_le_trans with (fault_weight_state (add (c0, v, sigma0)to sigma2)); try assumption.
          unfold fault_weight_state.
          unfold Rminus in Hgt. apply (Rplus_gt_compat_r (weight v)) in Hgt.
          rewrite Rplus_assoc in Hgt. rewrite Rplus_opp_l, Rplus_0_r in Hgt.
          apply Rgt_lt. apply Rge_gt_trans with (sum_weights (v' :: vs) + weight v)%R; try assumption.
          rewrite Rplus_comm.
          assert (Hsum : (weight v + sum_weights (v' :: vs))%R = sum_weights (v :: v' :: vs))
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
          * apply Hincl. assumption.
   }
Qed.

        End Non_triviality_Properties_Protocol_States.


End States.



