Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts Classical Sorting.
Import ListNotations.    
From Casper  
Require Import preamble ListExtras ListSetExtras sorted_lists protocol.

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

(* Additional types for defining light node states *)
(* State hashes *) 
Variable hash : Type.
Variable (about_H : `{StrictlyComparable hash}). 

(* Lists of state hashes *) 
Definition justification_type : Type := list hash. 

Lemma justification_type_inhabited : exists (j : justification_type), True. 
Proof. exists []. auto. Qed. 

Definition justification_compare : (justification_type -> justification_type -> comparison) := list_compare compare.

Instance about_justification_type : StrictlyComparable justification_type :=
  { inhabited := justification_type_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }. 

Definition justification_add : hash -> justification_type -> justification_type := add_in_sorted_list_fn compare.

Definition justification_add_iff := @add_in_sorted_list_iff hash compare compare_strictorder.

Definition justification_add_head := @add_in_sorted_list_head hash compare compare_strictorder.

Definition justification_add_tail := @add_in_sorted_list_tail hash compare compare_strictorder.

Definition justification_add_sorted := @add_in_sorted_list_sorted hash compare compare_strictorder.

Definition justification_add_all : list hash -> justification_type := fold_right justification_add nil.

Lemma justification_sorted : forall j : list hash,
  LocallySorted (compare_lt compare) (justification_add_all j).
Proof.
  induction j.
  - simpl. constructor.
  - apply justification_add_sorted. assumption.
Qed.

Lemma justification_set_eq : forall hs,
  set_eq hs (justification_add_all hs).
Proof.
  induction hs; simpl.
  - apply set_eq_refl.
  - split; intros x Hin
    ;  rewrite justification_add_iff || apply justification_add_iff in Hin
    ;  destruct Hin as [Heq | Hin]
    ; try (subst; left; reflexivity)
    ; right; apply IHhs; assumption.
Qed.

Lemma justification_add_all_injective : forall hs1 hs2,
  justification_add_all hs1 = justification_add_all hs2 ->
  set_eq hs1 hs2.
Proof.
  intros.
  apply (@set_equality_predicate hash (compare_lt compare) compare_lt_strict_order) in H;
    try apply justification_sorted.
  apply set_eq_tran with (justification_add_all hs1); try apply justification_set_eq.
  apply set_eq_tran with (justification_add_all hs2); try assumption.
  apply set_eq_comm. apply justification_set_eq.
Qed.

Definition justification_in : hash -> list hash -> bool := inb compare_eq_dec.

(* Messages *) 
Definition message : Type := C * V * justification_type.

Definition message_type := TripleStrictlyComparable C V justification_type.

(* StrictlyComparable and CompareStrictOrder for message type comes for free *) 

Definition estimate (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : justification_type :=
  match msg with (_, _, j) => j end.

Parameters (hash_message : message -> hash)
           (hash_message_injective : Injective hash_message).
 
(* Light node states are sets of message *)
(* Additionally, we don't care about sorting *) 
Definition state := set message.

Lemma state_inhabited : exists (s : state), True. 
Proof. exists []. auto. Qed. 

Definition state_compare : (state -> state -> comparison) := list_compare compare.

Instance about_state : StrictlyComparable state :=
  { inhabited := state_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }. 

Definition state0 : state := [].

Definition state_add : message -> state -> state := set_add compare_eq_dec.

Definition state_remove : message -> state -> state := set_remove compare_eq_dec.

Definition state_in : message -> state -> bool := set_mem compare_eq_dec.

Definition state_union : state -> state -> state := set_union compare_eq_dec.

Definition state_eq (s1 s2 : state) := incl s1 s2 /\ incl s2 s1.

Lemma state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1).
Proof.
  intros; unfold state_eq; split;
  intros x H_in;
  now apply set_union_comm.
Qed.

Definition hash_state (sigma : state) : justification_type :=
  justification_add_all (map hash_message sigma).

Lemma hash_state_sorted : forall sigma,
  LocallySorted (compare_lt compare) (hash_state sigma).
Proof.
  intros.
  apply justification_sorted.
Qed.

Lemma hash_state_injective : forall sigma1 sigma2,
  hash_state sigma1 = hash_state sigma2
  <->
  set_eq sigma1 sigma2.
Proof.
  split; intros.
  - apply justification_add_all_injective in H.
    destruct H as [H12 H21].
    split; intros x Hin
    ; apply (in_map hash_message) in Hin
    ; apply H12 in Hin || apply H21 in Hin
    ; apply in_map_iff in Hin
    ; destruct Hin as [x' [Heq Hin]]
    ; apply hash_message_injective in Heq
    ; subst; assumption.
  - apply (@set_equality_predicate hash (compare_lt compare) compare_lt_strict_order); try apply hash_state_sorted.
    unfold hash_state.
    apply set_eq_tran with (map hash_message sigma2); try apply (justification_set_eq (map hash_message sigma2)).
    apply set_eq_comm.
    apply set_eq_tran with (map hash_message sigma1); try apply (justification_set_eq (map hash_message sigma1)).
    apply map_set_eq. apply set_eq_comm. assumption.
Qed.

Lemma hash_state_in : forall sigma msg,
  In (hash_message msg) (hash_state sigma) <->
  In msg sigma.
Proof.
  unfold hash_state.
  intros.
  assert (H_s : set_eq (map hash_message sigma) (justification_add_all (map hash_message sigma)))
      by apply justification_set_eq.
  split; intro Hin.
  - apply H_s in Hin. 
    apply in_map_iff in Hin.
    destruct Hin as [msg' [Heq Hin]].
    apply hash_message_injective in Heq. subst. assumption.
  - apply H_s. apply in_map. assumption.
Qed.

Lemma hash_state_incl : forall sigma1 sigma2,
  incl sigma1 sigma2 <-> incl (hash_state sigma1) (hash_state sigma2).
Proof.
  intros.
  assert (H_s1 : set_eq (map hash_message sigma1) (justification_add_all (map hash_message sigma1)))
      by apply justification_set_eq.
  assert (H_s2 : set_eq (map hash_message sigma2) (justification_add_all (map hash_message sigma2)))
      by apply justification_set_eq.
  unfold hash_state.
  split; intro Hincl.
  - intros h Hin.
    apply H_s2. apply H_s1 in Hin.
    apply in_map_iff. apply in_map_iff in Hin.
    destruct Hin as [msg [H_mh Hin_m]].
    apply Hincl in Hin_m.
    exists msg. split; assumption.
  - intros msg Hin. apply hash_state_in in Hin.
    apply Hincl in Hin.
    apply hash_state_in in Hin. assumption.
Qed.


(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> C -> Prop)
           (estimator_total : forall s : state, exists c : C, estimator s c). 

Definition get_estimate (s : state) :=
  proj1_sig (choice C (estimator s) (estimator_total s)).

Definition get_estimate_correct (s : state) :=
  proj2_sig (choice C (estimator s) (estimator_total s)). 

Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _  => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match compare_eq_dec v1 v2 with
      | left _  => negb (inb compare_eq_dec (hash_message msg1) j2) && negb (inb compare_eq_dec (hash_message msg2) j1)
      | right _ => false
      end
    end
  end.

Definition equivocating_messages_prop (msg1 msg2 : message) : Prop :=
  msg1 <> msg2 /\ sender msg1 = sender msg2 /\ ~ In (hash_message msg1) (justification msg2) /\ ~ In (hash_message msg2) (justification msg1).

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
      apply (in_function compare_eq_dec) in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd. 
      rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      subst. 
      simpl in H. inversion H.
      inversion H. assumption.
    + (* Proving msg2 is not in msg1's justification *)
      intro H_absurd. apply (in_function compare_eq_dec) in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd. rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      rewrite andb_false_r in H. inversion H.
      inversion H. assumption. 
  - destruct H as [H_neq [H_sender [H_in1 H_in2]]].
    assert (H_in1_bool : inb compare_eq_dec (hash_message (c1,v1,j1)) (justification (c2,v2,j2)) = false).
    { rewrite mirror_reflect_curry.  exact H_in1.
      intros. symmetry. rewrite <- (in_function compare_eq_dec _ _ ). tauto. }
    assert (H_in2_bool : inb compare_eq_dec (hash_message (c2,v2,j2)) (justification (c1,v1,j1)) = false).
    { rewrite mirror_reflect_curry.  exact H_in2.
      intros. symmetry. rewrite <- (in_function compare_eq_dec _ _ ). tauto. }
    simpl in H_sender.
    unfold equivocating_messages.
    destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
    contradiction.
    rewrite eq_dec_if_false.
    destruct (compare_eq_dec v1 v2).
    simpl in *.
    rewrite H_in1_bool. rewrite H_in2_bool.
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
  existsb (equivocating_messages msg) sigma.

Definition equivocating_in_state_prop (msg : message) (s : state) : Prop :=
  exists msg', In msg' s /\ equivocating_messages_prop msg msg'. 

Lemma equivocating_in_state_correct :
  forall msg s, equivocating_in_state msg s = true <-> equivocating_in_state_prop msg s.
Proof.
  intros msg s.
  split; intro H.
  - unfold equivocating_in_state in H.
    rewrite existsb_exists in H.
    destruct H as [msg' [H_in H_equiv]].
    exists msg'. split. assumption.
    rewrite <- equivocating_messages_correct. assumption.
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

Lemma equivocating_in_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  forall msg,
    equivocating_in_state_prop msg sigma ->
    equivocating_in_state_prop msg sigma'.
Proof.
  intros.
  destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma equivocating_in_state_not_seen :
  forall msg sigma,
  ~ In (sender msg) (set_map compare_eq_dec sender sigma) ->
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
  set_map compare_eq_dec sender (filter (fun msg => equivocating_in_state msg sigma) sigma).

Definition equivocating_senders_prop (s : state) (lv : set V) :=
  forall v, In v lv <-> exists msg, In msg s /\ sender msg = v /\ equivocating_in_state_prop msg s. 

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

Lemma filter_set_add {X} `{StrictlyComparable X} :
  forall (l : list X) (f : X -> bool) (x : X),
    f x = false ->
    filter f l = filter f (set_add compare_eq_dec x l). 
Proof.
  induction l as [|hd tl IHl]; intros f x H_false. 
  - simpl. rewrite H_false. reflexivity.
  - simpl. spec IHl f x H_false. 
    destruct (compare_eq_dec x hd). 
    + subst. rewrite H_false.
      simpl. rewrite H_false. reflexivity.
    + case_eq (f hd); intro H_eq;
      simpl; rewrite H_eq; rewrite <- IHl; reflexivity.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  incl sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl.
  apply incl_tran with (filter (fun msg : message => equivocating_in_state msg sigma) sigma').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro.
    do 2 rewrite equivocating_in_state_correct.
    apply equivocating_in_state_incl. assumption.
Qed.

Definition reach (s1 s2 : state) := incl s1 s2.

Lemma reach_refl : forall s, reach s s. 
Proof. apply incl_refl. Qed.

Lemma reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3. 
Proof. apply incl_tran. Qed.

Lemma reach_union : forall s1 s2, reach s1 (state_union s1 s2). 
Proof. intros s1 s2 x H_in; apply set_union_iff; left; assumption. Qed.

Lemma reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3.
Proof. intros s1 s2 s3 H_reach H_eq x H_in. spec H_reach x H_in.
       destruct H_eq as [H_eq _]. spec H_eq x H_reach; assumption.
Qed. 

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
  incl sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply set_map_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

(* Estimator approval condition *) 
Definition valid_estimate (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(* The not overweight condition *)
Definition not_heavy (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

Lemma not_heavy_subset : forall sigma sigma',
  incl sigma sigma' ->
  not_heavy sigma' ->
  not_heavy sigma.
Proof.
  unfold not_heavy.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Lemma not_heavy_set_eq : forall sigma sigma',
  set_eq sigma sigma' ->
  not_heavy sigma ->
  not_heavy sigma'.
Proof.
  intros. destruct H.
  apply (not_heavy_subset _ _ H1 H0).
Qed. 

Inductive protocol_state : state -> Prop :=
| protocol_state_nil : protocol_state state0
| protocol_state_cons : forall (j : state),
    protocol_state j ->
    forall (c : C),
      valid_estimate c j ->
      forall (v : V) (s : state),
        In (c, v, hash_state j) s ->
        protocol_state (set_remove compare_eq_dec (c, v, hash_state j) s) ->
        NoDup s ->
        not_heavy s ->
        protocol_state s.


Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup sigma.
Proof.
  intros. inversion H; subst.
  - constructor.
  - assumption.
Qed.


Lemma not_extx_in_x : forall c v s s',
    protocol_state s ->
    protocol_state s' ->
    incl s' s ->
    ~ In (hash_message (c, v, hash_state s)) (hash_state s').
Proof.
  intros c v s s' PS PS'. induction PS'; intros Hincl Hin; apply hash_state_in in Hin.
  - unfold state0 in Hin. inversion Hin.
  - apply (set_remove_in_iff compare_eq_dec (c, v, hash_state s) (c0, v0, hash_state j) s0 H1 H0) in Hin.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst; clear Heq. apply hash_state_injective in H6. apply IHPS'1; try apply H6.
      apply hash_state_in. apply Hincl in H0. apply H6.
      assert (hash_state s = hash_state j) by (apply hash_state_injective; assumption).
      rewrite H3. assumption.
    + apply IHPS'2; try (apply hash_state_in; assumption).
      apply incl_tran with s0; try assumption.
      intros h Hin_h. apply set_remove_1 in Hin_h. assumption.
Qed.

Lemma set_eq_protocol_state :
  forall sigma,
  protocol_state sigma ->
  forall sigma',
    set_eq sigma sigma' ->
    NoDup sigma' ->
    protocol_state sigma'.
Proof.
  intros sigma H'.
  induction H'; intros.
  - destruct H. unfold state0 in *.
    apply incl_empty in H1; subst. constructor.
  - apply (set_eq_remove compare_eq_dec (c, v, hash_state j)) in H3 as Hset_eq; try assumption.
    apply IHH'2 in Hset_eq.
    apply (protocol_state_cons j H'1 c H v sigma'); try assumption.
    + destruct H3. now apply (H3 (c, v, hash_state j)). 
    + apply (not_heavy_set_eq _ _ H3 H2).
    + now apply set_remove_nodup. 
Qed.

Lemma message_justification_protocol_state :
  forall (s : state),
    protocol_state s ->
    forall (msg : message),
      In msg s ->
      forall (s' : state),
        hash_state s' = justification msg ->
        protocol_state s'. 
Proof.
  intros s H_prot msg H_in s' H_eq.
  induction H_prot.
  inversion H_in.
  assert (H_useful := set_remove_not_in compare_eq_dec (c,v,hash_state j) s).
  spec H_useful.
  destruct (classic (msg = (c, v, hash_state j))).
  - subst.
Abort. 

Lemma about_prot_state :
  forall (s1 s2 : state),
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
    protocol_state (state_union s1 s2). 
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - simpl. assumption.
  - clear IHHps2_1.
    assert (protocol_state (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))).
    { apply IHHps2_2.
      apply not_heavy_subset with (state_union sig1 s); try assumption.
      intro msg; intro Hin.
      apply set_union_intro.
      unfold state_union in Hin; apply set_union_elim in Hin.
      destruct Hin; try (left; assumption).
      right. apply (set_remove_1 _ _ _ _ H4).
    }
    clear IHHps2_2.
    apply protocol_state_nodup in Hps1 as Hnodups1.
    assert (HnodupUs1s' := H1).
    apply (set_union_nodup compare_eq_dec Hnodups1) in HnodupUs1s'.
    destruct (in_dec compare_eq_dec (c, v, hash_state j) sig1).
    + apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))
      ; try assumption.
      apply set_eq_remove_union_in; assumption.
    + eapply (protocol_state_cons j Hps2_1 c H v); try assumption.
      * apply set_union_iff. right. assumption.
      * apply (set_remove_nodup compare_eq_dec (c, v, hash_state j)) in HnodupUs1s' as Hnoduprem.
        apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))
        ; try assumption.
        apply set_eq_remove_union_not_in; assumption.
Qed.

Lemma equivocation_weight_compat :
  forall s1 s2 : state,
  (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R. 
Proof. 
  intros.
  apply fault_weight_state_incl.
  intros msg H_in.
  apply set_union_iff. tauto.
Qed.

Lemma non_equivocating_messages_extend : forall msg sigma1 c v,
  In msg sigma1 ->
  equivocating_messages msg (c, v, hash_state sigma1) = false.
Proof. 
  intros [(c0, v0) sigma'_hash]; intros.
  unfold equivocating_messages.
  destruct (compare_eq_dec (c0, v0, sigma'_hash) (c, v, hash_state sigma1)).  
  - (* In the case that these two messages are equal, they cannot be equivocating *)
    now rewrite eq_dec_if_true. 
  - (* In the case that these messages are not equal, *)
    rewrite eq_dec_if_false.
    (* When their senders are equal *)
    destruct (compare_eq_dec v0 v).  
    + subst. apply (in_function compare_eq_dec) in H.
      assert (H' : inb compare_eq_dec (hash_message (c0,v,sigma'_hash)) (hash_state sigma1) = true). 
      { apply in_function.
        unfold hash_state.
        assert (H_eq := justification_set_eq (map hash_message sigma1)).
        destruct H_eq.
        apply H0. rewrite in_map_iff.
        exists (c0,v,sigma'_hash).
        split. reflexivity.
        now apply (in_function compare_eq_dec). }
      rewrite H'. tauto.
    + reflexivity.
    + assumption. 
Qed.

Instance LightNode_seteq : CBC_protocol_eq :=
  { consensus_values := C;  
    about_consensus_values := about_C;
    validators := V;
    about_validators := about_V;
    weight := weight;
    t := t_full;
    suff_val := suff_val_full;
    state := state;
    state0 := state0;
    state_eq := set_eq;
    about_state := about_state;
    state_union := state_union;
    state_union_comm := state_union_comm;
    reach := reach;
    reach_refl := reach_refl;
    reach_trans := reach_trans;
    reach_union := reach_union;
    reach_morphism := reach_morphism;
    E := estimator;
    estimator_total := estimator_total; 
    prot_state := protocol_state;
    about_state0 := protocol_state_nil;
    equivocation_weight := fault_weight_state; 
    equivocation_weight_compat := equivocation_weight_compat; 
    about_prot_state := about_prot_state;
  }.

Definition pstate_light : Type := {s : state | protocol_state s}. 
Definition pstate_light_proj1 (p : pstate_light) : state :=
  proj1_sig p. 
Coercion pstate_light_proj1 : pstate_light >-> state.

Definition pstate_light_rel : pstate_light -> pstate_light -> Prop :=
  fun p1 p2 => incl (pstate_light_proj1 p1) (pstate_light_proj1 p2).

Definition non_trivial_pstate_light (P : pstate_light -> Prop) :=
  (exists (s1 : pstate_light), forall (s : pstate_light), pstate_light_rel s1 s -> P s)
  /\
  (exists (s2 : pstate_light), forall (s : pstate_light), pstate_light_rel s2 s -> (P s -> False)).

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= proj1_sig t_full)%R /\
      (sum_weights vs > proj1_sig t_full - weight v)%R.

Lemma Rtotal_le_gt : forall x y,
  (x <= y)%R \/ (x > y)%R.
Proof.
  intros.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
  - left. unfold Rle. left. assumption.
  - left. unfold Rle. right. assumption.
  - right. assumption.
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
  - simpl in H1. exfalso. apply (Rge_gt_trans t) in H2; try (apply Rle_ge; assumption).
    apply Rgt_not_eq in H2. apply H2. reflexivity.
  - simpl in H2.
    destruct (Rtotal_le_gt (sum_weights (vss ++ vsfix)) t).
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
  rewrite <- (app_nil_r vss) in H0.   rewrite <- (app_nil_r vss) in H.
  apply (pivotal_validator_extension [] vss) in H; try assumption.
  - destruct H as [vs [NoDupvs [Inclvs [Gt [v [Inv Lt]]]]]].
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

Lemma not_heavy_singleton : forall msg,
  not_heavy [msg].
Proof.
  intros [(c, v) j].
  unfold not_heavy.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. destruct t_full. easy.
Qed.

Lemma protocol_state_singleton : forall c v j,
  protocol_state j ->
  valid_estimate c j ->
  protocol_state [(c, v, hash_state j)].
Proof.
  intros.
  apply protocol_state_cons with j c v; try assumption.
  - left. reflexivity.
  - simpl. rewrite eq_dec_if_true; constructor.
  - constructor; try constructor. apply in_nil.
  - apply not_heavy_singleton.
Qed.

(*
      c1 = get_estimate [] 
      c' = get_estimate [(get_estimate [], v, [])]
      c2 = get_estimate [(c', v, hash_state [(get_estimate [], v, [])])]
      j1 = []
      j2 = [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])]
      msg1 = (get_estimate [], v, hash_state [])
      msg2 = (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])])
*)

(* This is a critical property of the light node protocol *)
(* Any duplicate-free subset of a protocol state (as list message) is itself a protocol state *) 
Lemma protocol_state_incl :
  forall (s : state),
    protocol_state s ->
    forall (s' : state),
      NoDup s' ->
      incl s' s ->
      protocol_state s'. 
Proof.
  intros s about_s.  
  induction about_s; intros s' H_nodup H_incl. 
  - destruct s'.
    + apply protocol_state_nil.
    + spec H_incl m (in_eq m s'). inversion H_incl.
  - destruct (classic (In (c,v,hash_state j) s')).
    + spec IHabout_s2 (set_remove compare_eq_dec (c,v,hash_state j) s').
      apply protocol_state_cons with j c v; try assumption.
      2 : now apply not_heavy_subset with s.
      apply IHabout_s2.
      now apply set_remove_nodup.
      intros msg H_in.
      destruct (classic (msg = (c,v,hash_state j))). 
      * subst.
        assert (H_contra := set_remove_elim compare_eq_dec (c,v,hash_state j) s').
        spec H_contra H_nodup.
        contradiction.
      * spec H_incl msg.
        spec H_incl.
        assert (H_useful := set_remove_iff compare_eq_dec msg (c,v,hash_state j)).
        spec H_useful s' H_nodup.
        rewrite H_useful in H_in.
        tauto.
        apply set_remove_iff; try tauto.
    + spec IHabout_s2 s'.
      apply IHabout_s2.
      assumption.
      intros msg H_in.
      assert (msg <> (c,v,hash_state j)).
      { intros H_absurd. subst.
        spec H_incl (c,v,hash_state j) H_in.
        contradiction. }
      apply set_remove_iff; try assumption.
      split. 2 : assumption.
      now apply (H_incl msg H_in).
Qed.

(* We can always split any two protocol states into two inequal duplicate-free subsets *) 
Lemma split_nodup_incl_lists {X} `{StrictlyComparable X} :
  forall (ls : list X),
    ls <> [] -> 
  exists (ls1 ls2 : list X),
    incl ls1 ls /\ incl ls2 ls /\
    NoDup ls1 /\ NoDup ls2 /\
    ~ set_eq ls1 ls2. 
Proof.
  intros ls H_non_nil.
  induction ls as [|hd tl IHls].
  - exfalso; apply H_non_nil.
    reflexivity.
  - destruct tl.
    exists [hd], [].
    repeat split.
    apply incl_refl.
    easy.
    constructor.
    intros; inversion 1.
    constructor.
    constructor.
    intros H_absurd. destruct H_absurd.
    spec H0 hd (in_eq hd []). inversion H0.
    spec IHls. intros; inversion 1.
    destruct IHls as [ls1 [ls2 [H_incl1 [H_incl2 [H_nodup1 [H_nodup2 H_neq]]]]]].
    exists ls1, ls2; repeat split; try apply incl_tl; assumption.
Qed.

(* We can now always construct an equivocation by splitting any protocol state into duplicate-free subsets of messages *) 
Lemma binary_justification_nodup : forall (vs : list V) (c1 c2 : C) (j1 j2 : state),
  ~ set_eq j1 j2 ->
  NoDup vs ->
  NoDup (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - simpl.
    apply NoDup_cons_iff in H0.
    destruct H0 as [Hnin Hnodup]. constructor.
    + intro H0. destruct H0.
      * apply H. inversion H0; subst; clear H0.
        apply hash_state_injective in H3. 
        now apply set_eq_comm. 
      * apply Hnin. apply in_flat_map in H0.
        destruct H0 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
    + apply IHvs in Hnodup. apply NoDup_cons_iff; split; try assumption. intro.
      apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
      destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
Qed.

Lemma binary_justification_protocol_state : forall vs c1 j1 c2 j2,
    protocol_state j1 ->
    protocol_state j2 ->
    ~ set_eq j1 j2 ->
    valid_estimate c1 j1 ->
    valid_estimate c2 j2 ->
    NoDup vs ->
    not_heavy (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) ->
    protocol_state (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros. 
  induction vs.
  - simpl. constructor.
  - apply NoDup_cons_iff in H4.
    destruct H4 as [Hanin Hnodup].
    simpl. apply protocol_state_cons with j1 c1 a; try assumption.
    + left; reflexivity.
    + simpl. rewrite eq_dec_if_true; try reflexivity.
      apply protocol_state_cons with j2 c2 a; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply IHvs; try assumption.
        apply not_heavy_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map in Hin. apply in_flat_map.
        destruct Hin as [v [Hinv Hinx]].
        exists v. split; try assumption. right. assumption.
      * apply NoDup_cons_iff. split; try apply binary_justification_nodup; try assumption.
        intro. apply Hanin.
        apply in_flat_map in H4. destruct H4 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
      * apply not_heavy_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map.
        { destruct Hin as [Heq | Hin].
          - subst. exists a. split; try (left; reflexivity). right. left. reflexivity.
          - apply in_flat_map in Hin. destruct Hin as [v [Hinv Hin]].
            exists v. split; try assumption. right. assumption.
        }
    + apply NoDup_cons_iff. split.
      * intro.
        { destruct H4 as [Heq | Hin].
          - apply H1. inversion Heq; subst; clear Heq.
            apply hash_state_injective in H7. 
            now apply set_eq_comm. 
          - apply Hanin.
            apply in_flat_map in Hin.
            destruct Hin as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
        }
      * apply NoDup_cons_iff.
        { split.
          - intro. apply Hanin.
            apply in_flat_map in H4. destruct H4 as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
          - apply binary_justification_nodup; assumption.
        }
Qed.

Lemma fault_weight_max : forall sigma,
  (fault_weight_state sigma <= sum_weights (set_map compare_eq_dec sender sigma))%R.
Proof.
  intros.
  apply sum_weights_incl; try apply set_map_nodup.
  unfold equivocating_senders.
  apply set_map_incl.
  intros x Hin.
  apply filter_In in Hin. destruct Hin; assumption.
Qed.

Lemma protocol_state_not_heavy : forall sigma,
  protocol_state sigma ->
  not_heavy sigma.
Proof.
  intros. inversion H.
  - unfold not_heavy. unfold fault_weight_state. simpl.
    apply Rge_le. destruct t_full; easy. 
  - assumption.
Qed.

Lemma exist_equivocating_messages : forall vs,
  vs <> nil ->
  exists j1, exists j2, protocol_state j1 /\ protocol_state j2 /\ ~ set_eq j1 j2 /\
    exists c1, exists c2,
      valid_estimate c1 j1 /\ valid_estimate c2 j2 /\
      (forall v,
        In v vs  ->
          equivocating_messages (c1, v, hash_state j1) (c2, v, hash_state j2) = true).
Proof.
  destruct (estimator_total []) as [c Hc].
  intros.
  destruct vs; try (exfalso; apply H; reflexivity); clear H. 
  destruct (estimator_total [(c, v, [])]) as [c' Hc'].
  destruct (estimator_total [(c', v, hash_state [(c, v, [])])]) as [c'' Hc''].
  exists []. exists [(c', v, hash_state [(c, v, [])])]. repeat split; try constructor.
  - apply (protocol_state_singleton c' v [(c, v, [])]) in Hc'; try constructor; try assumption.
    apply (protocol_state_singleton c v []) in Hc; try constructor; assumption.
  - intro. destruct H. apply incl_empty in H0. inversion H0.
  - exists c. exists c''. repeat split; try assumption.
    intros. unfold equivocating_messages. rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      apply andb_true_iff. split.
      * unfold hash_state, inb; simpl. 
        rewrite eq_dec_if_false; simpl; try reflexivity.
        intro. apply hash_message_injective in H0. inversion H0; subst.
      * simpl. reflexivity.
    + intro. inversion H0.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states : 
  exists p, non_trivial_pstate_light p.
Proof.
  (* Get a pivotal validator and its complement set *) 
  destruct exists_pivotal_validator as [v [vs [Hnodup [Hvnin [Hlte Hgt]]]]].
  (* Get a pair of messages in which that validator is equivocating *)
  destruct (exist_equivocating_messages (v :: vs)) as [j1 [j2 [Hj1ps [Hj2ps [Hneq12 [c1 [c2 [Hval1 [Hval2 Heqv]]]]]]]]].
  intro H; inversion H. 
  (* The property is that of containing one equivocating partner message from this pivotal validator *)
  exists (fun (p : pstate_light) => In (c1,v,hash_state j1) (proj1_sig p)).
  split.
  - (* The first state which does satisfy this property is the state containing just that one message *)
    exists (exist protocol_state [(c1,v,hash_state j1)] (protocol_state_singleton c1 v j1 Hj1ps Hval1)).
    intros sigma H. 
    apply H. left; reflexivity. 
  - (* The second state which does not satisfy the property is the state containing the message's equivocation partner, as well as messages from all the other validators in the complement set *)
    (* Why does it need to contain the messages from all the other senders? *)
    (* Because we need for the equivocation weight to be right under t_full by v's weight. *)
    (* And the idea is that each (c1, v, hash_state j1) (c2, v, hash_state j2) pair are mutually equivocating. *)
    (* And interestingly, here we are using list concatenation *) 
    assert (H_prot : protocol_state ((c2, v, hash_state j2) :: flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)).
    { apply protocol_state_cons with j2 c2 v; try assumption.
      * (* Proving that the message partner is in the new state *)
        left; reflexivity.
      * (* Proving that the new state without the message partner is a protocol state *)
        simpl. rewrite eq_dec_if_true; try reflexivity.
        (* This state is a protocol state if it's not too heavy *)
        apply binary_justification_protocol_state; try assumption.
        unfold not_heavy, fault_weight_state.
        (* Because filter map is a subset of map, sum_weights of filter map is less than or equal to sum_weights of map *)
        apply Rle_trans with (sum_weights (set_map compare_eq_dec sender (flat_map (fun v0 : V => [(c1, v0, hash_state j1); (c2, v0, hash_state j2)]) vs))); try apply fault_weight_max.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        (* In fact I think these should be set_eq *)
        (* But incl is weaker than set_eq *)
        (* x is some arbitrary validator in vs *) 
        intros x Hin.
        (* x has sent some message in the tl of the state *)
        apply set_map_exists in Hin.
        destruct Hin as [[(mc, mv) mj] [Hin Hveq]].
        simpl in Hveq. subst.
        apply in_flat_map in Hin.
        destruct Hin as [mv [Hinv Hinm]].
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * (* Proving that the new state is duplicate-free *)
        constructor; try (apply binary_justification_nodup; assumption).
        rewrite in_flat_map. intro.
        destruct H as [v'' [Hinv Hinm]].
        apply Hvnin.
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * (* Proving that the new state is not *)
        unfold not_heavy, fault_weight_state.  
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        unfold equivocating_senders.
        intros v0 Hinv0.
        apply set_map_exists in Hinv0.
        destruct Hinv0 as [[(c0, v0') j0] [Hin Heq]].
        simpl in Heq; subst.
        apply filter_In in Hin.
        destruct Hin as [Hin Hequiv].
        destruct Hin as [Heq | Hin]
        ; try (
          apply in_flat_map in Hin
          ; destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
          ; inversion Hin; subst; clear Hin; assumption
        ).
        inversion Heq; subst; clear Heq. simpl in Hequiv.
        unfold equivocating_messages in Hequiv.
        rewrite eq_dec_if_true in Hequiv; try reflexivity.
        simpl in Hequiv.
        apply existsb_exists in Hequiv.
        destruct Hequiv as [[(mc, mv) mj] [Hin Hequiv]].
        apply in_flat_map in Hin.
        unfold equivocating_messages in Hequiv.
        destruct (compare_eq_dec (c0, v0, hash_state j2) (mc, mv, mj))
        ; try (rewrite eq_dec_if_true in Hequiv; try assumption; discriminate).
        rewrite eq_dec_if_false in Hequiv; try assumption.
        destruct (compare_eq_dec v0 mv); try discriminate; subst.
        destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
        ; inversion Hin; subst; clear Hin; assumption. }
    exists (exist protocol_state ((c2, v, hash_state j2)  :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) H_prot).   
    intros sigma Hincl Hin. 
    destruct sigma as [sigma about_sigma]. 
    assert (Hpssigma := about_sigma).
    apply protocol_state_not_heavy in Hpssigma.
    apply (not_heavy_subset ((c1, v, hash_state j1) :: ((c2, v, hash_state j2) :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs))) in Hpssigma.
    * unfold not_heavy in Hpssigma.
      unfold fault_weight_state in Hpssigma.
      assert (Heq : ((c1, v, hash_state j1)
                       :: (c2, v, hash_state j2)
                       :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)
                    = flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (v :: vs))
      by reflexivity. 
      rewrite Heq in Hpssigma.
      apply (Rplus_gt_compat_r (weight v)) in Hgt.
      unfold Rminus in Hgt.
      rewrite Rplus_assoc in Hgt.
      rewrite Rplus_opp_l in Hgt.
      rewrite Rplus_0_r in Hgt.
      apply Rgt_lt in Hgt.
      apply (Rle_lt_trans _ _ _ Hpssigma) in Hgt.
      { apply (Rle_lt_trans (sum_weights (v :: vs))) in Hgt.
        - rewrite Rplus_comm in Hgt. simpl in Hgt.
          apply Rlt_irrefl with (weight v + sum_weights vs)%R.
          assumption.
        - apply sum_weights_incl.
          + constructor; assumption.
          + apply set_map_nodup.
          + intros v0 Hin0. unfold equivocating_senders.
            apply set_map_exists. exists (c1, v0, hash_state j1).
            split; try reflexivity.
            apply filter_In.
            split.
            * apply in_flat_map.
              exists v0. split; try assumption.
              left; reflexivity.
            * apply existsb_exists. exists (c2, v0, hash_state j2).
              split; try (apply Heqv; assumption).
              apply in_flat_map.
              exists v0. split; try assumption. right; left; reflexivity.
      } 
    * intros msg Hinm. 
      destruct Hinm as [Heq | Hinm]; subst; try assumption.
      apply Hincl. assumption.
Qed. 

Theorem no_local_confluence_prot_state_light :
  exists (a a1 a2 : pstate_light),
        pstate_light_rel a a1 /\ pstate_light_rel a a2 /\
        ~ exists (a' : pstate_light), pstate_light_rel a1 a' /\ pstate_light_rel a2 a'. 
Proof.
  assert (H_useful := non_triviality_decisions_on_properties_of_protocol_states).
  destruct H_useful as [P [[ps1 about_ps1] [ps2 about_ps2]]].
  exists (exist protocol_state state0 protocol_state_nil).
  exists ps1, ps2. repeat split; try (red; simpl; easy).
  intro Habsurd. destruct Habsurd as [s [Hs1 Hs2]].
  spec about_ps1 s Hs1.
  spec about_ps2 s Hs2. contradiction.
Qed.

Lemma pstate_light_eq_dec : forall (p1 p2 : pstate_light), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  assert (H_useful := about_state). 
  now apply sigify_eq_dec. 
Qed.

Lemma pstate_light_inhabited : exists (p1 : pstate_light), True.
Proof. now exists (exist protocol_state state0 protocol_state_nil). Qed.

Lemma pstate_light_rel_refl : Reflexive pstate_light_rel.
Proof.
  red. intro p.
  destruct p as [p about_p].
  red. simpl. easy. Qed.

Lemma pstate_light_rel_trans : Transitive pstate_light_rel. 
Proof. 
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  unfold pstate_rel in *; simpl in *.
  now eapply incl_tran with p2.
Qed. 

Instance level0_light : PartialOrder :=
  { A := pstate_light;
    A_eq_dec := pstate_light_eq_dec;
    A_inhabited := pstate_light_inhabited;
    A_rel := pstate_light_rel;
    A_rel_refl := pstate_light_rel_refl;
    A_rel_trans := pstate_light_rel_trans;
  }.

(* Instance level0 : PartialOrder := @level0 FullNode_syntactic. *) 

Parameter inhabited_two : at_least_two_validators. 

Instance level1_light : PartialOrderNonLCish :=
  { no_local_confluence_ish := no_local_confluence_prot_state_light; }.

(** Strong non-triviality **)
(* Defining reachablity in terms of message sending *)
Definition in_future (s1 s2 : state) :=
  incl s1 s2. 

Definition next_future (s1 s2 : state) :=
   exists (msg : message), set_eq (set_add compare_eq_dec msg s1) s2. 

Definition in_past (s1 s2 : state) :=
  incl s2 s1. 

Definition no_common_future (s1 s2 : pstate_light) :=
  forall (s : pstate_light), in_future s1 s /\ in_future s2 s -> False. 

Definition yes_common_future (s1 s2 : pstate_light) :=
  exists (s : pstate_light), in_future s1 s /\ in_future s2 s. 

Definition strong_nontriviality :=
  (* For every state, there exists a state *) 
  forall (s1 : pstate_light),
  exists (s2 : pstate_light),
    (* That is reachable in one step *) 
    next_future s1 s2 /\
    (* And there exists a third state *)
    exists (s3 : pstate_light),
      (* Such that s1 and s3 share a common future *)
      yes_common_future s1 s3
      /\
      (* But s2 and s3 don't. *) 
      no_common_future s2 s3.

Definition tweedle_dee (v : V) : message := (get_estimate [], v, hash_state []). 
Definition tweedle_dum (v : V) : message := (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])]). 

Lemma about_equivocating_messages_nil :
  forall v, equivocating_messages_prop (tweedle_dee v) (tweedle_dum v).  
Proof.
  intro v.
  apply equivocating_messages_correct.
  unfold equivocating_messages, tweedle_dee, tweedle_dum.
  rewrite eq_dec_if_false.
  + rewrite eq_dec_if_true; try reflexivity.
    apply andb_true_iff. split.
    * unfold hash_state, inb; simpl.  
      rewrite eq_dec_if_false; simpl; try reflexivity.
      intro. apply hash_message_injective in H.
      inversion H; subst.
    * simpl. reflexivity.
  + intro. inversion H.
Qed.

Lemma reach_state_equivocating_sender :
  forall (s : state) (v : V),
  exists (s' : state),
    reach s s' /\
    In v (equivocating_senders s').
Proof.
  intros s v.
  destruct (classic (In (tweedle_dee v) s)).
  - (* In the case that the first message is already there, *)
    destruct (classic (In (tweedle_dum v) s)).  
    + (* In the case that both messages are there *)
      exists s. 
      split. 
      * apply reach_refl.
      * apply equivocating_senders_correct. 
        exists (tweedle_dee v). 
        repeat split. assumption.
        red; repeat split.
        exists (tweedle_dum v).
        split. assumption.
        now apply about_equivocating_messages_nil.
    + (* In the case that tweedle_dum is absent *)
      exists (tweedle_dum v :: s).
      split. now apply incl_tl.
      apply equivocating_senders_correct. 
      exists (tweedle_dee v).
      repeat split.
      right; assumption.
      exists (tweedle_dum v).
      split. apply in_eq.
      now apply about_equivocating_messages_nil.
  - (* In the case that tweedle_dee is absent *)
    destruct (classic (In (tweedle_dum v) s)).  
    + (* In the case that only tweedle_dum is there *)
      exists (tweedle_dee v :: s). 
      split. 
      * right; now apply reach_refl.
      * apply equivocating_senders_correct.
        exists (tweedle_dee v). 
        repeat split.
        apply in_eq. 
        exists (tweedle_dum v).
        split. right; assumption. 
        now apply about_equivocating_messages_nil.
    + (* In the case that both are absent *)
      exists (tweedle_dee v :: tweedle_dum v :: s).
      split.
      apply incl_tl; now apply incl_tl.
      apply equivocating_senders_correct. 
      exists (tweedle_dee v).
      repeat split.
      apply in_eq.
      exists (tweedle_dum v).
      split. right; apply in_eq.
      now apply about_equivocating_messages_nil.
Qed.

(* Based on this proof *)
Definition next_equivocation_state (s : state) (v : V) :=
  if (inb compare_eq_dec (tweedle_dee v) s)
  then
    if (inb compare_eq_dec (tweedle_dum v) s)
    then s
    else (tweedle_dum v) :: s
  else
    if (inb compare_eq_dec (tweedle_dum v) s)
    then (tweedle_dee v) :: s
    else (tweedle_dum v :: tweedle_dee v :: s). 

Lemma in_correct :
  forall (s : state) (msg : message),
    In msg s <-> inb compare_eq_dec msg s = true. 
Proof.
  intros s msg.
  apply in_function.
Qed.

Lemma in_correct' :
  forall (s : state) (msg : message),
    ~ In msg s <-> inb compare_eq_dec msg s = false. 
Proof.
  intros s msg.
  symmetry. apply mirror_reflect_curry. 
  symmetry; now apply in_correct. 
Qed.

Lemma case_next_equivocation_state :
  forall (s : state) (v : V),
    (In (tweedle_dee v) s /\ In (tweedle_dum v) s /\
     next_equivocation_state s v = s)
    \/
    (In (tweedle_dee v) s /\ ~ In (tweedle_dum v) s /\
     next_equivocation_state s v = (tweedle_dum v) :: s)
    \/
    (~ In (tweedle_dee v) s /\ In (tweedle_dum v) s /\
     next_equivocation_state s v = (tweedle_dee v) :: s)
    \/
    (~ In (tweedle_dee v) s /\ ~ In (tweedle_dum v) s /\
     next_equivocation_state s v = (tweedle_dum v :: tweedle_dee v :: s)). 
Proof.
  intros s v.
  unfold next_equivocation_state. 
  destruct (classic (In (tweedle_dee v) s)) as [H_dee_yes | H_dee_no].
  - destruct (classic (In (tweedle_dum v) s)) as [H_dum_yes | H_dum_no].
    + left. repeat split; try assumption.
      apply in_correct in H_dee_yes.
      apply in_correct in H_dum_yes.
      rewrite H_dee_yes, H_dum_yes; tauto.
    + right; left. repeat split; try assumption. 
      apply in_correct in H_dee_yes.
      apply in_correct' in H_dum_no.
      rewrite H_dee_yes, H_dum_no; tauto.
  - destruct (classic (In (tweedle_dum v) s)) as [H_dum_yes | H_dum_no].
    + right; right; left. repeat split; try assumption. 
      apply in_correct' in H_dee_no.
      apply in_correct in H_dum_yes.
      rewrite H_dee_no, H_dum_yes; tauto. 
    + right; right; right. repeat split; try assumption.
      apply in_correct' in H_dee_no.
      apply in_correct' in H_dum_no.
      rewrite H_dee_no, H_dum_no; tauto.
Qed.

Tactic Notation "case_deedum" constr(a) constr(b) :=
  destruct (case_next_equivocation_state a b) as
    [[H_dee_in [H_dum_in H_unfold]] | [[H_dee_in [H_dum_out H_unfold]] | [[H_dee_out [H_dum_in H_unfold]] | [H_dee_out [H_dum_out H_unfold]]]]]. 
  
Lemma tweedle_dee_in :
  forall (s : state) (v : V),
    In (tweedle_dee v) (next_equivocation_state s v).
Proof.
  intros s v.
  case_deedum s v; rewrite H_unfold; try tauto. 
  right; assumption.
  apply in_eq.
  right; apply in_eq.
Qed.

Lemma tweedle_dum_in :
  forall (s : state) (v : V),
    In (tweedle_dum v) (next_equivocation_state s v).
Proof.
  intros s v.
  case_deedum s v; rewrite H_unfold; try tauto. 
  apply in_eq.
  right; assumption.
  apply in_eq.
Qed.
  
Lemma next_equivocation_state_correct :
  forall (s : state) (v : V),
    reach s (next_equivocation_state s v) /\
    In v (equivocating_senders (next_equivocation_state s v)).
Proof.
  intros s v.
  case_deedum s v; rewrite H_unfold.
  - split. 
    apply reach_refl.
    apply equivocating_senders_correct. 
    exists (tweedle_dee v). 
    repeat split; try assumption. 
    exists (tweedle_dum v).
    split; try assumption.
    now apply about_equivocating_messages_nil.
  - split.
    now apply incl_tl.
    apply equivocating_senders_correct. 
    exists (tweedle_dee v).
    repeat split. 
    right; assumption. 
    exists (tweedle_dum v).
    split. apply in_eq.
    now apply about_equivocating_messages_nil.
  - split. 
    right; assumption.
    apply equivocating_senders_correct.
    exists (tweedle_dee v). 
    repeat split.
    apply in_eq. 
    exists (tweedle_dum v).
    split. right; assumption. 
    now apply about_equivocating_messages_nil.
  - split.
    right; right; now apply reach_refl.
    apply equivocating_senders_correct. 
    exists (tweedle_dee v).
    repeat split.
    right; apply in_eq.
    exists (tweedle_dum v).
    split. apply in_eq.
    now apply about_equivocating_messages_nil.
Qed.

Lemma next_equivocation_state_incl :
  forall (j : state) (v : V),
    incl j (next_equivocation_state j v). 
Proof.
  intros j v.
  apply next_equivocation_state_correct.
Qed.

Lemma next_equivocation_state_keeps_equivocators :
  forall (j : state) (v : V),
    In v (equivocating_senders j) ->
    In v (equivocating_senders (next_equivocation_state j v)). 
Proof.
  intros.
  assert (H_incl := equivocating_senders_incl).
  spec H_incl j (next_equivocation_state j v) (next_equivocation_state_incl j v).
  now apply H_incl. 
Qed.

Lemma next_equivocation_state_keeps_equivocating_messages :
  forall (j : state) (v : V) (msg : message),
    equivocating_in_state_prop msg j ->
    equivocating_in_state_prop msg (next_equivocation_state j v). 
Proof.
  intros.
  assert (H_incl := equivocating_in_state_incl).
  spec H_incl j (next_equivocation_state j v) (next_equivocation_state_incl j v).
  now apply H_incl. 
Qed.

Lemma about_equivocating_messages_in_state_l :
  forall j v,
    equivocating_in_state_prop (tweedle_dee v)
                               (next_equivocation_state j v).
Proof.
  intros j v.
Admitted.

Lemma about_equivocating_messages_in_state_r :
  forall j v,
    equivocating_in_state_prop (tweedle_dum v)
                               (next_equivocation_state j v).
Proof.
  intros j v.
Admitted.

Lemma about_equivocating_messages_add_equivocator :
  forall j v,
    In v (equivocating_senders (next_equivocation_state j v)).
Proof.
  intros j v.
  apply equivocating_senders_correct.
  exists (tweedle_dee v).
  repeat split.
  apply tweedle_dee_in.
  now apply about_equivocating_messages_in_state_l.
Qed.

Lemma set_add_ignore {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    In x l ->
    set_add compare_eq_dec x l = l. 
Proof.
  induction l as [|hd tl IHtl]; intros x H_in.
  - inversion H_in.
  - inversion H_in as [H_eq | H_in_tl].
    + subst.
      simpl.
      destruct (compare_eq_dec x x). 
      reflexivity.
      contradiction.
    + simpl.
      destruct (compare_eq_dec x hd).
      reflexivity.
      spec IHtl x H_in_tl. rewrite IHtl.
      reflexivity.
Qed.

Lemma set_remove_incl {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    incl (set_remove compare_eq_dec x l) l. 
Proof. 
  induction l as [|hd tl IHl]; intros x.
  - simpl. apply incl_refl.
  - admit.
Admitted.

(* This is light node's equivalent of sending a neutral next message *) 
Lemma copy_protocol_state :
  forall (s : state),
    protocol_state s ->
    forall (v : V),
      not_heavy (state_add (get_estimate [], v, hash_state []) s) ->
      protocol_state (state_add (get_estimate [], v, hash_state []) s). 
Proof.
  intros s about_s v H_underweight.
  apply protocol_state_cons with [] (get_estimate []) v; try assumption; try constructor; try apply get_estimate_correct.
  apply set_add_iff. tauto. 
  destruct (classic (In (get_estimate [], v, hash_state []) s)).
  unfold state_add.
  rewrite set_add_ignore. 
  2 : assumption.
  apply protocol_state_incl with s. 
  assumption.
  apply set_remove_nodup.
  now apply protocol_state_nodup. 
  apply set_remove_incl.
  apply add_remove_inverse in H.
  unfold state_add.
  rewrite <- H in about_s.
  assumption.
  apply set_add_nodup.
  now apply protocol_state_nodup.
Qed.

Lemma add_weight :
  forall (j : state) (v : V),
    protocol_state j ->
    ~ In v (equivocating_senders j) -> 
    fault_weight_state (next_equivocation_state j v) =
    (fault_weight_state j +
     proj1_sig (weight v))%R.
Proof.
  intros j v H_prot H_notin.
Admitted. 

Definition add_weight_under (s : state) (v : V) :=
  (fault_weight_state s + proj1_sig (weight v) <= proj1_sig t_full)%R.

Lemma equivocation_adds_fault_weight : 
  forall (j : state),
    protocol_state j ->
    forall (v : V),
      ~ In v (equivocating_senders j) -> 
      fault_weight_state (next_equivocation_state j v) = 
      (fault_weight_state j + proj1_sig (weight v))%R. 
Proof.
  intros j about_j v about_v.
  rewrite add_weight; try assumption; reflexivity. 
Qed.

(* Under not-overweight conditions, the resulting state is a protocol state *) 
Theorem next_equivocation_protocol_state :
  forall j,
    protocol_state j ->
    forall v,
      ~ In v (equivocating_senders j) -> 
      (* This is the most minimal condition we need about fault weight *) 
      (add_weight_under j v ->
       protocol_state (next_equivocation_state j v)). 
Proof.
  intros j about_j v H_notin H_weight. 
  assert (H_useful := about_equivocating_messages_nil v).
  destruct H_useful as [H2_noteq [H2_sender [H2_left H2_right]]]. 
  (* Now. *)
Admitted. 

(* Under additional not-already-equivocating conditions, the resulting state actually adds weight *)
Lemma next_equivocation_adds_weight :
  forall (s : state),
    protocol_state s ->
    forall (v : V),
      (* If the weight is not over *) 
      add_weight_under s v ->
      (* And the sender is not already equivocating *) 
      ~ In v (equivocating_senders s) -> 
        (* Then we get a protocol state *) 
        protocol_state (next_equivocation_state s v) /\
        (* With increased weight *) 
        fault_weight_state (next_equivocation_state s v) =
        (fault_weight_state s + proj1_sig (weight v))%R. 
Proof.
  intros s about_s v H_not_heavy H_notin.
  split.
  apply next_equivocation_protocol_state; assumption.
  rewrite equivocation_adds_fault_weight; easy. 
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

Fixpoint next_equivocation_rec (s : state) (vs : list V) :=
  match vs with
  | [] => s
  | hd :: tl => next_equivocation_state (next_equivocation_rec s tl) hd
  end.

Lemma next_equivocation_state_keeps_messages :
  forall (j : state) (v : V) (msg : message),
    In msg j ->
    In msg (next_equivocation_state j v). 
Proof.
  apply next_equivocation_state_incl.
Qed.

Lemma next_equivocations_keeps_messages :
  forall (s : state) (vs : list V),
  forall (msg : message),
    In msg s ->
    In msg (next_equivocation_rec s vs). 
Proof.
  intros s vs msg H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    now apply next_equivocation_state_keeps_messages.
Qed.

Lemma next_equivocations_keeps_equivocating_senders :
  forall (s : state) (vs : list V),
  forall (v : V),
    In v (equivocating_senders s) ->
    In v (equivocating_senders (next_equivocation_rec s vs)). 
Proof.
  intros s vs v H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    unfold next_equivocation_state. 
    case_deedum s v.
Admitted.

Lemma next_equivocation_equivocating_sender_cons :
  forall (s : state),
    protocol_state s ->
    forall (hd : V) (v : V),
      In v (equivocating_senders (next_equivocation_state s hd)) <->
      v = hd \/ In v (equivocating_senders s).
Proof.
  intros s about_s hd v.
Admitted. 

Lemma next_equivocations_equivocating_senders_iff :
  forall (s : state) (vs : list V) (v : V),
    In v (equivocating_senders (next_equivocation_rec s vs)) <->
    In v vs \/ In v (equivocating_senders s). 
Proof.
Admitted.

Lemma next_equivocations_add_weights : 
  forall (s : state),
    protocol_state s ->
    forall (vs : list V),
      NoDup vs -> 
      (* The sum weight is not over *)
      (fault_weight_state s + sum_weights vs <= proj1_sig t_full)%R ->
      (* None of the senders are already equivocating *) 
      (forall (v : V),
          In v vs -> ~ In v (equivocating_senders s)) ->
      (* Then we end up with a protocol state *)
      protocol_state (next_equivocation_rec s vs) /\
      (* And s recursively adds the sums of all the weights in vs *) 
      fault_weight_state (next_equivocation_rec s vs) =
      (fault_weight_state s + sum_weights vs)%R.
Proof.
  intros s about_s vs H_nodup H_underweight H_disjoint. 
  induction vs as [|hd tl IHvs].
  - (* Base case : no validators to add *)
    split. assumption. 
    rewrite Rplus_0_r. reflexivity.
  - (* Induction step *)
    (* Discharging first premise *)  
    spec IHvs. 
    rewrite NoDup_cons_iff in H_nodup; tauto.
    (* Discharging second premise *)
    spec IHvs.
    simpl in H_underweight.
    apply (Rplus_le_reg_pos_r (fault_weight_state s + sum_weights tl) (proj1_sig (weight hd)) (proj1_sig t_full)).
    destruct (weight hd). firstorder.
    rewrite Rplus_assoc.
    rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
    rewrite <- Rplus_assoc.
    rewrite <- Rplus_assoc in H_underweight.
    assumption.
    (* Discharging third premise *)
    spec IHvs.
    intros. spec H_disjoint v. spec H_disjoint. 
    right; assumption.
    assumption. 
    (* Now. *)
    destruct IHvs as [H_prot H_weight].
    spec H_disjoint hd (in_eq hd tl).
    assert (H_notin_tl : ~ In hd tl).
    { rewrite NoDup_cons_iff in H_nodup.
      tauto. }
    assert (H_rewrite := next_equivocations_equivocating_senders_iff s tl hd).
    split.
    + simpl. 
      apply next_equivocation_protocol_state; try assumption.
      intros H_absurd.
      rewrite H_rewrite in H_absurd.
      tauto.
      (* Need a helper lemma about weight adding here *) 
      unfold add_weight_under.
      rewrite H_weight. simpl in H_underweight.
      rewrite <- Rplus_assoc in H_underweight.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
      rewrite <- Rplus_assoc.
      assumption.
    + simpl.
      rewrite (Rplus_comm (proj1_sig (weight hd)) (sum_weights tl)).
      rewrite <- Rplus_assoc.
      rewrite <- H_weight.
      apply equivocation_adds_fault_weight; try assumption.
      intro H_absurd. rewrite H_rewrite in H_absurd.
      tauto. 
Qed. 

Definition potentially_pivotal_state (v : V) (s : state) :=
  (* We say that v is a pivotal validator for some state s iff : *)
  (* v is not already equivocating in s *) 
  ~ In v (equivocating_senders s) /\
  (* There is a remaining list of validators *) 
  exists (vs : list V),
    (* That is duplicate-free *)
    NoDup vs /\
    (* Doesn't contain v *)
    ~ In v vs /\ 
    (* That are all not already equivocating in s *) 
    (forall (v : V), In v vs -> ~ In v (equivocating_senders s)) /\
    (* That tip over s's fault weight but only with the help of v *) 
    (sum_weights ((equivocating_senders s) ++ vs) <= proj1_sig t_full)%R /\
    (sum_weights ((equivocating_senders s) ++ vs) >
     proj1_sig t_full - proj1_sig (weight v))%R. 

(* This is a critical lemma *) 
Lemma all_pivotal_validator :
  forall (s : state),
    protocol_state s -> 
  exists (v : V),
    potentially_pivotal_state v s. 
Proof.
  intros s about_s.
  destruct suff_val as [vs [Hvs Hweight]].
  remember (equivocating_senders s) as eqv_s.
  remember (set_diff compare_eq_dec vs eqv_s) as vss.
  assert (sum_weights (vss ++ eqv_s) > proj1_sig t_full)%R.
  { apply Rge_gt_trans with (sum_weights vs); try assumption.
    apply Rle_ge. apply sum_weights_incl; try assumption.
    - rewrite Heqvss. apply diff_app_nodup; try assumption.
      subst. unfold equivocating_senders. apply set_map_nodup.
    - rewrite Heqvss. intros a Hin. apply in_app_iff.
      rewrite set_diff_iff. apply or_and_distr_left.
      split; try (left; assumption).
      destruct (in_dec compare_eq_dec a eqv_s); (left; assumption) || (right; assumption).
  }
  apply pivotal_validator_extension in H. 
  - destruct H as [vs' [Hnodup_vs' [Hincl_vs' [Hgt [v [Hin_v Hlt]]]]]].
    exists v. split.
    + subst. apply Hincl_vs' in Hin_v. apply set_diff_elim2 in Hin_v. assumption.
    + exists (set_remove compare_eq_dec v vs').
      assert (NoDup (set_remove compare_eq_dec v vs')) as Hnodup_remove
      ; try apply set_remove_nodup; try assumption.
      repeat split.
      * assumption.
      * try apply set_remove_elim; try assumption.
      * intros. apply set_remove_1 in H. apply Hincl_vs' in H. subst.
        apply set_diff_elim2 in H. assumption.
      * subst. rewrite sum_weights_app in *. rewrite Rplus_comm in Hlt.
        assumption.
      * apply Rlt_gt. apply Rplus_lt_reg_r with (proj1_sig (weight v)).
        unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l.
        rewrite Rplus_0_r. apply Rgt_lt.
        apply Rge_gt_trans with (sum_weights (vs' ++ eqv_s)); try assumption.
        unfold Rge. right. rewrite Rplus_comm.
        rewrite sum_weights_app. rewrite (Rplus_comm (sum_weights (equivocating_senders s))) .
        rewrite <- Rplus_assoc. rewrite sum_weights_app. subst.
        apply Rplus_eq_compat_r.
        symmetry. apply sum_weights_in; try assumption.
  - subst. apply set_map_nodup.
  - subst. apply protocol_state_not_heavy. assumption.
  - subst. apply diff_app_nodup; try assumption.
    apply set_map_nodup.
Qed.

Theorem strong_nontriviality_full : strong_nontriviality.  
Proof.
  intros [s1 about_s1]. 
  destruct (all_pivotal_validator s1 about_s1) as [v [H_v [vs [H_nodup [H_v_notin [H_disjoint [H_under H_over]]]]]]].
  case_eq (inb compare_eq_dec (tweedle_dee v) s1); intro H_rewrite. 
  - (* In the case that tweedle dee is already in s1, *)
    (* How to guarantee that s2 doesn't increase weight? *)
Abort. 
