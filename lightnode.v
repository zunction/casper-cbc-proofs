Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts Classical.
Import ListNotations.    
From Casper  
Require Import preamble ListExtras ListSetExtras sorted_lists protocol.

(** Building blocks for instancing CBC_protocol with light node version **)
(** Set equality on states **)

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

Variable hash : Type.
Variable (about_H : `{StrictlyComparable hash}). 

Definition justification_type : Type := list hash. 

Lemma justification_type_inhabited : exists (j : justification_type), True. 
Proof. exists []. auto. Qed. 

Definition justification_compare : (justification_type -> justification_type -> comparison) := list_compare compare.

Instance about_justification_type : StrictlyComparable justification_type :=
  { inhabited := justification_type_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }. 

Definition message : Type := C * V * justification_type.

Definition message_type := TripleStrictlyComparable C V justification_type.

Definition estimate (msg : message) : C :=
  match msg with (c, _, _) => c end.

Definition sender (msg : message) : V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : justification_type :=
  match msg with (_, _, j) => j end.

(* Defining new states for light node version *) 
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

Definition state_eq (s1 s2 : state) := incl s1 s2 /\ incl s2 s1.

Definition state_union (s1 s2 : state) : state := set_union compare_eq_dec s1 s2. 

Lemma state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1).
Proof.
  intros; unfold state_eq; split;
  intros x H_in;
  now apply set_union_comm.
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
       destruct H_eq as [H_eq _]. spec H_eq x H_reach; assumption. Qed. 

(* Defining protocol_state as a predicate *)
Parameters (get_hash : message -> hash)
           (get_hash_injective : Injective get_hash).
 
Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _  => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match compare_eq_dec v1 v2 with
      | left _  => negb (inb compare_eq_dec (get_hash msg1) j2) && negb (inb compare_eq_dec (get_hash msg2) j1)
      | right _ => false
      end
    end
  end.

Definition equivocating_messages_prop (msg1 msg2 : message) : Prop :=
  msg1 <> msg2 /\ sender msg1 = sender msg2 /\ ~ In (get_hash msg1) (justification msg2) /\ ~ In (get_hash msg2) (justification msg1).

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
    assert (H_in1_bool : inb compare_eq_dec (get_hash (c1,v1,j1)) (justification (c2,v2,j2)) = false).
    { rewrite mirror_reflect_curry.  exact H_in1.
      intros. symmetry. rewrite <- (in_function compare_eq_dec _ _ ). tauto. }
    assert (H_in2_bool : inb compare_eq_dec (get_hash (c2,v2,j2)) (justification (c1,v1,j1)) = false).
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

Lemma equivocating_in_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  forall msg,
  equivocating_in_state msg sigma = true -> equivocating_in_state msg sigma' = true.
Proof.
  unfold equivocating_in_state. 
  intros. rewrite existsb_exists in *.
  destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
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

Lemma equivocating_senders_nodup : forall sigma,
  NoDup (equivocating_senders sigma).
Proof.
  intros. apply set_map_nodup.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  incl sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_in_state msg sigma) sigma').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_in_state_incl. assumption.
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

(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> C -> Prop)
           (estimator_total : forall s : state, exists c : C, estimator s c). 

Definition get_estimate (s : state) :=
  proj1_sig (choice C (estimator s) (estimator_total s)).

Definition get_estimate_correct (s : state) :=
  proj2_sig (choice C (estimator s) (estimator_total s)). 

Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
  estimator sigma c.

Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

(* What if we don't need sorted hashes here either *) 
Definition hash_state (sigma : state) : justification_type :=
  map get_hash sigma.

Inductive protocol_state : state -> Prop :=
| protocol_state_nil : protocol_state state0
| protocol_state_cons : forall (c : C) (v : V) (j sigma' : state),
    protocol_state j -> 
    valid_estimate_condition c j ->  
    In (c, v, hash_state j) sigma' ->
    protocol_state (set_remove compare_eq_dec (c, v, hash_state j) sigma') ->
    NoDup sigma' ->
    fault_tolerance_condition sigma' ->
    protocol_state sigma'.

Lemma fault_tolerance_condition_subset : forall sigma sigma',
  incl sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup sigma.
Proof.
  intros. inversion H; subst.
  - constructor.
  - assumption.
Qed.

Lemma fault_tolerance_condition_set_eq : forall sigma sigma',
  set_eq sigma sigma' ->
  fault_tolerance_condition sigma ->
  fault_tolerance_condition sigma'.
Proof.
  intros. destruct H.
  apply (fault_tolerance_condition_subset _ _ H1 H0).
Qed. 
  
Lemma set_eq_protocol_state : forall sigma,
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
    apply (protocol_state_cons c v j); try assumption.
    + destruct H3. now apply (H3 (c, v, hash_state j)). 
    + apply (fault_tolerance_condition_set_eq _ _ H3 H2).
    + now apply set_remove_nodup. 
Qed.

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
    assert (protocol_state (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with (state_union sig1 sigma'); try assumption.
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
    + apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))
      ; try assumption.
      apply set_eq_remove_union_in; assumption.
    + apply (protocol_state_cons c v j); try assumption.
      * apply set_union_iff. right. assumption.
      * apply (set_remove_nodup compare_eq_dec (c, v, hash_state j)) in HnodupUs1s' as Hnoduprem.
        apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))
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
      assert (H' : inb compare_eq_dec (get_hash (c0,v,sigma'_hash)) (hash_state sigma1) = true). 
      { apply in_function.
        unfold hash_state.
        rewrite in_map_iff.
        exists (c0,v,sigma'_hash).
        split. reflexivity.
        now apply (in_function compare_eq_dec). }
      rewrite H'. tauto.
    + reflexivity.
    + assumption. 
Qed.

(* 
Definition equivocating_senders' (sigma : state) : set V :=
  map sender (filter (fun msg => equivocating_in_state msg sigma) sigma).

Lemma equivocating_senders_equiv :
  forall s, equivocating_senders' s = equivocating_senders s. 
Proof.
  intros. induction s.
  simpl. reflexivity.
  unfold equivocating_senders, equivocating_senders'.
*) 

Lemma equivocating_senders_extend : forall sigma c v,
  equivocating_senders (set_add compare_eq_dec (c, v, hash_state sigma) sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  (* Why doesn't the suff tactic work *) 
  f_equal.
  
  { try (rewrite H_suff; reflexivity).
    simpl.
    assert
      (Hequiv : equivocating_in_state (c, v, hash_state sigma) (set_add compare_eq_dec (c, v, hash_state sigma) sigma) = false); try rewrite Hequiv.
    { apply existsb_forall. intros.
      rewrite equivocating_messages_comm.
      apply set_add_iff in H. destruct H as [Heq | Hin].
      - subst. unfold equivocating_messages.
        rewrite eq_dec_if_true; reflexivity.
      - apply non_equivocating_messages_extend. assumption.
    }
    simpl. 
    admit.
Admitted.

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

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition [msg].
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. destruct t_full. easy.
Qed.

Lemma protocol_state_singleton : forall c v j,
  protocol_state j ->
  valid_estimate_condition c j ->
  protocol_state [(c, v, hash_state j)].
Proof.
  intros.
  apply protocol_state_cons with c v j; try assumption.
  - left. reflexivity.
  - simpl. rewrite eq_dec_if_true; constructor.
  - constructor; try constructor. apply in_nil.
  - apply fault_tolerance_condition_singleton.
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

Lemma exist_equivocating_messages : forall vs,
  vs <> nil ->
  exists j1, exists j2, protocol_state j1 /\ protocol_state j2 /\ ~ set_eq j1 j2 /\
    exists c1, exists c2,
      valid_estimate_condition c1 j1 /\ valid_estimate_condition c2 j2 /\
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
        intro. apply get_hash_injective in H0. inversion H0; subst.
      * simpl. reflexivity.
    + intro. inversion H0.
Qed.

Lemma binary_justification_nodup : forall (vs : list V) (c1 c2 : C) (j1 j2 : state),
  ~ set_eq j1 j2 ->
  NoDup vs ->
  NoDup (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - simpl. apply NoDup_cons_iff in H0. destruct H0 as [Hnin Hnodup]. constructor.
    + intro H0. destruct H0.
      * apply H. inversion H0; subst; clear H0.
        unfold hash_state in H3.
        apply map_injective in H3.
        subst. apply set_eq_refl.
        apply get_hash_injective. 
      * apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
    + apply IHvs in Hnodup. apply NoDup_cons_iff; split; try assumption. intro.
      apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
      destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
Qed.

Lemma binary_justification_protocol_state : forall vs c1 j1 c2 j2,
  protocol_state j1 ->
  protocol_state j2 ->
  ~ set_eq j1 j2 ->
  valid_estimate_condition c1 j1 ->
  valid_estimate_condition c2 j2 ->
  NoDup vs ->
  fault_tolerance_condition (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) ->
  protocol_state (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)
  .
Proof.
  intros. 
  induction vs.
  - simpl. constructor.
  - apply NoDup_cons_iff in H4. destruct H4 as [Hanin Hnodup].
    simpl. apply protocol_state_cons with c1 a j1; try assumption.
    + left; reflexivity.
    + simpl. rewrite eq_dec_if_true; try reflexivity.
      apply protocol_state_cons with c2 a j2; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply IHvs; try assumption.
        apply fault_tolerance_condition_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map in Hin. apply in_flat_map.
        destruct Hin as [v [Hinv Hinx]].
        exists v. split; try assumption. right. assumption.
      * apply NoDup_cons_iff. split; try apply binary_justification_nodup; try assumption.
        intro. apply Hanin.
        apply in_flat_map in H4. destruct H4 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
      * apply fault_tolerance_condition_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
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
            unfold hash_state in H7.
            apply map_injective in H7.
            subst; apply set_eq_refl.
            apply get_hash_injective. 
          - apply Hanin.
            apply in_flat_map in Hin. destruct Hin as [v [Hinv Hin]].
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

Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition sigma.
Proof.
  intros. inversion H.
  - unfold fault_tolerance_condition. unfold fault_weight_state. simpl.
    apply Rge_le. destruct t_full; easy. 
  - assumption.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  exists p, non_trivial_pstate_light p.
Proof.
  destruct exists_pivotal_validator as [v [vs [Hnodup [Hvnin [Hlte Hgt]]]]].
  destruct (exist_equivocating_messages (v :: vs)) as [j1 [j2 [Hj1ps [Hj2ps [Hneq12 [c1 [c2 [Hval1 [Hval2 Heqv]]]]]]]]].
  intro H; inversion H. 
  exists (fun (p : pstate_light) => In (c1,v,hash_state j1) (proj1_sig p)).
  split.
  - exists (exist protocol_state [(c1,v,hash_state j1)] (protocol_state_singleton c1 v j1 Hj1ps Hval1)).
    intros sigma H. 
    apply H. left; reflexivity. 
  - assert (H_prot : protocol_state ((c2, v, hash_state j2) :: flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)).
    { apply protocol_state_cons with c2 v j2; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply binary_justification_protocol_state; try assumption.
        unfold fault_tolerance_condition.
        apply Rle_trans with (sum_weights (set_map compare_eq_dec sender (flat_map (fun v0 : V => [(c1, v0, hash_state j1); (c2, v0, hash_state j2)]) vs)))
        ; try apply fault_weight_max.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        intros x Hin.
        apply set_map_exists in Hin.
        destruct Hin as [[(mc, mv) mj] [Hin Hveq]]. simpl in Hveq. subst.
        apply in_flat_map in Hin.
        destruct Hin as [mv [Hinv Hinm]].
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * constructor; try (apply binary_justification_nodup; assumption).
        rewrite in_flat_map. intro.
        destruct H as [v'' [Hinv Hinm]].
        apply Hvnin.
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * unfold fault_tolerance_condition.
        unfold fault_weight_state.
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
    apply protocol_state_fault_tolerance in Hpssigma.
    apply (fault_tolerance_condition_subset ((c1, v, hash_state j1) :: ((c2, v, hash_state j2) :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs))) in Hpssigma.
    * unfold fault_tolerance_condition in Hpssigma.
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


Lemma about_equivocating_messages :
  forall v, equivocating_messages (get_estimate [], v, hash_state [])
                             (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])]) = true.  
Proof.
  intro v.
  unfold equivocating_messages.
  rewrite eq_dec_if_false.
  + rewrite eq_dec_if_true; try reflexivity.
    apply andb_true_iff. split.
    * unfold hash_state, inb; simpl. 
      rewrite eq_dec_if_false; simpl; try reflexivity.
      intro. apply get_hash_injective in H. inversion H; subst.
    * simpl. reflexivity.
    + intro. inversion H.
Qed.

(* Defining the state that adds this minimal equivocation *)
Definition next_equivocation_state (j : state) (v v' : V) : state :=
  set_add compare_eq_dec
    (* One equivocation partner *)
    (get_estimate [], v, hash_state [])
    (* First state *) 
    (set_add compare_eq_dec
       (* Other equivocation partner *) 
       (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])])
       (* Zero-th state *)
       j).

(* Explicit instances of various incl results *) 
Lemma next_equivocation_state_incl :
  forall (j : state) (v v' : V),
    incl j (next_equivocation_state j v v'). 
Proof.
  intros j v v' msg H_in.
  unfold next_equivocation_state.
  do 2 (apply set_add_iff; right).
  assumption.
Qed.

Lemma next_equivocation_state_keeps_messages :
  forall (j : state) (v v' : V) (msg : message),
    In msg j ->
    In msg (next_equivocation_state j v v'). 
Proof.
  apply next_equivocation_state_incl.
Qed.

Lemma next_equivocation_state_keeps_equivocators :
  forall (j : state) (v v' v0 : V),
    In v (equivocating_senders j) ->
    In v (equivocating_senders (next_equivocation_state j v v')). 
Proof.
  intros.
  assert (H_incl := equivocating_senders_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl. 
Qed.

Lemma next_equivocation_state_keeps_equivocating_messages :
  forall (j : state) (v v' : V) (msg : message),
    equivocating_in_state_prop msg j ->
    equivocating_in_state_prop msg (next_equivocation_state j v v'). 
Proof.
  intros.
  assert (H_incl := equivocating_in_state_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  spec H_incl msg.
  apply equivocating_in_state_correct in H.
  spec H_incl H.
  apply equivocating_in_state_correct. assumption. 
Qed.

Lemma about_equivocating_messages_in_state_l :
  forall j v v',
      v <> v' ->
      equivocating_in_state_prop (get_estimate [], v, hash_state [])
                                 (next_equivocation_state j v v').
Proof.
  intros j v v' H_neq.
  exists (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])]). 
  split.
  apply set_add_iff.
  right.
  apply set_add_iff. 
  left. reflexivity.
  apply equivocating_messages_correct.
  now apply about_equivocating_messages.
Qed. 

Lemma about_equivocating_messages_in_state_r :
  forall j v v',
      v <> v' ->
      equivocating_in_state_prop (get_estimate [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [], v, [])])], v, hash_state [(get_estimate [(get_estimate [], v, [])], v, hash_state [(get_estimate [] , v, [])])])
                                 (next_equivocation_state j v v').
Proof.
  intros j v v' H_neq.
  exists (get_estimate [], v, hash_state []).
  split.
  apply set_add_iff.
  left. reflexivity.
  apply equivocating_messages_prop_swap. 
  apply equivocating_messages_correct.
  now apply about_equivocating_messages.
Qed.

Lemma about_equivocating_messages_add_equivocator :
  forall j v v',
      v <> v' ->
      In v (equivocating_senders (next_equivocation_state j v v')).
Proof.
  intros j v v' H_neq.
  apply equivocating_senders_correct.
  exists (get_estimate [], v, hash_state []). 
  split.
  unfold next_equivocation_state; rewrite set_add_iff.
  left; tauto.
  split. reflexivity.
  now apply about_equivocating_messages_in_state_l.
Qed.

Lemma equivocating_senders_sorted_extend :
  forall s v,
    set_eq (equivocating_senders s)
           (equivocating_senders (set_add compare_eq_dec (get_estimate s, v, hash_state s) s)). 
Proof.
  intros.
  assert (H_useful := equivocating_senders_extend s (get_estimate s) v).
  rewrite <- H_useful.
  rewrite set_eq_comm.
  eapply set_eq_tran.
  apply set_eq_refl.
  apply set_eq_refl. 
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

Lemma add_weight_one :
  forall (j : state) (v' : V),
    fault_weight_state j =
    fault_weight_state (set_add compare_eq_dec (get_estimate j, v', hash_state j) j).
Proof.
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply equivocating_senders_sorted_extend. 
Qed.

Lemma add_weight_two :
  forall (j : state) (v v' : V),
    (fault_weight_state 
      (set_add compare_eq_dec
         (get_estimate (set_add compare_eq_dec (get_estimate j, v', hash_state j) j), v, hash_state (set_add compare_eq_dec (get_estimate j, v', hash_state j) j))
         (set_add compare_eq_dec (get_estimate j, v', hash_state j) j)) =
    fault_weight_state
      (set_add compare_eq_dec (get_estimate j, v', hash_state j) j))%R. 
Proof. 
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply set_eq_comm.
  apply equivocating_senders_sorted_extend. 
Qed.

Lemma add_equivocating_sender :
  forall (s : state),
    protocol_state s ->
    forall (msg : message),
      (exists msg',
          In msg' s /\
          equivocating_messages_prop msg msg') ->
      set_eq (equivocating_senders (set_add compare_eq_dec msg s))
             (set_add compare_eq_dec (sender msg) (equivocating_senders s)).
Proof.
  (* Because we're using set_add, we don't need to care about whether (sender msg) is already in (equivocating_senders s) *) 
  intros s about_s msg [msg' [H_in H_equiv]]. 
  destruct (classic (In msg s)) as [H_msg_in | H_msg_out].
  - (* In the case that msg is already in s, *)
    (* Adding it does nothing to the state *)
    split. 
    + intros v H_v_in.
      assert (In v (equivocating_senders s)). 
      { apply set_map_exists in H_v_in. 
        destruct H_v_in as [msg0 [H_in0 H_sender0]].
        apply filter_In in H_in0.
        destruct H_in0.
        rewrite set_add_iff in H.
        destruct H. subst.
        unfold equivocating_senders.
        apply set_map_in. apply filter_In. split. assumption.
        apply equivocating_in_state_correct.
        exists msg'. split; assumption. subst.
        unfold equivocating_senders.
        apply set_map_in. apply filter_In. split. assumption.
        apply equivocating_in_state_correct.
        rewrite equivocating_in_state_correct in H0. 
        destruct H0 as [msg0_partner H0].
        exists msg0_partner. split; try assumption.
        destruct H0. apply set_add_iff in H0.
        destruct H0; subst; assumption.
        tauto. }
      apply set_add_iff. tauto. 
    (* Adding the sender should do nothing to (equivocating_senders s) *) 
    + intros v0 H_mem.
      unfold equivocating_senders in H_mem.
      apply set_add_iff in H_mem. 
      destruct H_mem as [H_eq | H_in'].
      subst. 
      apply set_map_in. apply filter_In.
Admitted.

Lemma in_absurd :
  forall v sigma, In (get_estimate sigma, v, hash_state sigma) sigma -> False. 
Proof. Admitted.

Definition not_heavy (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

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

Lemma copy_protocol_state : forall s,
  protocol_state s ->
    forall v,
      protocol_state (set_add compare_eq_dec (get_estimate s, v, hash_state s) s).
Proof.
  intros sigma Hps v.
  eapply protocol_state_cons. apply Hps. apply get_estimate_correct.
  apply set_add_iff.
  instantiate (1 := v). left.
  reflexivity.
  rewrite add_remove_inverse. 
  assumption. intro Habsurd. apply in_absurd in Habsurd.
  contradiction.
  apply set_add_nodup. now apply protocol_state_nodup.
  unfold fault_tolerance_condition. unfold fault_weight_state.
  rewrite equivocating_senders_extend.
  apply protocol_state_not_heavy in Hps. assumption.
Qed.

Lemma add_weight_three :
  forall (j : state) (v v' : V),
    protocol_state j ->
    ~ In v (equivocating_senders j) -> 
    v <> v' -> 
    fault_weight_state (next_equivocation_state j v v') =
    (fault_weight_state 
      (set_add compare_eq_dec
         (get_estimate (set_add compare_eq_dec (get_estimate j, v', hash_state j) j), v, hash_state (set_add compare_eq_dec (get_estimate j, v', hash_state j) j))
         (set_add compare_eq_dec (get_estimate j, v', hash_state j) j)) +
     proj1_sig (weight v))%R. 
Proof.     
  intros j v v' about_j H_notin H_neq.
  assert (H_useful := add_equivocating_sender).
  spec H_useful (set_add compare_eq_dec
        (get_estimate (set_add compare_eq_dec (get_estimate j, v', hash_state j) j), v,
        hash_state (set_add compare_eq_dec (get_estimate j, v', hash_state j) j))
        (set_add compare_eq_dec (get_estimate j, v', hash_state j) j)). spec H_useful.
  { eapply protocol_state_cons.
    admit.
Admitted.
