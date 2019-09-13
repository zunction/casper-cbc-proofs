Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.    
From Casper 
Require Import preamble ListExtras ListSetExtras sorted_lists protocol definitions.

(** Building blocks for instancing CBC_protocol with light node version **)
(** Set equality on states **) 

Variable H: Type.
Variable (about_H : `{StrictlyComparable H}). 

(* Additional types for defining light node states *) 
Definition justification_type : Type := list H. 

Lemma justification_type_inhabited : exists (j : justification_type), True. 
Proof. exists []. auto. Qed. 

Definition justification_compare : (justification_type -> justification_type -> comparison) := list_compare compare.

Instance about_justification_type : StrictlyComparable justification_type :=
  { inhabited := justification_type_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }. 

Definition message : Type := definitions.C * definitions.V * justification_type.

Definition message_type := TripleStrictlyComparable definitions.C definitions.V justification_type.

Definition estimate (msg : message) : definitions.C :=
  match msg with (c, _, _) => c end.

Definition sender (msg : message) : definitions.V :=
  match msg with (_, v, _) => v end.

Definition justification (msg : message) : justification_type :=
  match msg with (_, _, j) => j end.

(* Defining new states for light node version *) 
Definition state := set message.

Definition state0 : state := [].

Parameter about_state : StrictlyComparable state. 

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
Parameters (hash : message -> H)
           (hash_injective : Injective hash).
 
Definition equivocating_messages (msg1 msg2 : message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _  => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match compare_eq_dec v1 v2 with
      | left _  => negb (inb compare_eq_dec (hash msg1) j2) && negb (inb compare_eq_dec (hash msg2) j1)
      | right _ => false
      end
    end
  end.

Definition equivocating_message_state (msg : message) : state -> bool :=
  existsb (equivocating_messages msg).

Lemma equivocating_message_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  forall msg,
  equivocating_message_state msg sigma = true -> equivocating_message_state msg sigma' = true.
Proof.
  unfold equivocating_message_state. 
  intros. rewrite existsb_exists in *.
  destruct H1 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H0. assumption.
Qed.

Definition equivocating_senders (sigma : state) : set definitions.V :=
  set_map compare_eq_dec sender (filter (fun msg => equivocating_message_state msg sigma) sigma).

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
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_message_state msg sigma) sigma').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_message_state_incl. assumption.
Qed.

Definition fault_weight_state (sigma : state) : R :=
  sum_weights (equivocating_senders sigma).

Lemma sum_weights_in : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove compare_eq_dec v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H1; subst; clear H.
  - inversion H1; subst; clear H1.
    simpl.
    destruct (compare_eq_dec v v). reflexivity.
    contradiction. simpl.
    destruct (compare_eq_dec v a). subst; reflexivity.
    simpl. spec IHvs H5 H0.
    rewrite IHvs. simpl. 
    rewrite <- Rplus_assoc.
    rewrite <- (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc. reflexivity.  
Qed.

Lemma sum_weights_incl : forall vs vs',
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  intros vs vs'. generalize dependent vs.
  induction vs'; intros.
  - apply incl_empty in H2. subst. apply Rle_refl.
  - inversion H1; subst; clear H1.
    destruct (in_dec compare_eq_dec a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup compare_eq_dec a). assumption.
      * assumption.
      * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
        destruct Hrem as [Hin Hxa].
        apply H2 in Hin. destruct Hin; try assumption.
        exfalso; subst. apply Hxa. reflexivity.
      * assumption.
    + simpl. apply Rle_trans with (sum_weights vs').
      * apply IHvs'; try assumption.
        intros x Hin. apply H2 in Hin as Hin'.
        destruct Hin'; try assumption.
        exfalso; subst. apply n. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. destruct (weight a). simpl; auto. 
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  incl sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
  apply equivocating_senders_incl. assumption.
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

Lemma equivocation_weight_compat : forall s1 s2, (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R. 
Proof.
  intros s1 s2.
  assert (H_useful := fault_weight_state_incl s1 (state_union s2 s1)). 
  spec H_useful.
  intros x H_in. unfold state_union.
  rewrite set_union_iff. right; assumption. 
  assumption.
Qed.

(* Defining the estimator function as a relation *) 
Parameters (estimator : state -> definitions.C -> Prop)
           (estimator_total : forall s : state, exists c : definitions.C, estimator s c). 

Definition get_estimate (s : state) :=
  proj1_sig (choice definitions.C (estimator s) (estimator_total s)).

Definition get_estimate_correct (s : state) :=
  proj2_sig (choice definitions.C (estimator s) (estimator_total s)). 

Definition valid_estimate_condition (c : definitions.C) (sigma : state) : Prop :=
  estimator sigma c.

Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t_full)%R.

(* What if we don't need sorted hashes here either *) 
Definition hash_state (sigma : state) : justification_type := map hash sigma.

Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state state0
  | protocol_state_cons : forall (c : definitions.C) (v : definitions.V) (j sigma' : state),
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
  intros. inversion H0; subst.
  - constructor.
  - assumption.
Qed.

Lemma fault_tolerance_condition_set_eq : forall sigma sigma',
  set_eq sigma sigma' ->
  fault_tolerance_condition sigma ->
  fault_tolerance_condition sigma'.
Proof.
  intros. destruct H0.
  apply (fault_tolerance_condition_subset _ _ H2 H1).
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
  - destruct H0. unfold state0 in *.
    apply incl_empty in H2; subst. constructor.
  - apply (set_eq_remove compare_eq_dec (c, v, hash_state j)) in H4 as Hset_eq; try assumption.
    apply IHH'2 in Hset_eq.
    apply (protocol_state_cons c v j); try assumption.
    + destruct H4. now apply (H4 (c, v, hash_state j)). 
    + apply (fault_tolerance_condition_set_eq _ _ H4 H3).
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
      right. apply (set_remove_1 _ _ _ _ H5).
    }
    clear IHHps2_2.
    apply protocol_state_nodup in Hps1 as Hnodups1.
    assert (HnodupUs1s' := H2).
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

Instance LightNode_seteq : CBC_protocol_eq :=
  { consensus_values := definitions.C;  
    about_consensus_values := definitions.about_C;
    validators := definitions.V;
    about_validators := definitions.about_V;
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
  




