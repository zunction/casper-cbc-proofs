Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.  
From Casper
Require Import preamble ListExtras ListSetExtras.

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

Lemma sigify_eq_dec {X : Type} `{StrictlyComparable X} :
  forall (P : X -> Prop),
    forall (x1 x2 : {x | P x}), {x1 = x2} + {x1 <> x2}. 
Proof.
  intros P x1 x2;
    destruct x1 as [x1 about_x1];
    destruct x2 as [x2 about_x2].
  simpl.
  destruct (compare_eq_dec x1 x2) as [left | right].
  left. apply proj1_sig_injective; assumption. 
  right. intro Hnot. apply proj1_sig_injective in Hnot.
  contradiction.
Qed.

Program Definition sigify_compare {X} `{StrictlyComparable X} (P : X -> Prop) : {x | P x} -> {x | P x} -> comparison := _. 
Next Obligation.
  exact (compare X0 X1).
Defined.

(* Level 0 : *)
Class PartialOrder :=
  { A : Type;
    A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True; (* ? *) 
    A_rel : A -> A -> Prop;
    A_rel_refl :> Reflexive A_rel;
    A_rel_trans :> Transitive A_rel;
  }.

(* Level 1 : *) 
Class PartialOrderNonLCish `{PartialOrder} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        A_rel a a1 /\ A_rel a a2 /\
        ~ exists (a' : A), A_rel a1 a' /\ A_rel a2 a';
  }.

(* Level Specific : *)
Class CBC_protocol_eq :=
   {
      (** Consensus values equipped with reflexive transitive comparison **) 
      consensus_values : Type; 
      about_consensus_values : StrictlyComparable consensus_values; 
      (** Validators equipped with reflexive transitive comparison **) 
      validators : Type; 
      about_validators : StrictlyComparable validators; 
      (** Weights are positive reals **) 
      weight : validators -> {r | (r > 0)%R}; 
      (** Threshold is a non-negative real **) 
      t : {r | (r >= 0)%R}; 
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R;
      (** States with equality and union **)
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state;
      state_eq : state -> state -> Prop;
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1);
      (** Reachability relation **) 
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s; 
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3; 
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);  
      reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3;  
      (** Total estimator **)
      E : state -> consensus_values -> Prop; 
      estimator_total : forall s, exists c, E s c; 
      (** Protocol state definition as predicate **) 
      prot_state : state -> Prop; 
      about_state0 : prot_state state0; 
      (** Equivocation weights from states **) 
      equivocation_weight : state -> R; 
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R; 
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2); 
   }.

(*
Class CBC_protocol :=
   {
      (** Consensus values equipped with reflexive transitive comparison **) 
      consensus_values : Type; 
      about_consensus_values : StrictlyComparable consensus_values; 
      (** Validators equipped with reflexive transitive comparison **) 
      validators : Type; 
      about_validators : StrictlyComparable validators; 
      (** Weights are positive reals **) 
      weight : validators -> {r | (r > 0)%R}; 
      (** Threshold is a non-negative real **) 
      t : {r | (r >= 0)%R}; 
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R; 
      (** States with syntactic equality **) 
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state; 
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_union s1 s2 = state_union s2 s1;
      (** Reachability relation **) 
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s; 
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3; 
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);  
      (** Total estimator **)
      E : state -> consensus_values -> Prop; 
      estimator_total : forall s, exists c, E s c; 
      (** Protocol state definition as predicate **) 
      prot_state : state -> Prop; 
      about_state0 : prot_state state0;
      (** Equivocation weights from states **) 
      equivocation_weight : state -> R; 
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R; 
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2); 
   }.
 *)

Theorem reach_total `{CBC_protocol_eq} :
  forall s, exists s', reach s s'.
Proof. intro s. exists (state_union s s). apply (reach_union s s). Qed.

Section CommonFutures. 

  (* Theorem 1 *) 
  Theorem pair_common_futures `{CBC_protocol_eq}:
    forall s1 s2,
      prot_state s1 ->
      prot_state s2 ->
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      exists s, prot_state s /\ reach s1 s /\ reach s2 s.
  Proof.
    intros s1 s2 H_s1 H_s2 H_weight.
    exists (state_union s1 s2); split.
    apply about_prot_state; assumption. 
    split. apply reach_union.
    apply (reach_morphism s2 (state_union s2 s1) (state_union s1 s2)). 
    apply reach_union.
    apply state_union_comm. 
  Qed.
  
  Lemma reach_union_iter `{CBC_protocol_eq} :
    forall s ls, In s ls -> reach s (fold_right state_union state0 ls). 
  Proof.
    intros s ls H_in.
    induction ls as [|hd tl IHtl].
    - inversion H_in.
    - destruct H_in as [Heq | Hneq].
      + subst.
        simpl. apply reach_union.
      + spec IHtl Hneq. simpl. 
        eapply reach_trans.
        exact IHtl.  
        apply (reach_morphism (fold_right state_union state0 tl)
                              (state_union (fold_right state_union state0 tl) hd)
                              (state_union hd (fold_right state_union state0 tl))). 
        apply reach_union. apply state_union_comm. 
  Qed.

  Lemma prot_state_union_iter `{CBC_protocol_eq} :
    forall ls, Forall prot_state ls ->
          (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
          prot_state (fold_right state_union state0 ls). 
  Proof. 
    intros ls H_ls H_weight.
    induction ls as [|hd tl IHls].
    - simpl. exact about_state0.
    - simpl. apply about_prot_state.
      apply (Forall_inv H_ls).
      spec IHls. 
      apply Forall_forall. intros x H_in.
      rewrite Forall_forall in H_ls. spec H_ls x.
      spec H_ls. right; assumption. assumption. 
      spec IHls.
      simpl in H_weight.
      apply (Rle_trans (equivocation_weight (fold_right state_union state0 tl))
                       (equivocation_weight (state_union hd (fold_right state_union state0 tl)))
                       (proj1_sig t)).  
      apply equivocation_weight_compat.
      assumption. assumption. assumption.
  Qed.

  (* Theorem 2 *) 
  Theorem n_common_futures `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      exists s, prot_state s /\ Forall (fun s' => reach s' s) ls. 
  Proof.
    intros ls H_ls H_weight.
    exists (fold_right state_union state0 ls); split. 
    apply prot_state_union_iter; assumption.
    apply Forall_forall. intros s H_in.
    now apply reach_union_iter.
  Qed. 

End CommonFutures.

Section Consistency.

  Definition decided `{CBC_protocol_eq} (s : state) (P : state -> Prop) :=
    forall s', reach s s' -> P s'. 

  Definition not `{CBC_protocol_eq} (P : state -> Prop) :=
    fun s => P s -> False.
  
  Lemma forward_consistency `{CBC_protocol_eq} :
    forall s P,
      decided s P ->
      forall s',
        reach s s' ->
        decided s' P.
  Proof.
    intros s P H_dec s' H_rel.
    unfold decided in *.
    intros s'' H_rel'.
    assert (reach s s'') by (apply (reach_trans s s' s''); assumption).
    spec H_dec s''; now apply H_dec. 
  Qed.

  Lemma backward_consistency `{CBC_protocol_eq} :
    forall s s',
      reach s s' ->
      forall P,
      decided s' P ->
      ~ decided s (not P).
  Proof. 
    intros s s' H_rel P H_dec Hnot.
    destruct (reach_total s') as [s'' H_rel']. 
    unfold decided in *.
    spec H_dec s'' H_rel'. spec Hnot s''.
    assert (H_r : reach s s'') by (apply (reach_trans s s' s''); assumption).
    spec Hnot H_r; contradiction.
  Qed. 

  (* Theorem 3 *) 
  Theorem pair_consistency_prot `{CBC_protocol_eq} :
    forall s1 s2,
      prot_state s1 ->
      prot_state s2 ->
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      forall P, 
        ~ (decided s1 P /\ decided s2 (not P)).
  Proof.
    intros s1 s2 H_s1 H_s2 H_weight P [H_dec H_dec_not]. 
    destruct (pair_common_futures s1 s2 H_s1 H_s2 H_weight) as [s [H_s [H_r1 H_r2]]].
    spec H_dec s H_r1. spec H_dec_not s H_r2. contradiction.
  Qed. 

  (* Consistency on state properties *) 
  Definition state_consistency `{CBC_protocol_eq} (ls : list state) : Prop :=
    exists s,
      prot_state s /\
      forall (P : state -> Prop),
        Exists (fun s => decided s P) ls ->
        P s.
  
  (* Theorem 4 *) 
  Theorem n_consistency_prot `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      state_consistency ls. 
  Proof. 
    intros ls H_ls H_weight. 
    destruct (n_common_futures ls H_ls H_weight) as [s' [H_s' H_reach]].
    exists s'; split. 
    assumption.
    intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s'' [H_in'' H_dec'']].
    rewrite Forall_forall in H_reach. 
    spec H_reach s'' H_in''.
    spec H_dec'' s' H_reach.
    assumption.
  Qed.

  (* Consistency on consensus values *) 
  Definition lift `{CBC_protocol_eq} (P : consensus_values -> Prop) : state -> Prop :=
    fun s => forall c : consensus_values, E s c -> P c.

  Definition consensus_value_consistency `{CBC_protocol_eq} (ls : list state) : Prop :=
    exists c,
      forall (P : consensus_values -> Prop),
        Exists (fun s => decided s (lift P)) ls ->
        P c. 

  (* Theorem 5 *)
  Theorem n_consistency_consensus `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      consensus_value_consistency ls. 
  Proof.
    intros ls H_ls H_weight. 
    destruct (n_consistency_prot ls H_ls H_weight) as [s [H_s H_dec]].
    destruct (estimator_total s) as [c about_c].
    exists c. intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s' [H_in' H_dec']].
    spec H_dec (lift P).
    spec H_dec. apply Exists_exists.
    exists s'. split; assumption.
    unfold lift in H_dec.
    spec H_dec c about_c; assumption.
  Qed.

End Consistency.

(* Level Specific -refines-> Level 0 *) 

(** Defining A **) 
Definition pstate `{CBC_protocol_eq} : Type := {s : state | prot_state s}. 
Definition pstate_proj1 `{CBC_protocol_eq} (p : pstate) : state :=
  proj1_sig p. 
Coercion pstate_proj1 : pstate >-> state.

(** Proving A_eq_dec **)
Lemma pstate_eq_dec `{CBC_protocol_eq} : forall (p1 p2 : pstate), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  assert (H_useful := about_state). 
  now apply sigify_eq_dec. 
Qed.

(** Proving A_inhabited **) 
Lemma pstate_inhabited `{CBC_protocol_eq} : exists (p1 : pstate), True.
Proof. now exists (exist prot_state state0 about_state0). Qed. 

(** Defining A_rel **) 
Definition pstate_rel `{CBC_protocol_eq} : pstate -> pstate -> Prop :=
  fun p1 p2 => reach (pstate_proj1 p1) (pstate_proj1 p2).

(** Proving A_rel_refl **) 
Lemma pstate_rel_refl `{CBC_protocol_eq} : Reflexive pstate_rel.
Proof. red; intro p; now apply reach_refl. Qed.

(** Proving A_rel_trans **) 
Lemma pstate_rel_trans `{CBC_protocol_eq} : Transitive pstate_rel. 
Proof. 
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  now apply reach_trans with p2.
Qed.

Instance level0 `{CBC_protocol_eq} : PartialOrder :=
  { A := pstate;
    A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    A_rel := pstate_rel;
    A_rel_refl := pstate_rel_refl;
    A_rel_trans := pstate_rel_trans;
  }.

