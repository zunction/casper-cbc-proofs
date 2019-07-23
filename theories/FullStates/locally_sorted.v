Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation.
Import ListNotations.  
From Casper
Require Import preamble ListExtras ListSetExtras.

Class StrictPartialOrder (A : Type) :=
  { rel : A -> A -> Prop;
    rel_transitive : Transitive rel;
  }. 

Class PartialOrder (A : Type) `{StrictPartialOrder A} :=
  { rel_reflexive : Reflexive rel;
  }.

Class Join (A : Type) `{PartialOrder A} :=
  { join : A -> A -> A;
    left_intro_join : forall a1 a2, rel a1 (join a1 a2);
    right_intro_join : forall a1 a2, rel a2 (join a1 a2);
    rel_join_join : forall a1 a2 d, rel a1 d -> rel a2 d -> rel (join a1 a2) d;
  }. 

Class Meet (A : Type) `{PartialOrder A} :=
  { meet : A -> A -> A;
    left_intro_meet : forall a1 a2, rel (meet a1 a2) a1;
    right_intro_meet : forall a1 a2, rel (meet a1 a2) a2;
    rel_join_meet : forall a1 a2 d, rel d a1 -> rel d a2 -> rel d (meet a1 a2);
  }. 

Class JoinSemiLattice (A : Type) `{PartialOrder A} `{Join A} := { }. 

Class MeetSemiLattice (A : Type) `{PartialOrder A} `{Meet A} := { }. 

Definition is_principal_order (A : Type) `{PartialOrder A} (a : A) (l : list A) : Prop :=
  forall a', In a' l -> rel a' a. 

Class CBC_protocol :=
   {
      (** Consensus values equipped with reflexive transitive comparison **) 
      C : Type; (* done *) 
      about_C : StrictlyComparable C; (* done *) 
      (** Validators equipped with reflexive transitive comparison **) 
      V : Type; (* done *) 
      about_V : StrictlyComparable V; (* done *) 
      (** Weights are positive reals **) 
      weight : V -> {r | (r > 0)%R}; (* done *) 
      (** Threshold is a non-negative real **) 
      t : {r | (r >= 0)%R}; (* done *) 
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R; (* done *) 
      (** States equipped with their own notion of equality **) 
      state : Type; (* done, with abstract implementation *) 
      state0 : state; (* done *) 
      state_eq : state -> state -> Prop; (* done *) 
      state_union : state -> state -> state; (* done *) 
      eq_state_refl : reflexive state state_eq; (* done *) 
      eq_state_sym : symmetric state state_eq; (* done *) 
      eq_state_trans : transitive state state_eq; (* done *) 
      state0_neutral : forall s, state_eq (state_union s state0) s; (* done *) 
      state_union_compat : forall s1 s2, state_eq s1 s2 -> 
                                    forall t1 t2, state_eq t1 t2 ->
                                             state_eq (state_union s1 t1) (state_union s2 t2); (* done *) 
      reach : state -> state -> Prop; (* done *) 
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3; (* done *) 
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1); (* done *) 
      reach_union : forall s1 s2, reach s1 (state_union s1 s2); (* done *) 
      reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3; (* done *) 
      (* Estimator *)
      E : state -> C -> Prop; (* done *) 
      estimator_total : forall s, exists c, E s c; (* done *) 
      (* Protocol state definition as predicate *) 
      prot_state : state -> Prop; (* wip *) 
      about_state0 : prot_state state0; (* done *) 
      (* Obtaining equivocation weight from a state *) 
      equivocation_weight : state -> R; (* wip *) 
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R; (* wip *) 
      (* Protocol state is some kind of morphism *)
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2); (* wip *)
   }.

Add Parametric Relation `{CBC_protocol} : state state_eq 
  reflexivity proved by (eq_state_refl)
  symmetry proved by (eq_state_sym)
  transitivity proved by (eq_state_trans)
  as eq_state_rel.

Add Parametric Morphism `{CBC_protocol} : state_union
  with signature state_eq ==> state_eq ==> state_eq as state_union_mor.
Proof. exact state_union_compat. Qed. 

(*
Theorem reach_trans `{CBC_protocol} :
  forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3.
Proof. apply compare_lt_transitive. apply about_state. Qed.
 *)

Theorem reach_total `{CBC_protocol} :
  forall s, exists s', reach s s'.
Proof. intro s. exists (state_union s s). apply (reach_union s s). Qed.

Section CommonFutures. 

  (* Theorem 1 *) 
  Theorem pair_common_futures `{CBC_protocol}:
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
  
  Lemma reach_union_iter `{CBC_protocol} :
    forall s ls, In s ls -> reach s (fold_right state_union state0 ls). 
  Proof.
    intros s ls H_in.
    induction ls as [|hd tl IHtl].
    - inversion H_in.
    - destruct H_in.
      + subst.
        simpl. apply reach_union.
      + spec IHtl H0. simpl. 
        eapply reach_trans.
        exact IHtl.  
        apply (reach_morphism (fold_right state_union state0 tl)
                              (state_union (fold_right state_union state0 tl) hd)
                              (state_union hd (fold_right state_union state0 tl))). 
        apply reach_union. apply state_union_comm. 
  Qed.

  Lemma prot_state_union_iter `{CBC_protocol} :
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
  Theorem n_common_futures `{CBC_protocol} :
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

  Definition decided `{CBC_protocol} (s : state) (P : state -> Prop) :=
    forall s', reach s s' -> P s'. 

  Definition not `{CBC_protocol} (P : state -> Prop) :=
    fun s => P s -> False.
  
  Lemma forward_consistency `{CBC_protocol} :
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

  Lemma backward_consistency `{CBC_protocol} :
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
    assert (reach s s'') by (apply (reach_trans s s' s''); assumption).
    spec Hnot H0; contradiction.
  Qed. 

  (* Theorem 3 *) 
  Theorem pair_consistency_prot `{CBC_protocol} :
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
  Definition state_consistency `{CBC_protocol} (ls : list state) : Prop :=
    exists s,
      prot_state s /\
      forall (P : state -> Prop),
        Exists (fun s => decided s P) ls ->
        P s.
  
  (* Theorem 4 *) 
  Theorem n_consistency_prot `{CBC_protocol} :
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
  Definition lift `{CBC_protocol} (P : C -> Prop) : state -> Prop :=
    fun s => forall c : C, E s c -> P c.

  Definition consensus_value_consistency `{CBC_protocol} (ls : list state) : Prop :=
    exists c,
      forall (P : C -> Prop),
        Exists (fun s => decided s (lift P)) ls ->
        P c. 

  (* Theorem 5 *)
  Theorem n_consistency_consensus `{CBC_protocol} :
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


(** Building a FullNode CBC_protocol type **) 

(** Abstract consensus values **)
Parameters (C : Type)
           (C_inhabited : exists (c : C), True)
           (C_compare : C -> C -> comparison)
           (C_compare_strictorder : CompareStrictOrder C_compare). 

Instance C_type : StrictlyComparable C :=
  { inhabited := C_inhabited; 
    compare := C_compare;
    compare_strictorder := C_compare_strictorder; }. 

(** Abstract validators **) 
Parameters (V : Type)
           (V_inhabited : exists (v : V), True)
           (V_compare : V -> V -> comparison)
           (V_compare_strictorder : CompareStrictOrder V_compare). 

Instance V_type : StrictlyComparable V :=
  { inhabited := V_inhabited;
    compare := V_compare;
    compare_strictorder := V_compare_strictorder; }.  

(** Parameter weight **)
Parameter weight : V -> {r : R | (r > 0)%R}.
Definition sum_weight_senders (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l. 

(** Parameter threshold **)
Parameters (t : {r | (r >= 0)%R})
           (suff_val : exists (vs : list V), NoDup vs /\
                                        (sum_weight_senders vs > proj1_sig t)%R).

(** (Locally) Sorted states **)
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
      apply (message_lt_transitive _ _ _ Hlt) in Hlt2. clear Hlt.
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
  exfalso. apply (message_lt_irreflexive _ Hlt).
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
      apply message_lt_transitive with msg; assumption.
    }
    destruct H1in'; try assumption; subst.
    exfalso. apply (message_lt_irreflexive _ Hlt1).
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
  - exfalso. apply (message_lt_irreflexive _ H2).
  - exfalso. apply (message_lt_irreflexive _ H1).
  - exfalso. apply (message_lt_transitive _ _ _ H1) in H2. apply (message_lt_irreflexive _ H2).
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


(*****************)
(* Add_in_sorted *)
(*****************)

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
  - simpl. rewrite get_messages_next. simpl. split; apply incl_refl.
  - clear IHsigma1. simpl.
    destruct (message_compare msg (c, v, sigma1)) eqn:Hcmp.
    + simpl. apply (proj1 message_compare_strict_order) in Hcmp. subst.
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
    + apply (proj1 message_compare_strict_order) in Hcmp; inversion Hcmp; subst; clear Hcmp.
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
    + apply message_compare_asymmetric in Hcmp.
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


(*****************)
(* List_to_state *)
(*****************)

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

(*****************)
(** State Union **)
(*****************)

(** Elaine : Experimentation begin **)
Definition messages_union (m1 m2 : list message) := m1 ++ m2. 

Definition state_union (sigma1 sigma2 : state) : state :=
  (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))).

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

(** Experimentation end **)

(*
Definition state_union (sigma1 sigma2 : state) : state :=
  (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))).

Lemma state_union_messages : forall sigma1 sigma2,
  set_eq (get_messages (state_union sigma1 sigma2)) (messages_union (get_messages sigma1) (get_messages sigma2)).
Proof.
  intros.
  apply list_to_state_iff.
Qed.


Lemma state_union_incl_right : forall sigma1 sigma2,
  syntactic_state_inclusion sigma2 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages. apply set_union_incl_right. assumption.
Qed.

Lemma state_union_incl_left : forall sigma1 sigma2,
  syntactic_state_inclusion sigma1 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages. apply set_union_incl_left. assumption.
Qed.

Lemma state_union_iff : forall msg sigma1 sigma2,
  in_state msg (state_union sigma1 sigma2) <-> in_state msg sigma1 \/ in_state msg sigma2.
Proof.
  intros; unfold state_union; unfold in_state; split; intros.
  - apply state_union_messages in H. unfold messages_union in H. rewrite set_union_iff in H. assumption.
  - apply state_union_messages. unfold messages_union. rewrite set_union_iff. assumption.
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
  rewrite set_union_iff in Hin. destruct Hin.
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
 *)

(** Proof obligations from CBC_protocol **)
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

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

(* next is just syntactic sugar for add which is just syntactic sugar for Next. *)
Lemma add_in_sorted_ignore_repeat :
  forall msg c v j,
    msg = (c, v, j) ->
    forall s,
      add_in_sorted_fn msg (add (c,v,j) to s) = add (c,v,j) to s. 
Proof.     
  intros.
  simpl.
  replace (message_compare msg (c,v,j)) with Eq.
  reflexivity. subst. rewrite compare_eq_refl.
  reflexivity. exact (proj1 message_compare_strict_order).
Qed. 

Lemma add_in_sorted_fn_in :
  forall s1 s2,
    add_in_sorted_fn s1 (next s1 s2) = next s1 s2.
Proof.
  intros; destruct s1; destruct p.
  simpl. rewrite compare_eq_refl. 2 : exact (proj1 message_compare_strict_order). reflexivity.
Qed.

Lemma add_in_sorted_two :
  forall x y,
    add_in_sorted_fn y (next x Empty) = add_in_sorted_fn x (next y Empty).
Proof. 
  intros x y.
  destruct x; destruct p.
    rewrite <- add_is_next.
    simpl. destruct y; destruct p.
    rewrite <- add_is_next. simpl.
    destruct (message_compare (c0, v0, s0) (c,v,s)) eqn:H1.
    assert (H_rewrite := @compare_eq message message_compare (proj1 message_compare_strict_order)).
    rewrite H_rewrite in H1. clear H_rewrite; inversion H1; subst. 
    rewrite compare_eq_refl. reflexivity.
    exact (proj1 message_compare_strict_order).
    (apply message_compare_asymmetric in H1;
     rewrite H1; reflexivity).
        (apply message_compare_asymmetric in H1;
    rewrite H1; reflexivity).
Qed.

Lemma state_union_comm_helper_helper_helper :
  forall x y s, 
    add_in_sorted_fn y (add_in_sorted_fn x s) =
    add_in_sorted_fn x (add_in_sorted_fn y s).
Proof.                      
  intros.
  induction s. 
  - now apply add_in_sorted_two.
  - simpl.
    destruct (message_compare x (c,v,s1)) eqn:H_x.
    simpl.
    destruct (message_compare y (c,v,s1)) eqn:H_y.
    simpl. rewrite H_x. reflexivity.
    assert (x = (c,v,s1)). eapply compare_eq.
    exact H_x. subst.
    admit. 
Admitted.

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
    destruct (list_to_state l).
    + simpl. do 2 rewrite add_in_sorted_next.
      destruct (message_compare y x) eqn:H_yx.
      assert (x = y) by admit. subst; simpl.
      rewrite compare_eq_refl. reflexivity.
      exact (proj1 message_compare_strict_order).  apply message_compare_asymmetric in H_yx.
      rewrite H_yx. simpl. reflexivity.
      apply message_compare_asymmetric in H_yx. rewrite H_yx.
      simpl. reflexivity.
    + simpl.
      destruct (message_compare x (c,v,s1)) eqn:H_x.
      assert (x = (c,v,s1)) by admit. subst.
      simpl. destruct (message_compare y (c,v,s1)).
      simpl. rewrite compare_eq_refl.
      reflexivity. exact (proj1 message_compare_strict_order).  admit (* Repetition-based helper lemma here *).
      simpl. rewrite compare_eq_refl.
      reflexivity.
      exact (proj1 message_compare_strict_order).
      destruct (message_compare y (c,v,s1)) eqn:H_y.
      simpl. rewrite H_x.
      admit (* Repetition-based helper lemma *).
      admit. simpl. rewrite H_x.
      rewrite add_in_sorted_next.
      destruct (message_compare x y) eqn:H_xy.
      assert (x = y) by admit.  subst.
      rewrite compare_eq_refl. admit.
      exact (proj1 message_compare_strict_order).
      apply message_compare_asymmetric in H_xy. rewrite H_xy.
      simpl. rewrite H_y. reflexivity.
      apply message_compare_asymmetric in H_xy; rewrite H_xy.
      admit (* Same pattern again *).
      destruct (message_compare y (c,v,s1)) eqn:H_y.
      assert (y = (c,v,s1)) by admit; subst.
      simpl. rewrite compare_eq_refl.
      rewrite H_x. reflexivity.
      exact (proj1 message_compare_strict_order).
      simpl. rewrite H_y. admit.
      simpl. rewrite H_y. rewrite H_x.
      f_equal.
      apply state_union_comm_helper_helper_helper. 
  - rewrite IHPermutation1, IHPermutation2.
    reflexivity.
Admitted.

Lemma state_union_comm :
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

Lemma state_union_compat :
  forall (s1 s2 : sorted_state),
    s1 = s2 -> 
    forall (t1 t2 : sorted_state),
      t1 = t2 ->
      state_union s1 t1 = state_union s2 t2.
Proof.
  intros s1 s2 H_eq1 t1 t2 H_eq2.
  unfold state_union. subst. reflexivity.
Qed.

