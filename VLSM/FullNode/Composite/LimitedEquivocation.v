Require Import FinFun List ListSet RelationClasses.

Import ListNotations.

From CasperCBC
  Require Import
    Preamble
    ListExtras
    ListSetExtras
    TopSort
    CBC.Common
    CBC.Equivocation
    VLSM.Common
    VLSM.Composition
    Validator.State
    Validator.Equivocation
    FullNode.Validator
    VLSM.FullNode.Composite.Free
    PreceedsEquivocation
    .

Section ConstrainedValidators.

(** * Composing validators with limited equivocation *)

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (message := State.message C V)
    (FreeX := @VLSM_full_composed_free C V about_C about_V Hmeasurable Hrt Hestimator)
    .

Let index : Type := V + clients.
Let v_eq_dec := strictly_comparable_eq_dec about_V.
Existing Instance v_eq_dec.
Existing Instance index_eq_dec.

Fixpoint validators'
  (is : list index)
  : list V
  :=
  match is with
  | [] => []
  | i :: is' =>
    match i with
    | inl v => v :: validators' is'
    | _ => validators' is'
    end
  end.

Lemma validators'_in
  (is : list index)
  (v : V)
  : In v (validators' is) <-> In (inl v) is.
Proof.
  induction is.
  - split; intro H; inversion H.
  - destruct a; simpl; split.
    + intros [Heq | Hv].
      * subst v0. left. reflexivity.
      * right. apply IHis. assumption.
    + intros [Heq | Hv].
      * inversion Heq; subst. left. reflexivity.
      * right. apply IHis. assumption.
    + intro Hv. right. apply IHis. assumption.
    + intros [n | Hv]; try discriminate n.
      apply IHis. assumption.
Qed.

Lemma validators'_nodup
  (is : list index)
  (His : NoDup is)
  : NoDup (validators' is).
Proof.
  induction is; simpl; try apply NoDup_nil.
  apply NoDup_cons_iff in His. destruct His as [Ha His].
  specialize (IHis His).
  destruct a; try assumption.
  constructor; try assumption.
  intro Hv. elim Ha. apply validators'_in. assumption.
Qed.


Definition validators : list V := validators' indices.

Lemma finite_validators : Listing validators.
Proof.
  split.
  - apply validators'_nodup. apply (proj1 finite_index).
  - intros v. pose (proj2 finite_index (inl v)) as Hv.
    apply validators'_in. assumption.
Qed.


(*
Parameter (Hno_clients : clients -> False).
Definition v0 : V.
Proof.
  destruct (@i0 V).
  - exact v.
  - elim Hno_clients. exact c.
Defined.
*)

Lemma state_union_nodup
  (s : vstate FreeX)
  (Hs : protocol_state_prop (pre_loaded_vlsm FreeX) s)
  : NoDup (state_union s).
Proof.
  pose (VLSM_full_protocol_state_nodup s Hs) as Hnodup.
  unfold state_union.
  induction indices.
  - constructor.
  - simpl.
    apply set_union_nodup; try assumption.
    apply Hnodup.
Qed.

Lemma state_union_iff
  (s : vstate FreeX)
  (m : message)
  : In m (state_union s)
    <-> ex (fun v : V => In m (get_message_set (s (inl v))))
    \/ ex (fun client : clients => In m (s (inr client))).
Proof.
  unfold state_union.
  split.
  - intros Hm.
    apply set_union_in_iterated in Hm.
    apply Exists_exists in Hm.
    destruct Hm as [msgs [Hmsgs Hm]].
    apply in_map_iff in Hmsgs.
    destruct Hmsgs as [(_msgs, final) [Heq Hs]]. simpl in Heq. subst _msgs.
    apply in_map_iff in Hs. destruct Hs as [i [Hs Hi]].
    destruct i; simpl in Hs.
    + left. exists v. rewrite Hs. assumption.
    + right. exists c. inversion Hs. rewrite H0. assumption.
  - intros [[v Hm] | [client Hm]]
    ; apply set_union_in_iterated
    ; apply Exists_exists
    ; exists (get_message_set (s (inl v)))
      || exists (s (inr client))
    ; split; try assumption
    ; apply in_map_iff
    ; exists (s (inl v)) || exists (pair (s (inr client)) None)
    ; split; try reflexivity
    ; apply in_map_iff
    ; exists (inl v) || exists (inr client)
    ; split; try reflexivity
    ; apply (proj2 finite_index).
Qed.

Lemma state_union_initially_empty
  (is : vinitial_state FreeX)
  : state_union (proj1_sig is) = [].
Proof.
  apply incl_l_nil.
  intros m Hm.
  apply state_union_iff in Hm.
  destruct Hm as [[v Hm] | [client Hm]]
  ; destruct is as [is His]
  ; simpl in Hm
  ; specialize (His (inl v)) || specialize (His (inr client))
  ; simpl in His
  ; unfold initial_state_prop in His
  ;  rewrite His in Hm
  ; inversion Hm.
Qed.

Existing Instance VLSM_full_composed_free_basic_equivocation.

Definition Full_composition_constraint
  (l : vlabel FreeX)
  (som : vstate FreeX * option message)
  : Prop
  :=
  let (s', om') := vtransition FreeX l som in
  not_heavy s'.

Definition Full_constrained_composition : VLSM message
  := composite_vlsm IM_index i0 Full_composition_constraint.

Lemma Full_composition_constraint_state_not_heavy
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : not_heavy s.
Proof.
  destruct Hs as [_om Hs].
  inversion Hs; subst; simpl.
  - unfold s0. apply empty_not_heavy.
    simpl. rewrite state_union_initially_empty. reflexivity.
  - unfold s0. apply empty_not_heavy.
    remember (proj1_sig Common.s0) as s1. simpl. subst s1.
    rewrite state_union_initially_empty. reflexivity.
  - destruct Hv as [Hv Hctr].
    unfold Full_composition_constraint in Hctr.
    unfold vtransition in Hctr.
    simpl in Hctr.
    destruct l as (i, li).
    destruct
      (@vtransition (State.message C V)
      (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator i) li
      (@pair
         (@vstate (State.message C V)
            (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator i))
         (option (State.message C V)) (s0 i) om))
      as (si', om').
    inversion H0; subst.
    assumption.
Qed.

Existing Instance full_node_message_equivocation_evidence.

Global Instance Full_constrained_composition_message_equivocation_evidence
  : vlsm_message_equivocation_evidence V Full_constrained_composition.
Proof.
  apply
    (preceeds_equivocation_constrained
      IM_index i0 Full_composition_constraint (free_constraint _)
    ).
  - intro l; intros. exact I.
  - apply VLSM_full_composed_free_message_equivocation_evidence.
Qed.

Lemma in_protocol_state
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  (m : message)
  (i : index)
  (Hm : In m (get_message_set (project s i)))
  : protocol_message_prop Full_constrained_composition m.
Proof.
  destruct  Hs as [om Hsom].
  remember
    (@pair
      (@Common.state message (@type message Full_constrained_composition))
      (option message) s om)
    as som.
  generalize dependent i.
  generalize dependent m.
  generalize dependent om.
  generalize dependent s.
  induction Hsom; intros; inversion Heqsom; subst; clear Heqsom.
  - unfold s in *; clear s. destruct is as [is His]. simpl in *.
    specialize (His i).
    destruct i; inversion His; simpl in Hm
    ; rewrite H0 in Hm
    ; inversion Hm.
  - unfold s in *; clear s. destruct s0 as [is His]. simpl in *.
    specialize (His i).
    destruct i; inversion His; simpl in Hm
    ; rewrite H0 in Hm
    ; inversion Hm.
  - assert (Hpsom0 : option_protocol_message_prop Full_constrained_composition om0).
    { exists s0.
      replace
        (@pair (@Common.state message (@type message Full_constrained_composition)) (option message) s0 om0)
        with (vtransition Full_constrained_composition l (s, om)).
      apply protocol_generated with _om _s; assumption.
    }
    destruct l as (i', li').
    destruct i' as [v' | client']
    ; unfold vtransition in H0; simpl in H0
    ; destruct (s (inl v')) as (msgsv', finalv') eqn:Hsv'
      || remember (s (inr client')) as msgsv' eqn:Hsv'
    ; try destruct li' as [c|].
    + apply pair_equal_spec in H0. destruct H0 as [Hs Hom]; subst.
      destruct (eq_dec i (inl v')); destruct i as [v | client]; subst.
      * rewrite e in *. simpl in Hm. rewrite state_update_eq in Hm.
        apply set_add_iff in Hm.
        destruct Hm as [Heqm | Hinm]; subst; try assumption.
        apply (IHHsom1  s _om eq_refl m (inl v')). simpl.
        rewrite Hsv'. assumption.
      * discriminate e.
      * simpl in Hm. rewrite state_update_neq in Hm; try assumption.
        apply (IHHsom1  s _om eq_refl m (inl v)).
        assumption.
      * simpl in Hm. rewrite state_update_neq in Hm; try assumption.
        apply (IHHsom1  s _om eq_refl m (inr client)).
        assumption.
    + destruct om as [m'|].
      * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
        { destruct (eq_dec i (inl v')); destruct i as [v | client]; subst.
        - simpl in Hm. inversion e. subst v. rewrite state_update_eq in Hm.
          apply set_add_iff in Hm.
          destruct Hm as [Heqm | Hinm]; subst.
          + exists _s. assumption.
          + apply (IHHsom1  s _om eq_refl m (inl v')).
            simpl. rewrite Hsv'. assumption.
        - discriminate e.
        - simpl in Hm. rewrite state_update_neq in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m (inl v)).
          assumption.
        - simpl in Hm. rewrite state_update_neq in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m (inr client)).
          assumption.
        }
      * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
        rewrite state_update_id in Hm; try assumption.
        apply (IHHsom1  s _om eq_refl m i).
        assumption.
    + destruct om as [m'|].
      * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
        { destruct (eq_dec i (inr client')); destruct i as [v | client]; subst.
        - discriminate e.
        - simpl in Hm. inversion e. subst client. rewrite state_update_eq in Hm.
          apply set_add_iff in Hm.
          destruct Hm as [Heqm | Hinm]; subst.
          + exists _s. assumption.
          + apply (IHHsom1  s _om eq_refl m (inr client')).
            simpl. assumption.
        - simpl in Hm. rewrite state_update_neq in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m (inl v)).
          assumption.
        - simpl in Hm. rewrite state_update_neq in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m (inr client)).
          assumption.
        }
      * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
        rewrite state_update_id in Hm; try reflexivity.
        apply (IHHsom1  s _om eq_refl m i).
        assumption.
Qed.

Lemma state_union_protocol_message
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : Forall (protocol_message_prop Full_constrained_composition) (state_union s).
Proof.
  apply Forall_forall.
  intros m Hm.
  apply state_union_iff in Hm.
  destruct Hm as [[v Hm] | [client Hm]].
  - apply in_protocol_state with s (inl v); assumption.
  - apply in_protocol_state with s (inr client); assumption.
Qed.

Lemma state_union_byzantine_message
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : Forall (byzantine_message_prop Full_constrained_composition) (state_union s).
Proof.
  apply state_union_protocol_message in Hs.
  rewrite Forall_forall in *.
  intros m Hm.
  specialize (Hs m Hm). clear -Hs.
  apply can_emit_protocol_iff in Hs.
  apply pre_loaded_can_emit.
  destruct Hs as [[v [[miv Hmiv] Hs]] | Hem]; try assumption.
  destruct v; inversion Hmiv.
Qed.

Lemma state_union_free_byzantine_message
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : Forall (byzantine_message_prop FreeX) (state_union s).
Proof.
  rewrite Forall_forall. intros m Hm.
  apply constraint_subsumption_byzantine_message_prop with Full_composition_constraint.
  - intro l; intros. exact I.
  - specialize (state_union_byzantine_message s Hs).
    intros Hbm.
    rewrite Forall_forall in Hbm.
    apply Hbm.
    assumption.
Qed.

Definition sorted_state_union
  (s : vstate FreeX)
  : set message
  :=
  top_sort message_preceeds_fn (state_union s).

Lemma sorted_state_union_nodup
  (s : vstate FreeX)
  (Hs : protocol_state_prop (pre_loaded_vlsm FreeX) s)
  : NoDup (sorted_state_union s).
Proof.
  apply top_sort_nodup.
  apply state_union_nodup.
  assumption.
Qed.

Definition receive_label
  (s : vstate FreeX)
  (i : index)
  (m : message)
  : vlabel FreeX
  :=
  match i with
  | inl v => existT _ (inl v) None
  | inr client => existT _ (inr client) tt
  end.

Definition receive_destination
  (s : vstate FreeX)
  (i : index)
  (m : message)
  : vstate FreeX
  :=
  fst
    (vtransition Full_constrained_composition
      (receive_label s i m)
      (s, Some m)
    ).

Definition receive_message
  (s : vstate FreeX)
  (i : index)
  (m : message)
  : vtransition_item FreeX.
Proof.
  split.
  exact (receive_label s i m).
  exact (Some m).
  exact (receive_destination s i m).
  exact None.
Defined.

Fixpoint receive_messages
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  : list (vtransition_item FreeX)
  :=
  match ms with
  | [] => []
  | m :: ms' =>
    let items := receive_messages s i ms' in
    match in_dec eq_dec m (get_message_set (project s i)) with
    | left _ => items
    | right _ =>
      let final := last (map destination items) s in
      let item := receive_message final i m in
      items ++ [item]
    end
  end.

Lemma receive_messages_set_eq
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  (Hms : incl ms (state_union s))
  : set_eq (state_union s) (state_union (last (map destination (receive_messages s i (rev ms))) s)).
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; simpl; try apply set_eq_refl.
  assert (Hi : incl ms (state_union s)).
  { intros m Hm. apply Hms. apply in_app_iff. left. assumption. }
  specialize (IHms s Hi).
  rewrite rev_unit. simpl.
  destruct (in_dec eq_dec x (get_message_set (project s i))); try assumption.
  rewrite map_app. simpl. rewrite last_last.
  unfold receive_destination.  unfold vtransition. simpl.
  unfold vtransition. simpl.
  destruct IHms as [I1 I2].
  split; intros m Hm; destruct i as [v | client]; simpl in *.
  - destruct
    (@last
    (@_composite_state (State.message C V)
       (sum V clients)
       (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
    (@map
       (@transition_item (State.message C V)
          (@composite_type (State.message C V)
             (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt
                Hestimator)))
       (@_composite_state (State.message C V)
          (sum V clients)
          (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
       (@destination (State.message C V)
          (@composite_type (State.message C V)
             (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt
                Hestimator)))
       (receive_messages s (@inl V clients v) (@rev message ms))) s
    (@inl V clients v))
    as (msgs, final) eqn:Ht.
    apply state_union_iff.
    apply I1 in Hm.
    apply state_union_iff in Hm.
    destruct Hm as [[v' Hm] | [client' Hm]]; try destruct (eq_dec (inl v') (inl v)).
    + inversion e. subst v'. left.
      exists v. simpl.
      rewrite state_update_eq. simpl.
      apply set_add_iff. right.
      replace msgs with (get_message_set (msgs, final)) by reflexivity.
      rewrite <- Ht.
      assumption.
    + left. exists v'. simpl.
      rewrite state_update_neq; assumption.
    + right. exists client'. simpl.
      rewrite state_update_neq; try assumption.
      intro H; discriminate H.
  - remember
      (@last
      (@_composite_state (State.message C V)
         (sum V clients)
         (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
      (@map
         (@transition_item (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (@_composite_state (State.message C V)
            (sum V clients)
            (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
         (@destination (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (receive_messages s (@inr V clients client)
            (@rev message ms))) s (@inr V clients client)
      ) as msgs eqn:Ht.
    specialize (I1 m Hm).
    apply state_union_iff in I1.
    apply state_union_iff.
    destruct I1 as [[v' HI1] | [client' HI1]]; try destruct (eq_dec (inr client') (inr client)).
    + simpl. left. exists v'.  rewrite state_update_neq by (intro; discriminate).
      assumption.
    + inversion e. subst client'. right. exists client.
      simpl. rewrite state_update_eq.
      apply set_add_iff. right.
      subst msgs. assumption.
    + right. exists client'. simpl. rewrite state_update_neq; assumption.
  - destruct
      (@last
      (@_composite_state (State.message C V)
         (sum V clients)
         (@IM_index C V about_C about_V Hmeasurable Hrt
            Hestimator))
      (@map
         (@transition_item (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (@_composite_state (State.message C V)
            (sum V clients)
            (@IM_index C V about_C about_V Hmeasurable Hrt
               Hestimator))
         (@destination (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (receive_messages s (@inl V clients v)
            (@rev message ms))) s (@inl V clients v))
      as (msgs, final) eqn:Ht.
    apply state_union_iff in Hm.
    destruct Hm as [[v' Hm] | [client' Hm]]; try destruct (eq_dec (inl v') (inl v)).
    + inversion e. subst v'. simpl in Hm. rewrite state_update_eq in Hm.
      apply set_add_iff in Hm.
      destruct Hm as [Heq | Hm].
      * subst m. apply Hms. apply in_app_iff. right. left. reflexivity.
      * apply I2. apply state_union_iff.
        left. exists v.
        replace msgs with (get_message_set (msgs, final)) in Hm by reflexivity.
        rewrite <- Ht in Hm.
        assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by assumption.
      apply I2. apply state_union_iff.
      left. exists v'.
      assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by (intro; discriminate).
      apply I2. apply state_union_iff.
      right. exists client'.
      assumption.
  - remember
      (@last
      (@_composite_state (State.message C V)
         (sum V clients)
         (@IM_index C V about_C about_V Hmeasurable Hrt
            Hestimator))
      (@map
         (@transition_item (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (@_composite_state (State.message C V)
            (sum V clients)
            (@IM_index C V about_C about_V Hmeasurable Hrt
               Hestimator))
         (@destination (State.message C V)
            (@composite_type (State.message C V)
               (sum V clients)
               (@IM_index C V about_C about_V Hmeasurable Hrt
                  Hestimator)))
         (receive_messages s (@inr V clients client)
            (@rev message ms))) s (@inr V clients client))
      as msgs eqn:Ht.
    apply state_union_iff in Hm.
    destruct Hm as [[v' Hm] | [client' Hm]]; try destruct (eq_dec (inr client') (inr client)).
    + simpl in Hm. rewrite state_update_neq in Hm by (intro; discriminate).
      apply I2. apply state_union_iff.
      left. exists v'.
      assumption.
    + inversion e. subst client'. simpl in Hm. rewrite state_update_eq in Hm.
      apply set_add_iff in Hm.
      destruct Hm as [Heq | Hm].
      * subst m. apply Hms. apply in_app_iff. right. left. reflexivity.
      * apply I2. apply state_union_iff.
        right. exists client.
        subst msgs. assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by assumption.
      apply I2. apply state_union_iff.
      right. exists client'.
      assumption.
Qed.

Lemma receive_messages_v
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  : set_eq (get_message_set (project (last (map destination (receive_messages s i (rev ms))) s) i)) (set_union eq_dec (get_message_set (project s i)) ms).
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; try apply set_eq_refl.
  rewrite rev_unit. simpl.
  destruct (in_dec eq_dec x (get_message_set (project s i))).
  { specialize (IHms s).
    apply set_eq_tran with (set_union eq_dec (get_message_set (project s i)) ms)
    ; try assumption.
    split; intros m Hm; apply set_union_iff; apply set_union_iff in Hm
    ; destruct Hm as [Hm | Hm]; try (left; assumption); try (right; assumption).
    - right. apply in_app_iff. left. assumption.
    - apply in_app_iff in Hm. destruct Hm as [Hm | Hm]; try (right; assumption).
      left. inversion Hm; try contradiction. subst. assumption.
  }
  rewrite map_app. simpl.
  rewrite last_last.
  split; intros m Hm.
  - apply set_union_iff.
    unfold receive_destination in Hm.
    unfold vtransition in Hm. simpl in Hm.
    destruct i as [v | client]; simpl in *
    ; unfold vtransition in Hm; simpl in Hm.
    + destruct
        (@last
        (@_composite_state (State.message C V)
           (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt
              Hestimator))
        (@map
           (@transition_item (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (@_composite_state (State.message C V)
              (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt
                 Hestimator))
           (@destination (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (receive_messages s (@inl V clients v)
              (@rev message ms))) s (@inl V clients v))
        as (msgs, final) eqn:Heqlst.
      simpl in Hm.
      rewrite state_update_eq in Hm. simpl in Hm.
      apply set_add_iff in Hm.
      specialize (IHms s).
      rewrite Heqlst in IHms.
      simpl in IHms.
      destruct IHms as [Hincl _].
      destruct Hm as [Heq | Hm].
      * subst x. right. apply in_app_iff. right. left. reflexivity.
      * apply Hincl in Hm. apply set_union_iff in Hm.
        destruct Hm as [Hm | Hm]; try (left; assumption).
        right.
        apply in_app_iff. left. assumption.
    + remember
        (@last
        (@_composite_state (State.message C V)
           (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt
              Hestimator))
        (@map
           (@transition_item (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (@_composite_state (State.message C V)
              (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt
                 Hestimator))
           (@destination (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (receive_messages s (@inr V clients client)
              (@rev message ms))) s (@inr V clients client))
        as msgs eqn:Heqlst.
      simpl in Hm.
      rewrite state_update_eq in Hm. simpl in Hm.
      apply set_add_iff in Hm.
      specialize (IHms s).
      destruct IHms as [Hincl _].
      destruct Hm as [Heq | Hm].
      * subst x. right. apply in_app_iff. right. left. reflexivity.
      * rewrite <- Heqlst in Hincl. apply Hincl in Hm. apply set_union_iff in Hm.
        destruct Hm as [Hm | Hm]; try (left; assumption).
        right.
        apply in_app_iff. left. assumption.
  - apply set_union_iff in Hm.
    unfold receive_destination.
    unfold vtransition. simpl.
    destruct i as [v | client]; simpl in *
    ; unfold vtransition; simpl.
    + destruct
        (@last
        (@_composite_state (State.message C V)
           (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
        (@map
           (@transition_item (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (@_composite_state (State.message C V)
              (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
           (@destination (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (receive_messages s (@inl V clients v) (@rev message ms))) s
        (@inl V clients v))
      as (msgs, final) eqn:Heqlst.
      simpl.
      rewrite state_update_eq. simpl.
      apply set_add_iff.
      specialize (IHms s).
      rewrite Heqlst in IHms.
      simpl in IHms.
      destruct IHms as [_ Hincl].
      destruct Hm as [Hm | Hmm]
      ; try (apply in_app_iff in Hmm; destruct Hmm as [Hm | [Hm | Hnil]]; try inversion Hnil).
      * right. apply Hincl. apply set_union_iff. left. assumption.
      * right. apply Hincl. apply set_union_iff. right. assumption.
      * subst x. left. reflexivity.
    + remember
        (@last
        (@_composite_state (State.message C V)
           (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
        (@map
           (@transition_item (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (@_composite_state (State.message C V)
              (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
           (@destination (State.message C V)
              (@composite_type (State.message C V)
                 (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt
                    Hestimator)))
           (receive_messages s (@inr V clients client)
              (@rev message ms))) s (@inr V clients client))
      as msgs eqn:Heqlst.
      simpl.
      rewrite state_update_eq. simpl.
      apply set_add_iff.
      specialize (IHms s).
      destruct IHms as [_ Hincl].
      rewrite <- Heqlst in Hincl.
      destruct Hm as [Hm | Hmm]
      ; try (apply in_app_iff in Hmm; destruct Hmm as [Hm | [Hm | Hnil]]; try inversion Hnil).
      * right. apply Hincl. apply set_union_iff. left. assumption.
      * right. apply Hincl. apply set_union_iff. right. assumption.
      * subst x. left. reflexivity.
Qed.

Lemma receive_messages_not_v
  (s : vstate FreeX)
  (i i' : index)
  (Hv' : i' <> i)
  (ms : list message)
  : project (last (map destination (receive_messages s i (rev ms))) s) i' = project s i'.
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; try apply reflexivity.
  specialize (IHms s).
  rewrite rev_unit. simpl.
  destruct (in_dec eq_dec x (get_message_set (project s i))); try assumption.
  rewrite map_app. simpl.
  rewrite last_last.
  unfold receive_destination.
  unfold vtransition. simpl.
  destruct i as [v | client]; destruct i' as [v' | client']; simpl in *
  ;unfold vtransition; simpl
  ; destruct
    (@last
    (@_composite_state (State.message C V) (sum V clients)
       (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
    (@map
       (@transition_item (State.message C V)
          (@composite_type (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
       (@_composite_state (State.message C V) (sum V clients)
          (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
       (@destination (State.message C V)
          (@composite_type (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
       (receive_messages s (@inl V clients v) (@rev message ms))) s
    (@inl V clients v)
    ) as (msgs, final) eqn:Ht
  ||
  remember
    (@last
    (@_composite_state (State.message C V) (sum V clients)
       (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
    (@map
       (@transition_item (State.message C V)
          (@composite_type (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
       (@_composite_state (State.message C V) (sum V clients)
          (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
       (@destination (State.message C V)
          (@composite_type (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
       (receive_messages s (@inr V clients client) (@rev message ms))) s
    (@inr V clients client)
    ) as msgs eqn:Ht
  ; simpl
  ; rewrite state_update_neq; assumption
  .
Qed.

Lemma receive_messages_state_union_all
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  : incl ms (state_union (last (map destination (receive_messages s i (rev ms))) s)).
Proof.
  intros m Hm.
  specialize (receive_messages_v s i ms).
  intros [_ Hincl].
  assert (Hm' : In m (set_union eq_dec (get_message_set (project s i)) ms))
   by (apply set_union_iff; right; assumption).
  apply Hincl in Hm'.
  apply state_union_iff.
  destruct i as [v | client].
  - left. exists v. assumption.
  - right. exists client. assumption.
Qed.

Lemma receive_messages_protocol
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  (i : index)
  (ms : list message)
  (Hms : NoDup ms)
  (Hmsj : preceeds_closed message_preceeds_fn ms)
  (Hmsi : incl ms (state_union s))
  (Hmst : topologically_sorted message_preceeds_fn ms)
  : finite_protocol_trace_from Full_constrained_composition s (receive_messages s i (rev ms)).
Proof.
  induction ms using rev_ind.
  - constructor. assumption.
  - assert (Hmsi' : incl ms (state_union s)).
    { intros m Hm. apply Hmsi. apply in_app_iff. left. assumption. }
    assert (Hmsb : Forall (byzantine_message_prop FreeX) (ms ++ [x])).
    { apply incl_Forall with (state_union s); try assumption.
      apply state_union_free_byzantine_message.
      assumption.
    }
    assert (Hmsj' : preceeds_closed message_preceeds_fn ms).
    { apply topologically_sorted_preceeds_closed_remove_last
        with (byzantine_message_prop FreeX) (ms ++ [x]) x
      ; try assumption; try reflexivity.
      apply free_full_byzantine_message_preceeds_stict_order.
    }
    assert (Hmst' : topologically_sorted message_preceeds_fn ms ).
    { apply toplogically_sorted_remove_last with (ms ++ [x]) x; try assumption.
      reflexivity.
    }
    apply NoDup_remove in Hms.
    destruct Hms as [Hms Hnx].
    rewrite app_nil_r in *.
    specialize (IHms Hms Hmsj' Hmsi' Hmst').
    rewrite rev_unit. simpl.
    destruct (in_dec eq_dec x (get_message_set (project s i))); try assumption.
    apply (extend_right_finite_trace_from Full_constrained_composition); try assumption.
    repeat split.
    + apply finite_ptrace_last_pstate. assumption.
    + specialize (state_union_protocol_message s Hs).
      intro Hx.
      rewrite Forall_forall in Hx.
      assert (Hxs : In x (state_union s)).
      { apply Hmsi. apply in_app_iff. right; left; reflexivity. }
      specialize (Hx x Hxs).
      assumption.
    + assert (Hx : In x (ms ++ [x])).
        { apply in_app_iff. right. left. reflexivity. }
      simpl. destruct i as [v | client]; simpl; repeat split
      ; try
        (intro Hx'
        ; apply (proj1 (receive_messages_v s (inl v) ms))in Hx'
        || apply (proj1 (receive_messages_v s (inr client) ms))in Hx'
        ; apply set_union_iff in Hx'
        ; destruct Hx'; try (elim Hnx; assumption)
        ; elim n
        ; assumption
        )
      ; try
        (intros m Hm
        ; apply (receive_messages_v s (inl v))
        ||
        apply (receive_messages_v s (inr client))
        ; apply set_union_iff; right
        ; unfold preceeds_closed in Hmsj
        ; rewrite Forall_forall in Hmsj
        ; specialize (Hmsj x Hx m)
        ; destruct x as (c, v', j)
        ; unfold message_preceeds_fn in Hmsj; simpl in Hmsj
        ; unfold validator_message_preceeds_fn in Hmsj; simpl in Hmsj
        ; simpl in Hm; apply in_correct in Hm
        ; specialize (Hmsj Hm)
        ; apply in_app_iff in Hmsj
        ; destruct Hmsj as [Hmsj | [Heqm | Hn]]
        ; try inversion Hn
        ; try assumption
        ; subst m
        ; rewrite Forall_forall in Hmsb; specialize (Hmsb ((c, v', j)) Hx)
        ; specialize
          (free_full_byzantine_message_preceeds_irreflexive
          (exist _ ((c, v', j)) Hmsb)
          )
        ; intro Hc; elim Hc
        ; unfold free_full_byzantine_message_preceeds; simpl
        ; unfold validator_message_preceeds
        ; unfold validator_message_preceeds_fn
        ; unfold unmake_justification
        ; assumption
        ).
      * pose (Full_composition_constraint_state_not_heavy s Hs) as Hsnh.
        apply not_heavy_incl with (state_union s); try assumption.
        specialize (receive_messages_set_eq s (inr client) (ms ++ [x]) Hmsi).
        intros [_ Hincl].
        simpl in Hincl. rewrite rev_unit in Hincl. simpl in Hincl.
        destruct (in_dec eq_dec x (s (inr client))); try (elim n; assumption).
        rewrite map_app in Hincl. simpl in Hincl.
        rewrite last_last in Hincl.
        unfold receive_destination in Hincl.
        unfold vtransition in Hincl. simpl in Hincl.
        unfold vtransition in Hincl. simpl in Hincl.
        remember
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inr V clients client) (@rev message ms))) s
          (@inr V clients client))
          as msgs eqn:Hmsgs.
        replace
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inr V clients client) (@rev message ms))) s
          (@inr V clients client))
          with msgs.
        simpl in *.
        intros m Hm. apply Hincl.
        apply state_union_iff. right. exists client.
        rewrite state_update_eq.
        assumption.
    + unfold Full_composition_constraint.
      unfold vtransition. simpl.
      pose (Full_composition_constraint_state_not_heavy s Hs) as Hsnh.
      specialize (receive_messages_set_eq s i (ms ++ [x]) Hmsi).
      intros [_ Hincl].
      simpl in Hincl. rewrite rev_unit in Hincl. simpl in Hincl.
      destruct (in_dec eq_dec x (get_message_set (project s i)))
      ; try (elim n; assumption).
      rewrite map_app in Hincl. simpl in Hincl.
      rewrite last_last in Hincl.
      unfold receive_destination in Hincl.
      unfold vtransition in Hincl. simpl in Hincl.
      destruct i as [v | client]
      ; unfold vtransition; simpl
      ; destruct
        (@last
        (@_composite_state (State.message C V) (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
        (@map
           (@transition_item message
              (@composite_type (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
           (@_composite_state (State.message C V) (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
           (@destination message
              (@composite_type (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
           (receive_messages s (@inl V clients v) (@rev message ms))) s
        (@inl V clients v))
        as (msgs, final) eqn:Hmsgs
      || remember
        (@last
        (@_composite_state (State.message C V) (sum V clients)
           (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
        (@map
           (@transition_item message
              (@composite_type (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
           (@_composite_state (State.message C V) (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
           (@destination message
              (@composite_type (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
           (receive_messages s (@inr V clients client) (@rev message ms))) s
        (@inr V clients client))
        as msgs eqn:Hmsgs
      ; apply not_heavy_incl with s; try assumption
      ; unfold vtransition in Hincl; simpl in Hincl
      .
      * replace
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inl V clients v) (@rev message ms))) s
          (@inl V clients v))
          with (msgs, final) in Hincl.
        simpl in Hincl.
        assumption.
      * replace
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inr V clients client) (@rev message ms))) s
          (@inr V clients client))
          with msgs in Hincl.
        simpl in Hincl.
        assumption.
    + unfold receive_destination.
      unfold vtransition. simpl.
      destruct i as [v | client]
      ; unfold vtransition; simpl.
      * destruct
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inl V clients v) (@rev message ms))) s
          (@inl V clients v))
          as (msgs, final) eqn:Hmsgs.
        replace
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inl V clients v) (@rev message ms))) s
          (@inl V clients v))
          with (msgs, final).
        reflexivity.
      * remember
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination message
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inr V clients client) (@rev message ms))) s
          (@inr V clients client))
          as msgs eqn:Hmsgs.
        replace
          (@last
          (@_composite_state (State.message C V) (sum V clients)
             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
          (@map
             (@transition_item (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (@_composite_state (State.message C V) (sum V clients)
                (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
             (@destination (State.message C V)
                (@composite_type (State.message C V) (sum V clients)
                   (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
             (receive_messages s (@inr V clients client) (@rev message ms))) s
          (@inr V clients client))
          with msgs.
        reflexivity.
Qed.

Fixpoint receive_messages_iterated
  (s : vstate FreeX)
  (ms : list message)
  (is : list index)
  : list (vtransition_item FreeX)
  :=
  match is with
  | [] => []
  | i :: is' =>
    let items := receive_messages s i (rev ms) in
    let s' := last (List.map destination items) s in
    let items' := receive_messages_iterated s' ms is' in
    items ++ items'
  end.

Lemma receive_messages_iterated_out
  (s : vstate FreeX)
  (ms : list message)
  (is : list index)
  (i : index)
  (Hi : ~In i is)
  : project (last (map destination (receive_messages_iterated s ms is)) s) i = project s i.
Proof.
  generalize dependent s.
  induction is; intros; simpl; try reflexivity.
  rewrite map_app. rewrite last_app.
  assert (Hi' : ~In i is) by (intro; elim Hi; right; assumption).
  specialize (IHis Hi'). rewrite IHis.
  apply receive_messages_not_v.
  intro. subst a. elim Hi. left. reflexivity.
Qed.

Lemma receive_messages_iterated_in
  (s : vstate FreeX)
  (ms : list message)
  (is : list index)
  (i : index)
  (Hi : In i is)
  : set_eq
    (get_message_set (project (last (map destination (receive_messages_iterated s ms is)) s) i))
    (set_union eq_dec (get_message_set (project s i)) ms).
Proof.
  generalize dependent s.
  induction is; intros; simpl; inversion Hi
  ; rewrite map_app; rewrite last_app.
  - subst a.
    destruct (in_dec eq_dec i is).
    + specialize (IHis i0 (last (map destination (receive_messages s i (rev ms))) s)).
      apply set_eq_tran with (get_message_set (project (last (map destination (receive_messages s i (rev ms))) s) i))
      ; try apply receive_messages_v.
      destruct IHis as [Hincl Hincl'].
      split; intros m Hm.
      * apply Hincl in Hm.
        apply receive_messages_v.
        apply set_union_iff in Hm. apply set_union_iff.
        destruct Hm as [Hm | Hm]; try (right; assumption).
        apply receive_messages_v in Hm.
        apply set_union_iff in Hm.
        assumption.
      * apply Hincl'. apply receive_messages_v in Hm.
        apply set_union_iff in Hm. apply set_union_iff.
        destruct Hm as [Hm | Hm]; try (right; assumption).
        left.
        apply receive_messages_v.
        apply set_union_iff.
        left. assumption.
    + clear IHis.
      specialize (receive_messages_iterated_out (last (map destination (receive_messages s i (rev ms))) s) ms is i n).
      intro Heq.
      apply set_eq_tran with (get_message_set (project (last (map destination (receive_messages s i (rev ms))) s) i))
      ; try apply receive_messages_v.
      replace
        (@project C V about_C about_V Hmeasurable Hrt Hestimator
        (@last
           (@_composite_state (State.message C V) (sum V clients)
              (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
           (@map (@vtransition_item (State.message C V) FreeX)
              (@_composite_state (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
              (@destination (State.message C V)
                 (@composite_type (State.message C V) (sum V clients)
                    (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
              (receive_messages_iterated
                 (@last
                    (@_composite_state (State.message C V) (sum V clients)
                       (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
                    (@map
                       (@transition_item (State.message C V)
                          (@composite_type (State.message C V) (sum V clients)
                             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
                       (@_composite_state (State.message C V) (sum V clients)
                          (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
                       (@destination (State.message C V)
                          (@composite_type (State.message C V) (sum V clients)
                             (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
                       (receive_messages s i (@rev message ms))) s) ms is))
           (@last
              (@_composite_state (State.message C V) (sum V clients)
                 (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
              (@map (@vtransition_item (State.message C V) FreeX)
                 (@_composite_state (State.message C V) (sum V clients)
                    (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator))
                 (@destination (State.message C V)
                    (@composite_type (State.message C V) (sum V clients)
                       (@IM_index C V about_C about_V Hmeasurable Hrt Hestimator)))
                 (receive_messages s i (@rev message ms))) s)) i)
      with
        (project (last (map destination (receive_messages s i (rev ms))) s) i).
      apply set_eq_refl.
  - destruct (eq_dec i a).
    + subst a.
      specialize (IHis H (last (map destination (receive_messages s i (rev ms))) s)).
      apply set_eq_tran with (get_message_set (project (last (map destination (receive_messages s i (rev ms))) s) i))
      ; try apply receive_messages_v.
      destruct IHis as [Hincl Hincl'].
      split; intros m Hm.
      * apply Hincl in Hm.
        apply receive_messages_v.
        apply set_union_iff in Hm. apply set_union_iff.
        destruct Hm as [Hm | Hm]; try (right; assumption).
        apply receive_messages_v in Hm.
        apply set_union_iff in Hm.
        assumption.
      * apply Hincl'. apply receive_messages_v in Hm.
        apply set_union_iff in Hm. apply set_union_iff.
        destruct Hm as [Hm | Hm]; try (right; assumption).
        left.
        apply receive_messages_v.
        apply set_union_iff.
        left. assumption.
    + specialize (receive_messages_not_v s a i n ms).
      intro Heq.
      specialize (IHis H (last (map destination (receive_messages s a (rev ms))) s)).
      rewrite Heq in IHis.
      assumption.
Qed.

Lemma state_union_justification_closed
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : preceeds_closed message_preceeds_fn (state_union s).
Proof.
  unfold preceeds_closed.
  rewrite Forall_forall.
  intros m Hm mj Hmj.
  apply state_union_iff.
  apply state_union_iff in Hm.
  assert (Hs' : protocol_state_prop (pre_loaded_vlsm FreeX) s).
  { destruct Hs as [_om Hs]. exists _om.
    apply (pre_loaded_protocol_prop FreeX).
    apply constraint_free_protocol_prop with Full_composition_constraint.
    assumption.
  }
  unfold message_preceeds_fn in Hmj. simpl in Hmj.
  unfold validator_message_preceeds_fn in Hmj. simpl in Hmj.
  destruct m as (cm, vm, jm).
  specialize (in_correct (unmake_message_set (justification_message_set jm)) mj); intro Hin.
  apply Hin in Hmj.
  pose (in_free_byzantine_state_justification s Hs' ((cm, vm, jm))) as Hinm.
  destruct Hm as [[v Hm] | [client Hm]].
  - specialize (Hinm (inl v) Hm mj Hmj). left. exists v. assumption.
  - specialize (Hinm (inr client) Hm mj Hmj). right. exists client. assumption.
Qed.

Lemma receive_sorted_messages_protocol
  (is : list index)
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  (ms : set message)
  (Hnodup : NoDup ms)
  (Hms : topological_sorting message_preceeds_fn (state_union s) ms)
  (tr := receive_messages_iterated s ms is)
  : finite_protocol_trace_from Full_constrained_composition s tr.
Proof.
  assert (Hmsj : preceeds_closed message_preceeds_fn ms).
  { destruct Hms as [Hmseq _].
    apply preceeds_closed_set_eq with (state_union s).
    - apply set_eq_comm. assumption.
    - apply state_union_justification_closed. assumption.
  }
  assert (Hmsi : incl ms (state_union s)).
  { destruct Hms as [[_ Hincl] _]. assumption. }
  assert (Hmst : topologically_sorted message_preceeds_fn ms).
  { destruct Hms as [_ Hts]. assumption. }
  clear Hms.
  generalize dependent s.
  induction is; intros.
  - constructor. assumption.
  - unfold tr; clear tr. simpl.
    apply (finite_protocol_trace_from_app_iff Full_constrained_composition).
    specialize (receive_messages_protocol s Hs a ms Hnodup Hmsj Hmsi Hmst).
    intro Hms.
    split; try assumption.
    apply IHis.
    + apply finite_ptrace_last_pstate in Hms. assumption.
    + apply receive_messages_state_union_all.
Qed.

Definition union_state
  (s : vstate FreeX)
  : vstate FreeX
  :=
  let msgs := sorted_state_union s in
  let tr := receive_messages_iterated s msgs indices in
  last (map destination tr) s.

Lemma union_state_state_union
  (s : vstate FreeX)
  : Forall (fun i : index => set_eq (get_message_set (project (union_state s) i)) (state_union s)) indices.
Proof.
  rewrite Forall_forall. intros i Hi.
  unfold union_state.
  specialize (receive_messages_iterated_in s (sorted_state_union s) indices i Hi).
  intros Heq.
  specialize (top_sort_set_eq message_preceeds_fn (state_union s)).
  intro Heq'.
  apply set_eq_tran with (set_union eq_dec (get_message_set (project s i)) (sorted_state_union s))
  ; try assumption.
  split; intros m Hm.
  - apply set_union_iff in Hm.
    destruct Hm as [Hm | Hm].
    + apply state_union_iff.
      destruct i as [v | client].
      * left. exists v. assumption.
      * right. exists client. assumption.
    + apply Heq'. assumption.
  - apply set_union_iff.
    right. apply Heq'. assumption.
Qed.

Lemma common_future_state
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : exists s', in_futures Full_constrained_composition s s'
    /\ forall i i' : index, set_eq (get_message_set (project s' i)) (get_message_set (project s' i')).
Proof.
  exists (union_state s).
  split.
  - exists (receive_messages_iterated s (sorted_state_union s) indices).
    split; try reflexivity.
    apply receive_sorted_messages_protocol; try assumption.
    + apply sorted_state_union_nodup.
      destruct Hs as [om Hs].
      exists om. apply (pre_loaded_protocol_prop FreeX).
      apply constraint_free_protocol_prop in Hs.
      assumption.
    + specialize
        (@top_sort_correct _ _
          message_preceeds_fn
          (byzantine_message_prop FreeX)).
      intro H.
      apply H.
      * apply free_full_byzantine_message_preceeds_stict_order.
      * apply state_union_free_byzantine_message. assumption.
  - intros i i'.
    specialize (union_state_state_union s).
    rewrite Forall_forall.
    intro Heq.
    assert (Hi := proj2 finite_index i).
    assert (Hi' := proj2 finite_index i').
    apply Heq in Hi.
    apply Heq in Hi'.
    apply set_eq_tran with (state_union s); try assumption.
    apply set_eq_comm. assumption.
Qed.

End ConstrainedValidators.