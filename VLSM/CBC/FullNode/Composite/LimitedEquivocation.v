From Coq Require Import FinFun List ListSet RelationClasses.
Import ListNotations.

From CasperCBC
  Require Import
    Preamble
    ListExtras
    ListSetExtras
    Lib.Measurable
    TopSort
    VLSM.Equivocation
    VLSM.Decisions
    VLSM.Common
    VLSM.Composition
    VLSM.CBC.FullNode.Validator.State
    VLSM.CBC.FullNode.Validator.Equivocation
    VLSM.CBC.FullNode.Validator
    VLSM.CBC.FullNode.Client
    VLSM.CBC.FullNode.Composite.Free
    ObservableEquivocation
    .

Local Ltac destruct_match_term_as e pats Heq :=
  lazymatch e with
  | context [ match ?e with | _ => _ end] =>
    destruct_match_term_as e pats Heq
  | _ => destruct e as pats eqn:Heq
  end.
Local Ltac destruct_match_tac pats Heq :=
  lazymatch goal with
  | |- context [ match ?s with | _ => _ end] =>
    destruct_match_term_as s pats Heq
  end.
Local Ltac destruct_match_in_tac H pats Heq :=
  lazymatch type of H with
  | context [ match ?s with | _ => _ end] =>
    destruct_match_term_as s pats Heq
  end.
Local Tactic Notation "destruct_match" "as" simple_intropattern(pats)
  := destruct_match_tac pats ident:(Ht).
Local Tactic Notation "destruct_match" "as" simple_intropattern(pats) "eqn" ":" ident(Heq)
  := destruct_match_tac pats Heq.
Local Tactic Notation "destruct_match" "as" simple_intropattern(pats) "in" ident(H)
  := destruct_match_in_tac H pats ident:(Ht).
Local Tactic Notation "destruct_match" "as" simple_intropattern(pats) "eqn" ":" ident(Heq) "in" ident(H)
  := destruct_match_in_tac H pats Heq.

(** * VLSM Composing Validators with Limited Equivocation *)

Section ConstrainedValidators.

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (message := State.message C V)
    (clients : Type)
    {clients_eq_dec : EqDecision clients}
    (index : Type := (V + clients)%type)
    {i0 : Inhabited index}
    (indices : list index)
    (finite_index : Listing indices)
    (FreeX := @VLSM_full_composed_free C V about_C about_V Hmeasurable Hrt Hestimator clients _ _)
    (free_equivocation_evidence := @composed_equivocation_evidence
      C V about_C about_V Hmeasurable Hrt Hestimator clients indices)
    (free_basic_equivocation := @composed_basic_observable_equivocation
      C V about_C about_V Hmeasurable Hrt Hestimator clients _ _ indices finite_index)
    .

Existing Instance free_equivocation_evidence.
Existing Instance free_basic_equivocation.

Let v_eq_dec := @strictly_comparable_eq_dec _ about_V.
Existing Instance v_eq_dec.
Existing Instance index_eq_dec.

(*
Parameter (Hno_clients : clients -> False).
Definition v0 : V.
Proof.
  destruct (@i0 V).
  - exact v.
  - elim Hno_clients. exact c.
Defined.
*)

Definition Full_composition_constraint
  (l : vlabel FreeX)
  (som : vstate FreeX * option message)
  : Prop
  :=
  let (s', om') := vtransition FreeX l som in
  not_heavy s'.

Definition Full_constrained_composition : VLSM message
  := composite_vlsm IM_index Full_composition_constraint.

Existing Instance observable_messages.

Lemma Full_composition_constraint_state_not_heavy
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : not_heavy s.
Proof.
  specialize
    (@initial_state_not_heavy message V message _
      _ (validator_message_preceeds_dec C V)
      full_node_message_subject_of_observation
      _ _ _
      finite_index IM_index free_observable_messages_index _
      free_composite_vlsm_observable_messaged_index
      free_observation_based_equivocation_evidence_index
      _ Full_composition_constraint _ _ _ (composite_validators_nodup indices))
    as Hinitial_not_heavy.
  destruct Hs as [_om Hs].
  inversion Hs; subst; simpl.
  - apply Hinitial_not_heavy.
    assumption.
  - destruct Hv as [Hv Hctr].
    unfold Full_composition_constraint in Hctr.
    unfold vtransition in Hctr.
    simpl in Hctr.
    destruct l as (i, li).
    match type of Hctr with
      let (_,_) := (let (_,_) := ?Vtransition in _) in _ =>
      match type of H0 with
        (let (_,_) := ?Vtransition in _) = _ =>
        destruct Vtransition as (si',om')
      end
    end.
    inversion H0; subst.
    assumption.
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
  - specialize (Hs i).
    destruct i; inversion Hs; simpl in Hm
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
      destruct (decide (i = inl v')); destruct i as [v | client]; subst.
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
        { destruct (decide (i = inl v')); destruct i as [v | client]; subst.
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
        { destruct (decide (i = inr client')); destruct i as [v | client]; subst.
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
  : Forall (protocol_message_prop Full_constrained_composition)
           (state_union indices s).
Proof.
  apply Forall_forall.
  intros m Hm.
  apply state_union_iff in Hm;[..|exact finite_index].
  destruct Hm as [[v Hm] | [client Hm]].
  - apply in_protocol_state with s (inl v); assumption.
  - apply in_protocol_state with s (inr client); assumption.
Qed.

Lemma state_union_byzantine_message
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : Forall (byzantine_message_prop Full_constrained_composition) (state_union indices s).
Proof.
  apply state_union_protocol_message in Hs.
  rewrite Forall_forall in *.
  intros m Hm.
  specialize (Hs m Hm). clear -Hs.
  apply can_emit_protocol_iff in Hs.
  apply pre_loaded_with_all_messages_can_emit.
  destruct Hs as [[v [[miv Hmiv] Hs]] | Hem]; try assumption.
  destruct v; inversion Hmiv.
Qed.

Lemma state_union_free_byzantine_message
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : Forall (byzantine_message_prop FreeX) (state_union indices s).
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

Context
  (message_preceeds := validator_message_preceeds C V)
  (message_preceeds_dec := validator_message_preceeds_dec C V).

Existing Instance message_preceeds_dec.

Definition sorted_state_union
  (s : vstate FreeX)
  : set message
  :=
  top_sort message_preceeds (state_union indices s).

Lemma sorted_state_union_nodup
  (s : vstate FreeX)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm FreeX) s)
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
    match in_dec decide_eq m (get_message_set (project s i)) with
    | left _ => items
    | right _ =>
      let final := finite_trace_last s items in
      let item := receive_message final i m in
      items ++ [item]
    end
  end.

Lemma receive_messages_set_eq
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  (Hms : incl ms (state_union indices s))
  : set_eq (state_union indices s) (state_union indices (finite_trace_last s (receive_messages s i (rev ms)))).
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; simpl; try apply set_eq_refl.
  assert (Hi : incl ms (state_union indices s)).
  { intros m Hm. apply Hms. apply in_app_iff. left. assumption. }
  specialize (IHms s Hi).
  rewrite rev_unit. simpl.
  destruct (in_dec decide_eq x (get_message_set (project s i))); try assumption.
  rewrite finite_trace_last_is_last.
  simpl.
  unfold receive_destination.  unfold vtransition. simpl.
  unfold vtransition. simpl.
  destruct IHms as [I1 I2].
  split; intros m Hm; destruct i as [v | client]; simpl in *.
  - destruct_match as [msgs final].
    apply state_union_iff;[exact finite_index|..].
    apply I1 in Hm.
    apply state_union_iff in Hm;[..|exact finite_index].
    destruct Hm as [[v' Hm] | [client' Hm]];[destruct (decide_eq (inl v':index) (inl v))|].
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
  - match goal with
      |- context [@finite_trace_last _ ?T s ?l (inr client)] =>
      remember (@finite_trace_last _ T s l (inr client)) as msgs eqn:Ht
    end.
    specialize (I1 m Hm).
    apply state_union_iff in I1;[|exact finite_index].
    apply state_union_iff;[exact finite_index|].
    destruct I1 as [[v' HI1] | [client' HI1]];[|destruct (decide ((inr client':index) = inr client))].
    + simpl. left. exists v'.  rewrite state_update_neq by (intro; discriminate).
      assumption.
    + inversion e. subst client'. right. exists client.
      simpl. rewrite state_update_eq.
      apply set_add_iff. right.
      subst msgs. assumption.
    + right. exists client'. simpl. rewrite state_update_neq; assumption.
  - destruct_match as [msgs final] in Hm.
    apply state_union_iff in Hm;[|exact finite_index].
    destruct Hm as [[v' Hm] | [client' Hm]]; try destruct (decide ((inl v':index) = inl v)).
    + inversion e. subst v'. simpl in Hm. rewrite state_update_eq in Hm.
      apply set_add_iff in Hm.
      destruct Hm as [Heq | Hm].
      * subst m. apply Hms. apply in_app_iff. right. left. reflexivity.
      * apply I2. apply state_union_iff;[exact finite_index|].
        left. exists v.
        replace msgs with (get_message_set (msgs, final)) in Hm by reflexivity.
        rewrite <- Ht in Hm.
        assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by assumption.
      apply I2. apply state_union_iff;[exact finite_index|].
      left. exists v'.
      assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by (intro; discriminate).
      apply I2. apply state_union_iff;[exact finite_index|].
      right. exists client'.
      assumption.
  - match type of Hm with
      context [@finite_trace_last _ ?T s ?l (inr client)] =>
      remember (@finite_trace_last _ T s l (inr client)) as msgs eqn:Ht
    end.
    apply state_union_iff in Hm;[|exact finite_index].
    destruct Hm as [[v' Hm] | [client' Hm]]; try destruct (decide ((inr client':index) = inr client)).
    + simpl in Hm. rewrite state_update_neq in Hm by (intro; discriminate).
      apply I2. apply state_union_iff;[exact finite_index|].
      left. exists v'.
      assumption.
    + inversion e. subst client'. simpl in Hm. rewrite state_update_eq in Hm.
      apply set_add_iff in Hm.
      destruct Hm as [Heq | Hm].
      * subst m. apply Hms. apply in_app_iff. right. left. reflexivity.
      * apply I2. apply state_union_iff;[exact finite_index|].
        right. exists client.
        subst msgs. assumption.
    + simpl in Hm. rewrite state_update_neq in Hm by assumption.
      apply I2. apply state_union_iff;[exact finite_index|].
      right. exists client'.
      assumption.
Qed.

Lemma receive_messages_v
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  : set_eq (get_message_set (project (finite_trace_last s (receive_messages s i (rev ms))) i)) (set_union decide_eq (get_message_set (project s i)) ms).
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; try apply set_eq_refl.
  rewrite rev_unit. simpl.
  destruct (in_dec decide_eq x (get_message_set (project s i))).
  { specialize (IHms s).
    apply set_eq_tran with (set_union decide_eq (get_message_set (project s i)) ms)
    ; try assumption.
    split; intros m Hm; apply set_union_iff; apply set_union_iff in Hm
    ; destruct Hm as [Hm | Hm]; try (left; assumption); try (right; assumption).
    - right. apply in_app_iff. left. assumption.
    - apply in_app_iff in Hm. destruct Hm as [Hm | Hm]; try (right; assumption).
      left. inversion Hm; try contradiction. subst. assumption.
  }
  rewrite finite_trace_last_is_last.
  simpl.
  split; intros m Hm.
  - apply set_union_iff.
    unfold receive_destination in Hm.
    unfold vtransition in Hm. simpl in Hm.
    destruct i as [v | client]; simpl in *
    ; unfold vtransition in Hm; simpl in Hm.
    + destruct_match as (msgs, final) eqn: Heqlst in Hm.
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
    + match type of Hm with
        context [@finite_trace_last _ ?T s ?l (inr client)] =>
        remember (@finite_trace_last _ T s l (inr client)) as msgs eqn:Heqlst
      end.
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
    + destruct_match as (msgs, final) eqn:Heqlst.
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
    + match goal with
        |- context [@finite_trace_last _ ?T s ?l (inr client)] =>
        remember (@finite_trace_last _ T s l (inr client)) as msgs eqn:Heqlst
      end.
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
  : project (finite_trace_last s (receive_messages s i (rev ms))) i' = project s i'.
Proof.
  generalize dependent s.
  induction ms using rev_ind; intros; try apply reflexivity.
  specialize (IHms s).
  rewrite rev_unit. simpl.
  destruct (in_dec decide_eq x (get_message_set (project s i))); try assumption.
  rewrite finite_trace_last_is_last.
  simpl.
  unfold receive_destination.
  unfold vtransition. simpl.
  destruct i as [v | client]; destruct i' as [v' | client']; simpl in *
  ;unfold vtransition; simpl;
    match goal with
      |- context[@finite_trace_last _ ?T s ?l ?ix] =>
      match ix with
      | (inl _) => destruct (@finite_trace_last _ T s l ix) as (msgs, final) eqn:Ht
      | (inr _) => remember (@finite_trace_last _ T s l ix) as msgs eqn:Ht
      end
    end
  ; simpl
  ; rewrite state_update_neq; assumption
  .
Qed.

Lemma receive_messages_state_union_all
  (s : vstate FreeX)
  (i : index)
  (ms : list message)
  : incl ms (state_union indices (finite_trace_last s (receive_messages s i (rev ms)))).
Proof.
  intros m Hm.
  specialize (receive_messages_v s i ms).
  intros [_ Hincl].
  assert (Hm' : In m (set_union decide_eq (get_message_set (project s i)) ms))
   by (apply set_union_iff; right; assumption).
  apply Hincl in Hm'.
  apply state_union_iff;[exact finite_index|].
  destruct i as [v | client].
  - left. exists v. assumption.
  - right. exists client. assumption.
Qed.

Instance StrictOrder_preceeds_message_preceeds:
  StrictOrder (preceeds_P message_preceeds (byzantine_message_prop FreeX))
  := free_full_byzantine_message_preceeds_stict_order.

Lemma preceeds_closed_contains_justification
  (x m : message)
  (ms : list message)
  (Hm : In m (get_message_set (unmake_justification (get_justification x))))
  (Hmsj : preceeds_closed message_preceeds (ms ++ [x])):
  In m (ms ++ [x]).
Proof.
  clear -Hmsj Hm.
  unfold preceeds_closed in Hmsj.
  rewrite Forall_forall in Hmsj.
  apply (Hmsj x);clear Hmsj.
  { apply in_app_iff;right;left;reflexivity. }
  unfold message_preceeds, validator_message_preceeds;simpl.
  rewrite Is_true_iff_eq_true.
  destruct x;simpl.
  rewrite <- in_correct_refl.
  assumption.
Qed.

Lemma byzantine_message_prop_justification_excludes_self
  (x: message)
  (Hmsb : byzantine_message_prop FreeX x):
  ~In x (get_message_set (unmake_justification (get_justification x))).
Proof.
  clear -Hmsb.
  intro Hcycle.
  destruct
    (free_full_byzantine_message_preceeds_irreflexive
       (exist _ _ Hmsb)) as [].
  apply in_correct in Hcycle.
  destruct x.
  exact Hcycle.
Qed.

Lemma receive_messages_protocol
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  (i : index)
  (ms : list message)
  (Hms : NoDup ms)
  (Hmsj : preceeds_closed message_preceeds ms)
  (Hmsi : incl ms (state_union indices s))
  (Hmst : topologically_sorted message_preceeds ms)
  : finite_protocol_trace_from Full_constrained_composition s (receive_messages s i (rev ms)).
Proof.
  induction ms using rev_ind.
  - constructor. assumption.
  - assert (Hmsi' : incl ms (state_union indices s)).
    { intros m Hm. apply Hmsi. apply in_app_iff. left. assumption. }
    assert (Hmsb : Forall (byzantine_message_prop FreeX) (ms ++ [x])).
    { apply incl_Forall with (state_union indices s); try assumption.
      apply state_union_free_byzantine_message.
      assumption.
    }
    assert (Hmsj' : preceeds_closed message_preceeds ms).
    { apply topologically_sorted_preceeds_closed_remove_last
        with (byzantine_message_prop FreeX) (ms ++ [x]) x
      ; try assumption; try reflexivity.
      apply StrictOrder_preceeds_message_preceeds.
    }
    assert (Hmst' : topologically_sorted message_preceeds ms ).
    { apply toplogically_sorted_remove_last with (ms ++ [x]) x; try assumption.
      reflexivity.
    }
    apply NoDup_remove in Hms.
    destruct Hms as [Hms Hnx].
    rewrite app_nil_r in *.
    specialize (IHms Hms Hmsj' Hmsi' Hmst').
    rewrite rev_unit. simpl.
    destruct (in_dec decide_eq x (get_message_set (project s i))); try assumption.
    apply (extend_right_finite_trace_from Full_constrained_composition); try assumption.
    repeat split.
    + apply finite_ptrace_last_pstate. assumption.
    + specialize (state_union_protocol_message s Hs).
      intro Hx.
      rewrite Forall_forall in Hx.
      assert (Hxs : In x (state_union indices s)).
      { apply Hmsi. apply in_app_iff. right; left; reflexivity. }
      specialize (Hx x Hxs).
      assumption.
    + assert (Hx : In x (ms ++ [x])).
        { apply in_app_iff. right. left. reflexivity. }
        simpl.
        set (ix:=i).
        destruct i as [v | client]; simpl; repeat split;
        lazymatch goal with
        | |- ~ In _ ?L =>
          intro Hx';apply (receive_messages_v s ix), set_union_iff in Hx';
          clear -Hx' n Hnx;tauto
        | |- incl _ _ =>
          intros m Hm
          ; apply (receive_messages_v s ix), set_union_iff
          ; right
          ; apply (preceeds_closed_contains_justification x m _ Hm) in Hmsj
          ; apply in_app_iff in Hmsj
          ; destruct Hmsj as [Hmsj | [Heqm | []]];[assumption|subst m]
          ; exfalso
          ; rewrite Forall_forall in Hmsb; specialize (Hmsb _ Hx)
          ; apply byzantine_message_prop_justification_excludes_self in Hmsb
          ; exact (Hmsb Hm)
        | |- not_heavy _ => idtac
        end.
      unfold ix;clear ix.
      pose (Full_composition_constraint_state_not_heavy s Hs) as Hsnh.
      specialize (receive_messages_set_eq s (inr client) (ms ++ [x]) Hmsi).
      intros [_ Hincl].
      simpl in Hincl. rewrite rev_unit in Hincl. simpl in Hincl.
      destruct (in_dec decide_eq x (s (inr client))); try (elim n; assumption).
      rewrite finite_trace_last_is_last in Hincl.
      simpl in Hincl.
      unfold receive_destination in Hincl.
      unfold vtransition in Hincl. simpl in Hincl.
      match goal with
      | |- context [@finite_trace_last _ ?T s ?l] =>
        remember (@finite_trace_last _ T s l) as lst
      end.
      replace (finite_trace_last _ _) with lst.
      assert (Hincl' : incl (set_add decide_eq x (lst (inr client))) (state_union indices s)).
      {
        intros m Hm. apply Hincl.
        apply state_union_iff;[exact finite_index|]. right. exists client.
        rewrite state_update_eq. assumption.
      }
      apply not_heavy_incl with (state_union indices s); [assumption| ..].
      * apply set_map_incl. assumption.
      * intros m Hm.
        apply (proj1 (full_node_client_has_been_observed_iff _ m)) in Hm.
        apply (full_node_client_has_been_observed_iff _ m).
        apply Hincl'. assumption.
      * apply not_heavy_commute with finite_index. assumption.
    + unfold Full_composition_constraint.
      unfold vtransition. simpl.
      pose (Full_composition_constraint_state_not_heavy s Hs) as Hsnh.
      specialize (receive_messages_set_eq s i (ms ++ [x]) Hmsi).
      intros [_ Hincl].
      simpl in Hincl. rewrite rev_unit in Hincl. simpl in Hincl.
      destruct (in_dec decide_eq x (get_message_set (project s i)))
      ; [elim n; assumption|]. clear n0.
      rewrite finite_trace_last_is_last in Hincl.
      simpl in Hincl.
      unfold receive_destination in Hincl.
      unfold vtransition in Hincl. simpl in * |- *.
      Set Printing Implicit.
      match goal with
          |- context[@finite_trace_last ?msg ?T s ?l] =>
            remember (@finite_trace_last msg T s l) as lst eqn:Hlst
      end.
      destruct (receive_label lst i x) as (j, lj) eqn:Hrlabel.
      lazymatch goal with
          |- context[@finite_trace_last ?msg ?T s ?l j] =>
          replace (@finite_trace_last msg T s l) with lst by assumption
      end.
      match type of Hincl with
      | context [let (si', om') := ?v in _] => destruct v as (si', om') eqn:Ht
      end.
      simpl in Hincl.
      apply not_heavy_incl with s; [assumption| | | assumption].
      * apply set_map_incl. assumption.
      * intros m Hm.
       specialize (composite_has_been_observed_state_union _ finite_index) as Hunion.
       apply Hunion. apply Hincl. apply Hunion. assumption.
    + unfold receive_destination.
      unfold vtransition. simpl.
      destruct i as [v | client]
      ; [|reflexivity].
      unfold vtransition. simpl.
      destruct_match as (msgs, final) eqn:Hmsgs.
      replace (finite_trace_last s _ (inl v)) with (msgs, final).
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
    let s' := finite_trace_last s items in
    let items' := receive_messages_iterated s' ms is' in
    items ++ items'
  end.

Lemma receive_messages_iterated_out
  (s : vstate FreeX)
  (ms : list message)
  (is : list index)
  (i : index)
  (Hi : ~In i is)
  : project (finite_trace_last s (receive_messages_iterated s ms is)) i = project s i.
Proof.
  generalize dependent s.
  induction is; intros; simpl; try reflexivity.
  rewrite finite_trace_last_app.
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
    (get_message_set (project (finite_trace_last s (receive_messages_iterated s ms is)) i))
    (set_union decide_eq (get_message_set (project s i)) ms).
Proof.
  generalize dependent s.
  induction is; intros; simpl; inversion Hi
  ; rewrite finite_trace_last_app.
  - subst a.
    destruct (in_dec decide_eq i is).
    + specialize (IHis i1 (finite_trace_last s (receive_messages s i (rev ms)))).
      apply set_eq_tran with (get_message_set (project (finite_trace_last s (receive_messages s i (rev ms))) i));[|solve[apply receive_messages_v]].
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
      specialize (receive_messages_iterated_out (finite_trace_last s (receive_messages s i (rev ms))) ms is i n).
      intro Heq.
      apply set_eq_tran with (get_message_set (project (finite_trace_last s (receive_messages s i (rev ms))) i))
      ; try apply receive_messages_v.
      replace (project _ i)
      with (project (finite_trace_last s (receive_messages s i (rev ms))) i).
      apply set_eq_refl.
  - destruct (decide (i = a)).
    + subst a.
      specialize (IHis H (finite_trace_last s (receive_messages s i (rev ms)))).
      apply set_eq_tran with (get_message_set (project (finite_trace_last s (receive_messages s i (rev ms))) i))
      ;[|solve[apply receive_messages_v]].
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
      specialize (IHis H (finite_trace_last s (receive_messages s a (rev ms)))).
      rewrite Heq in IHis.
      assumption.
Qed.

Lemma state_union_justification_closed
  (s : vstate FreeX)
  (Hs : protocol_state_prop Full_constrained_composition s)
  : preceeds_closed message_preceeds (state_union indices s).
Proof.
  unfold preceeds_closed.
  rewrite Forall_forall.
  intros m Hm mj Hmj.
  apply state_union_iff;[exact finite_index|].
  apply state_union_iff in Hm;[|exact finite_index].
  assert (Hs' : protocol_state_prop (pre_loaded_with_all_messages_vlsm FreeX) s).
  { destruct Hs as [_om Hs]. exists _om.
    apply (pre_loaded_with_all_messages_protocol_prop FreeX).
    apply constraint_free_protocol_prop with Full_composition_constraint.
    assumption.
  }
  unfold message_preceeds, validator_message_preceeds in Hmj.
  unfold validator_message_preceeds_fn in Hmj. simpl in Hmj.
  destruct m as (cm, vm, jm).
  specialize (in_correct (unmake_message_set (justification_message_set jm)) mj); intro Hin.
  apply Hin in Hmj.
  pose (in_free_byzantine_state_justification s Hs' (Msg cm vm jm)) as Hinm.
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
  (Hms : topological_sorting message_preceeds (state_union indices s) ms)
  (tr := receive_messages_iterated s ms is)
  : finite_protocol_trace_from Full_constrained_composition s tr.
Proof.
  assert (Hmsj : preceeds_closed message_preceeds ms).
  { destruct Hms as [Hmseq _].
    apply preceeds_closed_set_eq with (state_union indices s).
    - apply set_eq_comm. assumption.
    - apply state_union_justification_closed. assumption.
  }
  assert (Hmsi : incl ms (state_union indices s)).
  { destruct Hms as [[_ Hincl] _]. assumption. }
  assert (Hmst : topologically_sorted message_preceeds ms).
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
  finite_trace_last s tr.

Lemma union_state_state_union
  (s : vstate FreeX)
  : Forall (fun i : index => set_eq (get_message_set (project (union_state s) i)) (state_union indices s)) indices.
Proof.
  rewrite Forall_forall. intros i Hi.
  unfold union_state.
  specialize (receive_messages_iterated_in s (sorted_state_union s) indices i Hi).
  intros Heq.
  specialize (top_sort_set_eq message_preceeds (state_union indices s)).
  intro Heq'.
  apply set_eq_tran with (set_union decide_eq (get_message_set (project s i)) (sorted_state_union s))
  ; try assumption.
  split; intros m Hm.
  - apply set_union_iff in Hm.
    destruct Hm as [Hm | Hm].
    + apply state_union_iff;[exact finite_index|].
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
    apply ptrace_add_last;[|reflexivity].
    apply receive_sorted_messages_protocol; try assumption.
    + apply sorted_state_union_nodup.
      destruct Hs as [om Hs].
      exists om. apply (pre_loaded_with_all_messages_protocol_prop FreeX).
      apply constraint_free_protocol_prop in Hs.
      assumption.
    + specialize
        (@top_sort_correct _ _
          message_preceeds
          message_preceeds_dec (byzantine_message_prop FreeX)).
      intro H.
      apply H.
      * apply StrictOrder_preceeds_message_preceeds.
      * apply state_union_free_byzantine_message. assumption.
  - intros i i'.
    specialize (union_state_state_union s).
    rewrite Forall_forall.
    intro Heq.
    assert (Hi := proj2 finite_index i).
    assert (Hi' := proj2 finite_index i').
    apply Heq in Hi.
    apply Heq in Hi'.
    apply set_eq_tran with (state_union indices s); try assumption.
    apply set_eq_comm. assumption.
Qed.

End ConstrainedValidators.
