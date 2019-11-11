Require Import List.
Import ListNotations.

From Casper
Require Import vlsm two_vlsms list_of_vlsms indexed_vlsm.


Definition noneOrAll
  (op : option Prop)
  : Prop
  :=
  match op with
  | None => True
  | (Some p) => p
  end.


Class composed_vlsm_class (message : Type) `{VLSM message} :=
  { index : Set
  ; index_eq_dec : EqDec index

  ; iproto_state : index -> Type
  ; istate_proj : forall i : index, state -> iproto_state i

  ; ilabel : label -> index
  ; ilabel_type := fun (i : index) => { l : label | ilabel l = i }
  ; ilabel_type_inhabited : forall i : index, inhabited (ilabel_type i)

  ; iproto_message_prop : index -> message -> Prop
  ; iproto_message_decidable : forall i : index, forall m : message, {iproto_message_prop i m} + {~iproto_message_prop i m}
  ; iproto_message_inhabited : forall i : index, inhabited {m : message | iproto_message_prop i m}
  ; iproto_message_consistent : forall i : index, forall m : message, iproto_message_prop i m -> proto_message_prop m

  ; transition_projection_consistency
    : forall (s1 s2 : state) (om : option proto_message) (l : label) (i : index)
        (Hproj_s : istate_proj i s1 = istate_proj i s2)
        (Hli : ilabel l = i),
    (   snd (transition l (s1, om)) = snd (transition l (s2, om))
    /\  istate_proj i (fst (transition l (s1, om))) = istate_proj i (fst (transition l (s2, om)))
    )
  ; transition_projection_state_preservation
    : forall (s : state) (om : option proto_message) (l : label) (i : index)
        (Hnli : ilabel l <> i),
        (istate_proj i (fst (transition l (s, om))) = istate_proj i s
    )
  ; transition_projection_type_preservation
    : forall (s : state) (om : option proto_message) (l : label) (i : index)
        (Hli : ilabel l = i),
        noneOrAll (option_map (iproto_message_prop i) (option_map (@proj1_sig message proto_message_prop) (snd (transition l (s, om)))))
  }.

Definition istate
  { message : Type }
  `{composed_vlsm_class message}
  (i : index)
  :=
  { is : iproto_state i | exists s : state, istate_proj i s = is }.

Definition proj_istate
  { message : Type }
  `{composed_vlsm_class message}
  (s : state)
  (i : index)
  : istate i.
remember (istate_proj i s) as is.
assert (His : exists s', istate_proj i s' = is) by (exists s; subst; reflexivity).
exact (exist _ is His).
Defined.

Lemma proj_istate_eq
  { message : Type }
  `{composed_vlsm_class message}
  (s1 s2 : state)
  (i : index)
  : istate_proj i s1 = istate_proj i s2 <-> proj_istate s1 i = proj_istate s2 i.
Proof.
  unfold proj_istate.
  split; intros Heq.
  - apply exist_eq. simpl. assumption.
  - inversion Heq. reflexivity.
Qed.

Inductive composed2_index : Set := one | two.

Lemma composed2_index_eq_dec
  : EqDec composed2_index.
Proof.
  intros x y; destruct x; destruct y; try (left; reflexivity); right; intros C; inversion C.
Qed.

Definition composed2_iproto_state
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : Type
  :=
  match i with
  | one => @state message S1
  | two => @state message S2
  end.

Definition composed2_istate_proj
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  (s : (@state message S1) * (@state message S2))
  : composed2_iproto_state S1 S2 i
  :=
  match i with
  | one => fst s
  | two => snd s
  end.

Definition composed2_istate_proj'
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  (s : @state message (composed2_vlsm S1 S2))
  : composed2_iproto_state S1 S2 i
  :=
  composed2_istate_proj S1 S2 i s.

Definition composed2_ilabel
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (l : (@label message S1) + (@label message S2))
  : composed2_index
  :=
  match l with
  | inl _ => one
  | inr _ => two
  end.

Lemma composed2_ilabel_type_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : inhabited { l : @label message S1 + @label message S2 | composed2_ilabel S1 S2 l = i }.
Proof.
  specialize (@label_inhabited message S1); intros [l1].
  specialize (@label_inhabited message S2); intros [l2].
  constructor.
  destruct i.
  - exists (inl l1). reflexivity.
  - exists (inr l2). reflexivity.
Qed.

Definition composed2_iproto_message_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : message -> Prop
  :=
  match i with
  | one => @proto_message_prop message S1
  | two => @proto_message_prop message S2
  end.

Lemma composed2_iproto_message_decidable
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : forall m : message, {composed2_iproto_message_prop S1 S2 i m} + {~composed2_iproto_message_prop S1 S2 i m}.
Proof.
  unfold composed2_iproto_message_prop. destruct i; apply proto_message_decidable.
Qed.

Lemma composed2_iproto_message_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : inhabited {m : message | composed2_iproto_message_prop S1 S2 i m}.
Proof.
  unfold composed2_iproto_message_prop. destruct i; apply message_inhabited.
Qed.

Lemma composed2_iproto_message_consistent
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (i : composed2_index)
  : forall m : message, composed2_iproto_message_prop S1 S2 i m -> composed2_proto_message_prop S1 S2 m.
Proof.
  unfold composed2_iproto_message_prop; intros. destruct i; (left; assumption) || (right; assumption).
Qed.

Lemma composed2_transition_projection_consistency
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : forall
      (s1 s2 : @state message S1 * @state message S2)
      (om : option (composed2_proto_message S1 S2))
      (l : @label message S1 + @label message S2)
      (i : composed2_index)
      (Hproj_s : composed2_istate_proj S1 S2 i s1 = composed2_istate_proj S1 S2 i s2)
      (Hli : composed2_ilabel S1 S2 l = i),
    (   snd (composed2_transition S1 S2 l (s1, om)) = snd (composed2_transition S1 S2 l (s2, om))
    /\  composed2_istate_proj S1 S2 i (fst (composed2_transition S1 S2 l (s1, om)))
      = composed2_istate_proj S1 S2 i (fst (composed2_transition S1 S2 l (s2, om)))
    ).
Proof.
  intros.
  destruct s1 as [s1one s1two]. destruct s2 as [s2one s2two].
  destruct l as [lone | ltwo]; simpl in Hli; subst;  destruct om as [[m Hm]|]; simpl in *; subst; try (split; reflexivity);
  destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; split; reflexivity.
Qed.

Lemma composed2_transition_projection_state_preservation
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : forall
      (s : @state message S1 * @state message S2)
      (om : option (composed2_proto_message S1 S2))
      (l : @label message S1 + @label message S2)
      (i : composed2_index)
      (Hnli : composed2_ilabel S1 S2 l <> i),
        composed2_istate_proj S1 S2 i (fst (composed2_transition S1 S2 l (s, om))) = composed2_istate_proj S1 S2 i s
  .
Proof.
  intros.
  destruct s as [sone stwo].
  destruct i; destruct l as [lone | ltwo]; simpl in Hnli; try contradiction
  ; destruct om as [[m Hm]|]; try reflexivity
  ; simpl; destruct (proto_message_decidable m) as [Hpm | Hnpm]
  ; reflexivity.
Qed.

Lemma composed2_transition_projection_type_preservation
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : forall
      (s : @state message S1 * @state message S2)
      (om : option (composed2_proto_message S1 S2))
      (l : @label message S1 + @label message S2)
      (i : composed2_index)
      (Hli : composed2_ilabel S1 S2 l = i),
      noneOrAll
        (option_map (composed2_iproto_message_prop S1 S2 i)
          (option_map (@proj1_sig message (composed2_proto_message_prop S1 S2))
            (snd (composed2_transition S1 S2 l (s, om)))))
  .
Proof.
  intros.
  destruct s as [sone stwo]. destruct l as [lone | ltwo]; simpl in Hli; subst; destruct om as [[m Hm]|]; simpl in *; subst
  ; try (destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl); try exact I.
  - remember (transition lone (sone, Some (exist proto_message_prop m Hpm))) as t.
    destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
  - remember (transition lone (sone, None)) as t.
    destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
  - remember (transition ltwo (stwo, Some (exist proto_message_prop m Hpm))) as t.
    destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
  - remember (transition ltwo (stwo, None)) as t.
    destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
Qed.

Definition composed2_vlsm_composed_instance
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : @composed_vlsm_class message (composed2_vlsm S1 S2) :=
  {| index := composed2_index
  ; index_eq_dec := composed2_index_eq_dec
  ; iproto_state := composed2_iproto_state S1 S2
  ; istate_proj := composed2_istate_proj' S1 S2
  ; ilabel := composed2_ilabel S1 S2
  ; ilabel_type_inhabited := composed2_ilabel_type_inhabited S1 S2
  ; iproto_message_prop := composed2_iproto_message_prop S1 S2
  ; iproto_message_decidable := composed2_iproto_message_decidable S1 S2
  ; iproto_message_inhabited := composed2_iproto_message_inhabited S1 S2
  ; iproto_message_consistent := composed2_iproto_message_consistent S1 S2
  ; transition_projection_consistency := composed2_transition_projection_consistency S1 S2
  ; transition_projection_state_preservation := composed2_transition_projection_state_preservation S1 S2
  ; transition_projection_type_preservation := composed2_transition_projection_type_preservation S1 S2
  |}.

Definition composed2_constrained_istate_proj
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop)
  (i : composed2_index)
  (s : @state message (composed2_vlsm_constrained S1 S2 constraint))
  : composed2_iproto_state S1 S2 i
  :=
  composed2_istate_proj S1 S2 i s.


Definition composed2_vlsm_constrained_composed_instance
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop)
  : @composed_vlsm_class message (composed2_vlsm_constrained S1 S2 constraint) :=
  {| index := composed2_index
  ; index_eq_dec := composed2_index_eq_dec
  ; iproto_state := composed2_iproto_state S1 S2
  ; istate_proj := composed2_constrained_istate_proj S1 S2 constraint
  ; ilabel := composed2_ilabel S1 S2
  ; ilabel_type_inhabited := composed2_ilabel_type_inhabited S1 S2
  ; iproto_message_prop := composed2_iproto_message_prop S1 S2
  ; iproto_message_decidable := composed2_iproto_message_decidable S1 S2
  ; iproto_message_inhabited := composed2_iproto_message_inhabited S1 S2
  ; iproto_message_consistent := composed2_iproto_message_consistent S1 S2
  ; transition_projection_consistency := composed2_transition_projection_consistency S1 S2
  ; transition_projection_state_preservation := composed2_transition_projection_state_preservation S1 S2
  ; transition_projection_type_preservation := composed2_transition_projection_type_preservation S1 S2
  |}.

Definition composed_list_index
  {message}
  (Ss : list (VLSM message))
  :=
  { n : nat | n < length Ss }.

Lemma composed_list_index_eq_dec
  {message}
  (Ss : list (VLSM message))
 : EqDec (composed_list_index Ss).
Proof.
  apply DepEqDec. apply nat_eq_dec.
Qed.

Fixpoint composed_list_iproto_state
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : Type.
destruct i as [i Hi].
destruct Ss as [| Sh St]; simpl in Hi.
{ exfalso. inversion Hi. }
destruct i.
- exact (@state message Sh).
- apply le_pred in Hi; simpl in Hi.
  exact (composed_list_iproto_state message St (exist _ i Hi)).
Defined.

Fixpoint composed_list_istate_proj
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : composed_list_state Ss -> composed_list_iproto_state Ss i.
intros s.
destruct i as [i Hi]. 
destruct Ss as [| Sh St]; simpl in Hi; simpl.
{ exfalso. inversion Hi. }
destruct s as [sh st]; simpl.
destruct i.
- exact sh.
- remember (exist (fun n : nat => n < length St) i (le_pred (S (S i)) (S (length St)) Hi)) as i'.
  exact (composed_list_istate_proj message St i' st).
Defined.

Definition composed_list_istate_proj'
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  (i : composed_list_index Ss)
  (s : @state message (composed_list_vlsm Ss Ssnn))
  : composed_list_iproto_state Ss i
  := composed_list_istate_proj Ss i s.


Definition composed_list_ilabel
  {message}
  (Ss : list (VLSM message))
  (l : composed_list_label Ss)
  : composed_list_index Ss.
induction Ss; try contradiction.
destruct l as [lh | lt].
- assert (Hi : 0 < length (a :: Ss)) by (apply le_n_S; apply le_0_n).
  exact (exist _ 0 Hi).
- specialize (IHSs  lt).
  destruct IHSs as [i Hi]. apply  le_n_S in Hi.
  exact (exist _ (S i) Hi).
Defined.

Lemma composed_list_ilabel_type_inhabited
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : inhabited { l : composed_list_label Ss | composed_list_ilabel Ss l = i }.
Proof.
  induction Ss as [| Sh St IHSt]; destruct i as [i Hi].
  - exfalso. inversion Hi.
  - destruct i.
    + specialize (@label_inhabited message Sh); intros [lh].
      constructor. exists (inl lh). simpl. apply f_equal. apply proof_irrelevance.
    + simpl in Hi. specialize (IHSt (exist _ i (le_pred _ _ Hi))).
      destruct IHSt as [[lt Hlt]].
      constructor.
      exists (inr lt).
      simpl. rewrite Hlt. apply f_equal. apply proof_irrelevance.
Qed.

Fixpoint composed_list_iproto_message_prop
  {message}
  (Ss : list (VLSM message))
  : composed_list_index Ss -> message -> Prop.
intros [i Hi] m.
destruct Ss as [| Sh St].
- exfalso. inversion Hi.
- destruct i.
  + exact (@proto_message_prop message Sh m).
  + specialize (composed_list_iproto_message_prop message St).
    specialize (composed_list_iproto_message_prop (exist _ i (le_pred _ _ Hi))).
    exact (composed_list_iproto_message_prop m).
Defined.

Lemma composed_list_iproto_message_decidable
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : forall m : message, {composed_list_iproto_message_prop Ss i m} + {~composed_list_iproto_message_prop Ss i m}.
Proof.
  induction Ss; destruct i as [i Hi].
  - exfalso. inversion Hi.
  - destruct i; simpl; try apply proto_message_decidable.
    specialize (IHSs  (exist _ i (le_pred _ _ Hi))); simpl in IHSs.
    assumption.
Qed.

Lemma composed_list_iproto_message_inhabited
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : inhabited {m : message | composed_list_iproto_message_prop Ss i m}.
Proof.
  induction Ss; destruct i as [i Hi].
  - exfalso. inversion Hi.
  - destruct i; simpl; try apply message_inhabited.
    specialize (IHSs  (exist _ i (le_pred _ _ Hi))); simpl in IHSs.
    assumption.
Qed.

Lemma composed_list_iproto_message_consistent
  {message}
  (Ss : list (VLSM message))
  (i : composed_list_index Ss)
  : forall m : message, composed_list_iproto_message_prop Ss i m -> composed_list_proto_message_prop Ss m.
Proof.
  induction Ss; destruct i as [i Hi].
  - exfalso. inversion Hi.
  - destruct i; simpl; intros.
    + left. assumption.
    + right. specialize (IHSs (exist _ i (le_pred _ _ Hi)) m). simpl in IHSs.
      apply IHSs. assumption.
Qed.

Lemma composed_list_transition_projection_consistency
  {message}
  (Ss : list (VLSM message))
  : forall
      (s1 s2 : composed_list_state Ss)
      (om : option (composed_list_proto_message Ss))
      (l : composed_list_label Ss)
      (i : composed_list_index Ss)
      (Hproj_s : composed_list_istate_proj Ss i s1 = composed_list_istate_proj Ss i s2)
      (Hli : composed_list_ilabel Ss l = i),
    (   snd (composed_list_transition Ss l (s1, om)) = snd (composed_list_transition Ss l (s2, om))
    /\  composed_list_istate_proj Ss i (fst (composed_list_transition Ss l (s1, om)))
      = composed_list_istate_proj Ss i (fst (composed_list_transition Ss l (s2, om)))
    ).
Proof.
  induction Ss; intros; try contradiction.
  destruct s1 as [s1h s1t]. destruct s2 as [s2h s2t].
  destruct i as [i Hi]. destruct i.
  - simpl in Hproj_s. subst.
    destruct l as [lh | lt].
    + simpl.  destruct om as [[m Hm]|]; simpl; try (split; reflexivity).
      destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; split; reflexivity.
    + simpl in Hli. destruct (composed_list_ilabel Ss lt) as [j Hj] eqn:Hl. inversion Hli.
  - simpl in Hproj_s. simpl in Hi.
    destruct l as [lh | lt].
    +  simpl in Hli. inversion Hli.
    + destruct om as [[m Hm]|].
      * simpl. destruct (composed_list_proto_message_decidable Ss m) as [Hpm | Hnpm]; simpl; try (split; reflexivity || assumption).
        specialize (IHSs s1t s2t (Some (exist _ m Hpm)) lt (exist _ i (le_pred _ _ Hi)) Hproj_s).
        simpl in Hli.
        remember (composed_list_ilabel Ss lt) as j.
        destruct j as [j Hj].
        inversion Hli; subst.
        assert
          (Hirrelevant :
            exist (fun n : nat => n < length Ss) i Hj =
            exist (fun n : nat => n < length Ss) i (le_pred (S (S i)) (S (length Ss)) Hi)
          ) by ( apply f_equal; apply proof_irrelevance ).
        specialize (IHSs Hirrelevant).
        destruct IHSs as [Hmsg' Hs'].
        split; try assumption. simpl. apply f_equal. assumption.
      * specialize (IHSs s1t s2t None lt (exist _ i (le_pred _ _ Hi)) Hproj_s).
        simpl in Hli. 
        remember (composed_list_ilabel Ss lt) as j.
        destruct j as [j Hj].
        inversion Hli; subst.
        assert
          (Hirrelevant :
            exist (fun n : nat => n < length Ss) i Hj =
            exist (fun n : nat => n < length Ss) i (le_pred (S (S i)) (S (length Ss)) Hi)
          ) by ( apply f_equal; apply proof_irrelevance ).
        specialize (IHSs Hirrelevant).
        destruct IHSs as [Hmsg' Hs'].
        split; try assumption. simpl. apply f_equal. assumption.
Qed.


Lemma composed_list_transition_projection_state_preservation
  {message}
  (Ss : list (VLSM message))
  : forall
      (s : composed_list_state Ss)
      (om : option (composed_list_proto_message Ss))
      (l : composed_list_label Ss)
      (i : composed_list_index Ss)
      (Hnli : composed_list_ilabel Ss l <> i),
        composed_list_istate_proj Ss i (fst (composed_list_transition Ss l (s, om))) = composed_list_istate_proj Ss i s
  .
Proof.
  induction Ss as [| Sh St IHSt]; intros; try contradiction.
  destruct s as [sh st].
  destruct i as [i Hi]. destruct i; destruct l as [lh |lt]
  ; destruct om as [[m Hm]|]; try reflexivity
  ; simpl in Hnli
  ; try (exfalso; apply Hnli; apply f_equal; apply proof_irrelevance); simpl.
  - destruct (composed_list_proto_message_decidable St m) as [Hpm | Hnpm]; simpl; reflexivity.
  - destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; reflexivity.
  - destruct (composed_list_proto_message_decidable St m) as [Hpm | Hnpm]; simpl; try reflexivity.
    specialize (IHSt st (Some (exist _ m Hpm)) lt (exist _ i (le_pred _ _ Hi))).
    simpl in IHSt. apply IHSt.
    remember (composed_list_ilabel St lt) as j. destruct j as [j Hj].
    intros Heq. apply Hnli. inversion Heq; subst. apply f_equal. apply proof_irrelevance.
  - specialize (IHSt st None lt (exist _ i (le_pred _ _ Hi))).
    simpl in IHSt. apply IHSt.
    remember (composed_list_ilabel St lt) as j. destruct j as [j Hj].
    intros Heq. apply Hnli. inversion Heq; subst. apply f_equal. apply proof_irrelevance.
Qed.

Lemma composed_list_transition_projection_type_preservation
  {message}
  (Ss : list (VLSM message))
  : forall
      (s : composed_list_state Ss)
      (om : option (composed_list_proto_message Ss))
      (l : composed_list_label Ss)
      (i : composed_list_index Ss)
      (Hli : composed_list_ilabel Ss l = i),
      noneOrAll
        (option_map (composed_list_iproto_message_prop Ss i)
          (option_map (@proj1_sig message (composed_list_proto_message_prop Ss))
            (snd (composed_list_transition Ss l (s, om)))))
  .
Proof.
  induction Ss as [| Sh St IHSt]; intros; try contradiction.
  destruct s as [sh st].
  destruct i as [i Hi]. destruct i.
  - destruct l as [lh | lt].
    + destruct om as [[m Hm]|]; simpl in *; subst
      ; try (destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl); try exact I.
      * remember (transition lh (sh, Some (exist proto_message_prop m Hpm))) as t.
        destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
      * remember (transition lh (sh, None)) as t.
        destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
    + simpl in Hli. destruct (composed_list_ilabel St lt). inversion Hli.
  - simpl in Hli. destruct l as [lh | lt].
    + inversion Hli.
    + destruct om as [[m Hm]|]; simpl in *; subst.
      * destruct (composed_list_proto_message_decidable St m) as [Hpm | Hnpm]; simpl; try exact I.
        specialize (IHSt st (Some (exist _ m Hpm)) lt (exist _ i (le_pred _ _ Hi))).

        remember (composed_list_ilabel St lt) as it. destruct it as [it Hit].
        inversion Hli. subst.
        assert
          (Hirrelevant :
            exist (fun n : nat => n < length St) i Hit =
            exist (fun n : nat => n < length St) i (le_pred (S (S i)) (S (length St)) Hi)
          ) by ( apply f_equal; apply proof_irrelevance ).
        specialize (IHSt Hirrelevant).


        remember (Some (exist (composed_list_proto_message_prop St) m Hpm)) as opm.
        unfold composed_list_state in IHSt. unfold composed_list_proto_message in IHSt.
        remember (composed_list_transition St lt (st, opm)) as t.
        destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
      * specialize (IHSt st None lt (exist _ i (le_pred _ _ Hi))).

        remember (composed_list_ilabel St lt) as it. destruct it as [it Hit].
        inversion Hli. subst.
        assert
          (Hirrelevant :
            exist (fun n : nat => n < length St) i Hit =
            exist (fun n : nat => n < length St) i (le_pred (S (S i)) (S (length St)) Hi)
          ) by ( apply f_equal; apply proof_irrelevance ).
        specialize (IHSt Hirrelevant).

        unfold composed_list_state in IHSt. 
        remember (composed_list_transition St lt (st, None)) as t.
        destruct t as (s', om'). destruct om' as [[m' Hpm']|]; simpl; try assumption; try exact I.
Qed.

Definition composed_list_vlsm_composed_instance
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : @composed_vlsm_class message (composed_list_vlsm Ss Ssnn) :=
  {| index := composed_list_index Ss
  ; index_eq_dec := composed_list_index_eq_dec Ss
  ; iproto_state := composed_list_iproto_state Ss
  ; istate_proj := composed_list_istate_proj' Ss Ssnn
  ; ilabel := composed_list_ilabel Ss
  ; ilabel_type_inhabited := composed_list_ilabel_type_inhabited Ss
  ; iproto_message_prop := composed_list_iproto_message_prop Ss
  ; iproto_message_decidable := composed_list_iproto_message_decidable Ss
  ; iproto_message_inhabited := composed_list_iproto_message_inhabited Ss
  ; iproto_message_consistent := composed_list_iproto_message_consistent Ss
  ; transition_projection_consistency := composed_list_transition_projection_consistency Ss
  ; transition_projection_state_preservation := composed_list_transition_projection_state_preservation Ss
  ; transition_projection_type_preservation := composed_list_transition_projection_type_preservation Ss
  |}.

Definition composed_list_constrained_istate_proj
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  (constraint : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop)
  (i : composed_list_index Ss)
  (s : @state message (composed_list_vlsm_constrained Ss Ssnn constraint))
  : composed_list_iproto_state Ss i
  := composed_list_istate_proj Ss i s.


Definition composed_list_vlsm_constrained_composed_instance
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  (constraint : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop)
  : @composed_vlsm_class message (composed_list_vlsm_constrained Ss Ssnn constraint) :=
  {| index := composed_list_index Ss
  ; index_eq_dec := composed_list_index_eq_dec Ss
  ; iproto_state := composed_list_iproto_state Ss
  ; istate_proj := composed_list_constrained_istate_proj Ss Ssnn constraint
  ; ilabel := composed_list_ilabel Ss
  ; ilabel_type_inhabited := composed_list_ilabel_type_inhabited Ss
  ; iproto_message_prop := composed_list_iproto_message_prop Ss
  ; iproto_message_decidable := composed_list_iproto_message_decidable Ss
  ; iproto_message_inhabited := composed_list_iproto_message_inhabited Ss
  ; iproto_message_consistent := composed_list_iproto_message_consistent Ss
  ; transition_projection_consistency := composed_list_transition_projection_consistency Ss
  ; transition_projection_state_preservation := composed_list_transition_projection_state_preservation Ss
  ; transition_projection_type_preservation := composed_list_transition_projection_type_preservation Ss
  |}.

Definition indexed_vlsm_istate
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  : Type
  := @state message (IS i).


Definition indexed_vlsm_istate_proj
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  (s : indexed_state IS)
  : @indexed_vlsm_istate oindex message Heqd IS i
  :=
  s i.

Definition indexed_vlsm_istate_proj'
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  (i : oindex)
  (s : @state _ (indexed_vlsm IS Hi))
  : @indexed_vlsm_istate oindex message Heqd IS i
  :=
  indexed_vlsm_istate_proj i s.


Definition indexed_vlsm_ilabel
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (l : indexed_label IS)
  : oindex
  :=
  projT1 l.


Lemma indexed_vlsm_ilabel_type_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  : inhabited { l : indexed_label IS | indexed_vlsm_ilabel l = i }.
Proof.
  specialize (@label_inhabited message (IS i)); intros [li].
  constructor. 
  exists (existT _ i li).
  reflexivity.
Qed.

Definition indexed_vlsm_iproto_message_prop
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  : message -> Prop
  :=
  @proto_message_prop message (IS i).

Definition indexed_vlsm_iproto_message_decidable
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  : forall m : message, {indexed_vlsm_iproto_message_prop i m} + {~indexed_vlsm_iproto_message_prop i m}
  :=
  @proto_message_decidable message (IS i).

Definition indexed_vlsm_iproto_message_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  (i : oindex)
  : inhabited {m : message | indexed_vlsm_iproto_message_prop i m}
  :=
  @message_inhabited message (IS i).

Lemma indexed_vlsm_iproto_message_consistent
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> VLSM message}
  (i : index)
  : forall m : message,
  indexed_vlsm_iproto_message_prop i m ->
  @proto_message_prop message (indexed_vlsm IS (inhabits i)) m.
Proof.
  unfold indexed_vlsm_iproto_message_prop.
  intros m Hmi.
  exists i. assumption.
Qed.

Lemma indexed_vlsm_transition_projection_consistency
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  : forall
      (s1 s2 : indexed_state IS)
      (om : option (indexed_proto_message IS))
      (l : indexed_label IS)
      (i : oindex)
      (Hproj_s : indexed_vlsm_istate_proj i s1 = indexed_vlsm_istate_proj i s2)
      (Hli : indexed_vlsm_ilabel l = i),
    (   snd (indexed_transition IS l (s1, om)) = snd (indexed_transition IS l (s2, om))
    /\  indexed_vlsm_istate_proj i (fst (indexed_transition IS l (s1, om)))
      = indexed_vlsm_istate_proj i (fst (indexed_transition IS l (s2, om)))
    ).
Proof.
  intros.
  destruct l as [j l]. simpl in Hli. subst.
  unfold indexed_vlsm_istate_proj in Hproj_s.
  unfold indexed_vlsm_istate_proj.
  simpl.
  destruct om as [[m Hm]|].
  - destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; try (split; reflexivity || assumption).
    rewrite <- Hproj_s. 
    remember (transition l (s1 i, Some (exist proto_message_prop m Hpm))) as t.
    destruct t as [si' om']. simpl. split; try reflexivity.
    destruct (eq_dec i i); try contradiction.
    reflexivity.
  - rewrite <- Hproj_s.
    remember (transition l (s1 i, None)) as t.
    destruct t as [si' om']. simpl. split; try reflexivity.
    destruct (eq_dec i i); try contradiction.
    reflexivity.
Qed.

Lemma indexed_vlsm_transition_projection_state_preservation
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  : forall
      (s : indexed_state IS)
      (om : option (indexed_proto_message IS))
      (l : indexed_label IS)
      (i : oindex)
      (Hnli : indexed_vlsm_ilabel l <> i),
        indexed_vlsm_istate_proj i (fst (indexed_transition IS l (s, om))) = indexed_vlsm_istate_proj i s
  .
Proof.
  intros.
  destruct l as [j l]. simpl in Hnli.
  simpl.
  destruct om as [[m Hm]|]
  ; (destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; try reflexivity
    ; remember (transition l (s j, Some (exist proto_message_prop m Hpm))) as t)
    || remember (transition l (s j, None)) as t
  ; destruct t as [s' om']; simpl
  ; unfold indexed_vlsm_istate_proj
  ; destruct (eq_dec i j); try (subst; contradiction)
  ; reflexivity
  .
Qed.


Lemma indexed_vlsm_transition_projection_type_preservation
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  : forall
      (s : indexed_state IS)
      (om : option (indexed_proto_message IS))
      (l : indexed_label IS)
      (i : oindex)
      (Hli : indexed_vlsm_ilabel l = i),
      noneOrAll
        (option_map (indexed_vlsm_iproto_message_prop i)
          (option_map (@proj1_sig message (indexed_proto_message_prop IS))
            (snd (indexed_transition IS l (s, om)))))
  .
Proof.
  intros.
  destruct l as [j l]. simpl in Hli. subst.
  simpl.
  destruct om as [[m Hm]|]
  ; (destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; try exact I
  ; remember (transition l (s i, Some (exist proto_message_prop m Hpm))) as t)
    || remember (transition l (s i, None)) as t
  ; destruct t as [s' om']; simpl
  ; destruct om' as [[m' Hm']|]; simpl; try exact I
  ;  assumption.
Qed.

Definition indexed_vlsm_composed_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  : @composed_vlsm_class message (indexed_vlsm IS Hi) :=
  {| index := oindex
  ; iproto_state := @indexed_vlsm_istate oindex message Heqd IS
  ; istate_proj := @indexed_vlsm_istate_proj' oindex message Heqd IS Hi
  ; ilabel := indexed_vlsm_ilabel
  ; ilabel_type_inhabited := indexed_vlsm_ilabel_type_inhabited
  ; iproto_message_prop := indexed_vlsm_iproto_message_prop
  ; iproto_message_decidable := indexed_vlsm_iproto_message_decidable
  ; iproto_message_inhabited := indexed_vlsm_iproto_message_inhabited
  ; iproto_message_consistent := indexed_vlsm_iproto_message_consistent
  ; transition_projection_consistency := indexed_vlsm_transition_projection_consistency
  ; transition_projection_state_preservation := indexed_vlsm_transition_projection_state_preservation
  ; transition_projection_type_preservation := indexed_vlsm_transition_projection_type_preservation
  |}.

Definition indexed_vlsm_constrained_istate_proj
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (i : oindex)
  (s : @state _ (indexed_vlsm_constrained IS Hi constraint))
  : @indexed_vlsm_istate oindex message Heqd IS i
  :=
  indexed_vlsm_istate_proj i s.

Definition indexed_vlsm_constrained_composed_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (Hi : inhabited oindex)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : @composed_vlsm_class message (indexed_vlsm_constrained IS Hi constraint) :=
  {| index := oindex
  ; iproto_state := @indexed_vlsm_istate oindex message Heqd IS
  ; istate_proj := @indexed_vlsm_constrained_istate_proj oindex message Heqd IS Hi constraint
  ; ilabel := indexed_vlsm_ilabel
  ; ilabel_type_inhabited := indexed_vlsm_ilabel_type_inhabited
  ; iproto_message_prop := indexed_vlsm_iproto_message_prop
  ; iproto_message_decidable := indexed_vlsm_iproto_message_decidable
  ; iproto_message_inhabited := indexed_vlsm_iproto_message_inhabited
  ; iproto_message_consistent := indexed_vlsm_iproto_message_consistent
  ; transition_projection_consistency := indexed_vlsm_transition_projection_consistency
  ; transition_projection_state_preservation := indexed_vlsm_transition_projection_state_preservation
  ; transition_projection_type_preservation := indexed_vlsm_transition_projection_type_preservation
  |}.
