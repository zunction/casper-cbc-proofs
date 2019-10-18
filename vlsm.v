Require Import List Streams.
Import ListNotations.

From Casper
Require Import ListExtras.

Section GenericVLSM.

Class VLSM (message : Type) :=
  { state : Type
  ; label : Type
  ; initial_state_prop : state -> Prop
  ; protocol_state_inhabited : { p : state | initial_state_prop p}
  ; initial_message_prop : message -> Prop
  ; message_inhabited : { _ : message | True }
  ; label_inhabited : { _ : label | True }
  ; transition : option message -> label -> state -> (state * option message)%type
  ; valid : option message -> label -> state  -> Prop
  }.

Definition initial_state
  {message : Type}
  `{V : VLSM message}
  : Type := { i : state | initial_state_prop  i }.

Definition initial_message
  {message : Type}
  `{V : VLSM message}
  : Type := { i : message | initial_message_prop  i }.

Inductive
  protocol_state_prop
    {message}
    `{V : VLSM message}
    : state -> Prop
    := 
      | initial_protocol_state
        : forall s : initial_state,
        protocol_state_prop (proj1_sig s)
      | next_protocol_state_no_message
        : forall (s s' : state) (l : label) (om' : option message),
        protocol_state_prop s ->
        valid None l s ->
        transition None l s = (s', om') ->
        protocol_state_prop s'
      | next_protocol_state_with_message
        : forall (s s' : state) (l : label) (m : message) (om' : option message),
        protocol_state_prop s ->
        protocol_message_prop m ->
        valid (Some m) l s ->
        transition (Some m) l s = (s', om') ->
        protocol_state_prop s'
  with
  protocol_message_prop
    {message}
    `{V : VLSM message}
    : message -> Prop
    := 
      | initial_protocol_message
        : forall m : initial_message,
        protocol_message_prop (proj1_sig m)
      | create_protocol_message
        : forall (s s' : state) (l : label) (m' : message),
        protocol_state_prop s ->
        valid None l s ->
        transition None l s = (s', Some m') ->
        protocol_message_prop m'
      | receive_protocol_message
        : forall (s s' : state) (l : label) (m m' : message),
        protocol_state_prop s ->
        protocol_message_prop m ->
        valid (Some m) l s ->
        transition (Some m) l s = (s', Some m') ->
        protocol_message_prop m'
  .

(* Consider using optional protocol message above, if possible *)

Definition protocol_state
  {message}
  `{V : VLSM message}
  : Type := { s : state | protocol_state_prop s }.

Definition protocol_message
  {message}
  `{V : VLSM message}
  : Type := { s : message | protocol_message_prop s }.

Definition labeled_valid_transition
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps ps' : protocol_state)
  : Prop
  :=
  let om := option_map (@proj1_sig message protocol_message_prop) opm in
  let s := proj1_sig ps in
  let s' := proj1_sig ps' in
    fst (transition om l s) = s'
    /\ valid om l s.

Definition valid_transition
  {message}
  `{V : VLSM message}
  (ps ps' : protocol_state)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_transition opm l ps ps'.

Inductive valid_trace
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> Prop :=
  | valid_trace_one
    : forall s s',
    valid_transition s s' ->
    valid_trace s s'
  | valid_trace_more
    : forall s s' s'',
    valid_transition s s' ->
    valid_trace s' s'' ->
    valid_trace s s''
  .

Lemma extend_valid_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace.
  induction Htrace as [s1 s2 Ht12| s1 s1' s2 Ht11' Htrace1'2 IHtrace1'3]; intros Ht23.
  - apply valid_trace_more with s2; try assumption.
    apply valid_trace_one. assumption.
  - specialize (IHtrace1'3 Ht23).
    apply valid_trace_more with s1'; assumption.
Qed.

Definition valid_reflexive_trace
  {message}
  `{V : VLSM message}
  (s s' : protocol_state)
  : Prop
  :=
  s = s' \/ valid_trace s s'.

Lemma extend_valid_reflexive_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_reflexive_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace12 Ht23.
  destruct Htrace12 as [Heq | Htrace12].
  - subst. apply valid_trace_one. assumption.
  - apply extend_valid_trace with s2; assumption.
Qed.


Definition labeled_valid_message_production
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps : protocol_state)
  (pm' : protocol_message)
  : Prop
  :=
  let om := option_map (@proj1_sig message protocol_message_prop) opm in
  let s := proj1_sig ps in
  let m' := proj1_sig pm' in
    snd (transition om l s) = Some m'
    /\ valid om l s.

Definition valid_message_production
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_message_production opm l s m'.

Definition valid_trace_message
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists s', valid_reflexive_trace s s' /\ valid_message_production s' m'.

Lemma valid_protocol_message
  {message}
  `{V : VLSM message}
  : forall (pm : protocol_message),
  (exists im : initial_message, proj1_sig pm = proj1_sig im)
  \/
  (exists (s : protocol_state),
   exists (pm' : protocol_message),
   valid_trace_message s pm' /\ proj1_sig pm = proj1_sig pm').
Proof.
  intros. destruct pm as [m Hpm].  simpl. destruct Hpm as [im | s s' l m' Hps Hv Ht | s s' l m m' Hps Hpm Hv Ht ]
  ; try (
      right
    ; exists (exist _ s Hps)
    ; ( exists (exist _ m' (create_protocol_message s s' l m' Hps Hv Ht))
      || exists (exist _ m' (receive_protocol_message s s' l m m' Hps Hpm Hv Ht))
      )
    ; simpl
    ; split; try reflexivity
    ; exists (exist _ s Hps)
    ; split; try (left; reflexivity)
    )
  .
  - left. exists im. reflexivity.
  - exists None; exists l; unfold labeled_valid_message_production; simpl; rewrite Ht; simpl; split; try assumption; reflexivity.
  - exists (Some (exist _ m Hpm)); exists l; unfold labeled_valid_message_production; simpl; rewrite Ht; simpl; split; try assumption; reflexivity.
Qed.

Inductive trace_from_to
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> list protocol_state -> Prop
  :=
  | trace_from_to_one
    : forall s1 s2, valid_transition s1 s2 -> trace_from_to s1 s2 [s1; s2]
  | trace_from_to_more
    : forall s1 s3 ts s2, valid_transition s1 s2 -> trace_from_to s2 s3 ts -> trace_from_to s1 s3 (s1 :: ts)
  .

Lemma extend_trace_from_to_left
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s2 s3 ls ->
  valid_transition s1 s2 ->
  trace_from_to s1 s3 (s1 :: ls).
Proof.
  intros s1 s2 s3 ls Ht23 Hv12.
  apply trace_from_to_more with s2; assumption.
Qed.

Lemma extend_trace_from_to_right
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s1 s2 ls ->
  valid_transition s2 s3 ->
  trace_from_to s1 s3 (ls ++ [s3]).
Proof.
  intros s1 s2 s3 ls Ht12 Hv23.
  induction Ht12 as [s1 s2 Hv12 | s1 s2 ls s1' Hv11' Ht1'2 Ht1'3].
  - simpl. apply trace_from_to_more with s2; try assumption.
    apply trace_from_to_one. assumption.
  - specialize (Ht1'3 Hv23).
    rewrite <- app_comm_cons.
    apply extend_trace_from_to_left with s1'; assumption.
Qed.

CoInductive infinite_trace_from
  {message}
  `{V : VLSM message}
  : protocol_state -> Stream protocol_state -> Prop
  :=
  | infinite_trace_first
    : forall s1 ts s2,
    valid_transition s1 s2 ->
    infinite_trace_from s2 ts ->
    infinite_trace_from s1 (Cons s1 ts)
  .

Inductive Trace `{VLSM} : Type :=
  | Finite : list protocol_state -> Trace
  | Infinite : Stream protocol_state -> Trace
  .

Definition filtered_finite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : list protocol_state)
  : Prop
  :=
  match ts with
  | [] => False
  | [s] => False
  | s :: t => subset s /\ trace_from_to s (last t s) ts
  end.

Definition initial_protocol_state_prop
  {message}
  `{V : VLSM message}
  (ps : protocol_state)
  : Prop
  :=
  initial_state_prop (proj1_sig ps).

Definition protocol_finite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : list protocol_state)
  : Prop
  := filtered_finite_trace initial_protocol_state_prop ts.

Definition filtered_infinite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : Stream protocol_state)
  : Prop
  :=
  subset (hd ts) /\ infinite_trace_from (hd ts) ts.

Definition protocol_infinite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : Stream protocol_state)
  : Prop
  := filtered_infinite_trace initial_protocol_state_prop ts.

Definition protocol_trace_prop
  {message}
  `{V : VLSM message}
  (t : Trace)
  : Prop
  :=
  match t with
  | Finite ts => protocol_finite_trace_prop ts
  | Infinite ts => protocol_infinite_trace_prop ts
  end.

Definition protocol_trace
  {message}
  `{V : VLSM message}
  : Type := { t : Trace | protocol_trace_prop t}.

Definition first
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact h.
  - destruct t as [h t].
    exact h.
Defined.

Definition last
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : option protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact (Some (last t h)).
  - exact None.
Defined.

Lemma procotol_state_reachable
  {message}
  `{V : VLSM message}
  : forall ps : protocol_state,
  initial_state_prop (proj1_sig ps) \/
  exists t : protocol_trace,
  exists ps' : protocol_state,
  last t = Some ps' /\ proj1_sig ps = proj1_sig ps'.
Proof.
  intros. destruct ps as [s Hps]. simpl.
  induction Hps as
    [ is
    | s s' l om' Hps IHps Hv Ht
    | s s' l m om' Hps IHps Hpm Hv Ht
    ].
  - left. destruct is as [s His]. assumption.
  - right. destruct IHps as [His | Hmore].
    + remember (exist _ s' (next_protocol_state_no_message s s' l om' Hps Hv Ht)) as ps'.
      remember (exist _ s His) as is.
      remember (exist _ s (initial_protocol_state (exist _ s His))) as ps.
      assert (Hips : initial_protocol_state_prop ps)
        by (subst; unfold initial_protocol_state_prop; assumption).
      assert (Hvt : valid_transition ps ps').
      { subst; exists None. exists l. unfold labeled_valid_transition. simpl. split; try assumption. rewrite Ht. reflexivity. }
      assert (Pt : trace_from_to ps ps' [ps; ps']) by (apply trace_from_to_one; assumption).
      assert (Hpt : protocol_trace_prop (Finite [ps; ps']))
        by (split; assumption).
      exists (exist _ (Finite [ps; ps']) Hpt). exists ps'. subst. simpl. split; reflexivity.
    + destruct Hmore as [pt [ps [Heq_last Heq_s]]].
      destruct pt as [t Hpt].
      destruct t as [t | t].
      * unfold protocol_trace_prop in Hpt. unfold protocol_finite_trace_prop in Hpt.
        unfold filtered_finite_trace in Hpt.
        destruct t as [|h t]; try contradiction.
        destruct t as [|h' t]; try contradiction.
        destruct Hpt as [Hhi Htrace].
        assert (Hlast : last (exist (fun t : Trace => protocol_trace_prop t) (Finite (h :: h' :: t)) (conj Hhi Htrace)) = Some (List.last (h' :: t) h))
          by reflexivity.
        rewrite Hlast in Heq_last. inversion Heq_last as [Heq_last'].
        simpl in Htrace. assert (Htrace' := Htrace). rewrite Heq_last' in Htrace'.
        remember (exist _ s' (next_protocol_state_no_message s s' l om' Hps Hv Ht)) as ps'.
        assert (Hvss' : valid_transition ps ps').
        { exists None. exists l. split; simpl; rewrite <- Heq_s; try assumption. rewrite Ht; subst; reflexivity. }
        assert (Hts' : trace_from_to h ps' (h :: h' :: (t ++ [ps']))).
        { repeat rewrite app_comm_cons. apply extend_trace_from_to_right with ps; assumption. }
        assert (Hhs'pt : protocol_trace_prop (Finite (h :: h' :: t ++ [ps']))).
        { split; try assumption. rewrite app_comm_cons. rewrite last_is_last. assumption. }
        remember (exist (fun t : Trace => protocol_trace_prop t) (Finite (h :: h' :: t ++ [ps'])) Hhs'pt) as ths'.
        exists ths'. exists ps'.
        rewrite Heqps' at 2; simpl. split; try reflexivity.
        rewrite Heqths'. simpl. rewrite last_is_last. destruct t; reflexivity.
      * simpl in Heq_last. inversion Heq_last.
  - right. destruct IHps as [His | Hmore].
    + remember (exist _ s' (next_protocol_state_with_message s s' l m om' Hps Hpm Hv Ht)) as ps'.
      remember (exist _ s His) as is.
      remember (exist _ s (initial_protocol_state (exist _ s His))) as ps.
      assert (Hips : initial_protocol_state_prop ps)
        by (subst; unfold initial_protocol_state_prop; assumption).
      assert (Hvt : valid_transition ps ps').
      { subst; exists (Some (exist _ m Hpm)). exists l. unfold labeled_valid_transition. simpl. split; try assumption. rewrite Ht. reflexivity. }
      assert (Pt : trace_from_to ps ps' [ps; ps']) by (apply trace_from_to_one; assumption).
      assert (Hpt : protocol_trace_prop (Finite [ps; ps']))
        by (split; assumption).
      exists (exist _ (Finite [ps; ps']) Hpt). exists ps'. subst. simpl. split; reflexivity.
    + destruct Hmore as [pt [ps [Heq_last Heq_s]]].
      destruct pt as [t Hpt].
      destruct t as [t | t].
      * unfold protocol_trace_prop in Hpt. unfold protocol_finite_trace_prop in Hpt.
        unfold filtered_finite_trace in Hpt.
        destruct t as [|h t]; try contradiction.
        destruct t as [|h' t]; try contradiction.
        destruct Hpt as [Hhi Htrace].
        assert (Hlast : last (exist (fun t : Trace => protocol_trace_prop t) (Finite (h :: h' :: t)) (conj Hhi Htrace)) = Some (List.last (h' :: t) h))
          by reflexivity.
        rewrite Hlast in Heq_last. inversion Heq_last as [Heq_last'].
        simpl in Htrace. assert (Htrace' := Htrace). rewrite Heq_last' in Htrace'.
        remember (exist _ s' (next_protocol_state_with_message s s' l m om' Hps Hpm Hv Ht)) as ps'.
        assert (Hvss' : valid_transition ps ps').
        { exists (Some (exist _ m Hpm)). exists l. split; simpl; rewrite <- Heq_s; try assumption. rewrite Ht; subst; reflexivity. }
        assert (Hts' : trace_from_to h ps' (h :: h' :: (t ++ [ps']))).
        { repeat rewrite app_comm_cons. apply extend_trace_from_to_right with ps; assumption. }
        assert (Hhs'pt : protocol_trace_prop (Finite (h :: h' :: t ++ [ps']))).
        { split; try assumption. rewrite app_comm_cons. rewrite last_is_last. assumption. }
        remember (exist (fun t : Trace => protocol_trace_prop t) (Finite (h :: h' :: t ++ [ps'])) Hhs'pt) as ths'.
        exists ths'. exists ps'.
        rewrite Heqps' at 2; simpl. split; try reflexivity.
        rewrite Heqths'. simpl. rewrite last_is_last. destruct t; reflexivity.
      * simpl in Heq_last. inversion Heq_last.
Qed.

Definition final_state_prop
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  : Prop
  :=
  ~ exists s' : protocol_state, valid_transition s s'.

Definition final_state
  {message}
  `{V : VLSM message}
  : Type := { s : protocol_state | final_state_prop s}.

Definition terminating_trace
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  match last t with
  | Some ps => final_state_prop ps
  | None => False
  end.

Definition infinite_trace
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  last t = None.

Definition complete_trace
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  infinite_trace t \/ terminating_trace t.


End GenericVLSM.

Section Composing2VLSMs.

Definition composed2_initial_state_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (s : (@state message S1) * (@state message S2)) : Prop
  :=
  match s with
  | (s1, s2) => initial_state_prop s1 /\ initial_state_prop s2
  end.

Lemma composed2_protocol_state_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : { p : (@state message S1) * (@state message S2) | composed2_initial_state_prop S1 S2 p}.
Proof.
  destruct (@protocol_state_inhabited message S1).
  destruct (@protocol_state_inhabited message S2).
  exists (x, x0). split; assumption.
Qed.

Definition composed2_initial_message_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (m : message)
  :=
  @initial_message_prop _ S1 m \/ @initial_message_prop _ S2 m.

Lemma composed2_message_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : { _ : message | True }
  .
Proof.
  exact (@message_inhabited message S1).
Qed.

Lemma composed2_label_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : { _ : (@label message S1) + (@label message S2) | True }.
Proof.
  split; try exact I.
  left.
  destruct (@label_inhabited message S1).
  exact x.
Qed.

Definition composed2_transition
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (om : option message)
  (l : (@label message S1) + (@label message S2))
  (s : (@state message S1) * (@state message S2))
  : (((@state message S1) * (@state message S2)) * option message)%type
  :=
  match l,s with
  | inl l1, (s1, s2) =>
    ((fst (transition om l1 s1), s2), snd (transition om l1 s1))
  | inr l2, (s1, s2) =>
    (s1, (fst (transition om l2 s2)), snd (transition om l2 s2))
  end.

Definition composed2_valid
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (om : option message)
  (l : (@label message S1) + (@label message S2))
  (s : (@state message S1) * (@state message S2))
  : Prop
  :=
  match l,s with
  | inl l1, (s1, s2) => valid om l1 s1
  | inr l2, (s1, s2) => valid om l2 s2
  end.

Definition composed2_valid_constrained
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : option message -> (@label message S1) + (@label message S2) -> (@state message S1) * (@state message S2) -> Prop)
  (om : option message )
  (l : (@label message S1) + (@label message S2))
  (s : (@state message S1) * (@state message S2))
  :=
  composed2_valid S1 S2 om l s /\ constraint om l s.

Definition compose2_vlsm
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : VLSM message
  :=
  {| state := (@state message S1) * (@state message S2)
  ; label := (@label message S1) + (@label message S2)
  ; initial_state_prop := composed2_initial_state_prop S1 S2
  ; protocol_state_inhabited := composed2_protocol_state_inhabited S1 S2
  ; initial_message_prop := composed2_initial_message_prop S1 S2
  ; message_inhabited := composed2_message_inhabited S1 S2
  ; label_inhabited := composed2_label_inhabited S1 S2
  ; transition := composed2_transition S1 S2
  ; valid := composed2_valid S1 S2
  |}.

Definition compose2_vlsm_constrained
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : option message -> (@label message S1) + (@label message S2) -> (@state message S1) * (@state message S2) -> Prop)
  : VLSM message
  :=
  {| state := (@state message S1) * (@state message S2)
  ; label := (@label message S1) + (@label message S2)
  ; initial_state_prop := composed2_initial_state_prop S1 S2
  ; protocol_state_inhabited := composed2_protocol_state_inhabited S1 S2
  ; initial_message_prop := composed2_initial_message_prop S1 S2
  ; message_inhabited := composed2_message_inhabited S1 S2
  ; label_inhabited := composed2_label_inhabited S1 S2
  ; transition := composed2_transition S1 S2
  ; valid := composed2_valid_constrained S1 S2 constraint
  |}.

End Composing2VLSMs.

Section ComposingVLSMs.

(* TODO: minimal assumptions for communication. Do we really need that messages are shared.
    maybe add a ptoto_message predicate defining a subset for each VLSM.
  *)
Definition composed_state {message} (Ss : list (VLSM message)) : Type :=
  fold_right prod unit (List.map (@state message) Ss).

Definition composed_label {message} (Ss : list (VLSM message)) : Type :=
  fold_right sum Empty_set (List.map (@label message) Ss).

Fixpoint composed_initial_state_prop
  {message}
  (Ss : list (VLSM message))
  : composed_state Ss -> Prop.
destruct Ss as [|Sh St]; unfold composed_state; simpl; intros.
- exact True.
- destruct X as [sh st].
  exact (@initial_state_prop _ Sh sh /\ composed_initial_state_prop _ St st).
Defined.

Lemma composed_protocol_state_inhabited
  {message}
  (Ss : list (VLSM message))
  : {s : composed_state Ss | composed_initial_state_prop Ss s}.
Proof.
  induction Ss as [| Sh St IHt].
  - exists tt. exact I.
  - destruct IHt as [st Ht].
    destruct (@protocol_state_inhabited _ Sh) as [sh Hh].
    exists (sh, st). split; assumption.
Qed.

Fixpoint composed_initial_message_prop
  {message}
  (Ss : list (VLSM message))
  : message -> Prop.
destruct Ss as [|Sh St]; unfold composed_state; simpl; intros.
- exact False.
- exact (@initial_message_prop _ Sh X \/ composed_initial_message_prop _ St X).
Defined.

Lemma composed_message_inhabited
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : { _ : message | True }
  .
Proof.
  destruct Ss as [| Sh St]; try contradiction.
  exact (@message_inhabited _ Sh).
Qed.

Lemma composed_label_inhabited
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : { _ : composed_label Ss | True }.
Proof.
  split; try exact I.
  destruct Ss as [| Sh St]; try contradiction.
  left.
  destruct (@label_inhabited message Sh).
  exact x.
Qed.

Fixpoint composed_transition
  {message}
  (Ss : list (VLSM message))
  : option message -> composed_label Ss -> composed_state Ss -> (composed_state Ss * option message)%type.
destruct Ss as [| Sh St]; unfold composed_label; unfold composed_state; simpl
; intros om l s.
- inversion l.
- destruct s as [sh st]. destruct l as [lh | lt].
  + destruct (transition om lh sh) as [sh' om'].
    exact ((sh', st), om').
  + destruct (composed_transition message St om lt st) as  [st' om'].
    exact ((sh, st'), om').
Defined.

Fixpoint composed_valid
  {message}
  (Ss : list (VLSM message))
  : option message -> composed_label Ss -> composed_state Ss -> Prop.
destruct Ss as [| Sh St]; unfold composed_label; unfold composed_state; simpl
; intros om l s.
- inversion l.
- destruct s as [sh st]. destruct l as [lh | lt].
  + exact (valid om lh sh).
  + exact (composed_valid message St om lt st).
Defined.

Definition composed_valid_constrained
  {message}
  (Ss : list (VLSM message))
  (constraint : option message -> composed_label Ss -> composed_state Ss -> Prop)
  (om : option message )
  (l : composed_label Ss)
  (s : composed_state Ss)
  :=
  composed_valid Ss om l s /\ constraint om l s.

Definition composed_vlsm
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : VLSM message
  :=
  {| state := composed_state Ss
  ; label := composed_label Ss
  ; initial_state_prop := composed_initial_state_prop Ss
  ; protocol_state_inhabited := composed_protocol_state_inhabited Ss
  ; initial_message_prop := composed_initial_message_prop Ss
  ; message_inhabited := composed_message_inhabited Ss Ssnn
  ; label_inhabited := composed_label_inhabited Ss Ssnn
  ; transition := composed_transition Ss
  ; valid := composed_valid Ss
  |}.

Definition composed_vlsm_constrained
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  (constraint : option message -> composed_label Ss -> composed_state Ss -> Prop)
  : VLSM message
  :=
  {| state := composed_state Ss
  ; label := composed_label Ss
  ; initial_state_prop := composed_initial_state_prop Ss
  ; protocol_state_inhabited := composed_protocol_state_inhabited Ss
  ; initial_message_prop := composed_initial_message_prop Ss
  ; message_inhabited := composed_message_inhabited Ss Ssnn
  ; label_inhabited := composed_label_inhabited Ss Ssnn
  ; transition := composed_transition Ss
  ; valid := composed_valid_constrained Ss constraint
  |}.

End ComposingVLSMs.
