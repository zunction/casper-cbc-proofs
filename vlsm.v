Require Import List Streams.
Import ListNotations.

From Casper
Require Import ListExtras.

Class VLSM (state message label : Type) :=
  { initial_state_prop : state -> Prop
  ; protocol_state_inhabited : { p : state | initial_state_prop p}
  ; message_inhabited : { _ : message | True }
  ; label_inhabited : { _ : label | True }
  ; transition : option message -> label -> state -> (state * option message)%type
  ; valid : option message -> label -> state  -> Prop
  }.

Definition initial_state
  {state message label : Type}
  `{V : VLSM state message label}
  : Type := { i : state | initial_state_prop  i }.

Inductive
  protocol_state_prop
    {state message label}
    `{V : VLSM state message label}
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
    {state message label}
    `{V : VLSM state message label}
    : message -> Prop
    := 
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

Definition protocol_state
  {state message label}
  `{V : VLSM state message label}
  : Type := { s : state | protocol_state_prop s }.

Definition protocol_message
  {state message label}
  `{V : VLSM state message label}
  : Type := { s : message | protocol_message_prop s }.

Definition labeled_valid_transition
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
  (ps ps' : protocol_state)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_transition opm l ps ps'.

Inductive valid_trace
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
  (s s' : protocol_state)
  : Prop
  :=
  s = s' \/ valid_trace s s'.

Lemma extend_valid_reflexive_trace
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_message_production opm l s m'.

Definition valid_trace_message
  {state message label}
  `{V : VLSM state message label}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists s', valid_reflexive_trace s s' /\ valid_message_production s' m'.

Lemma valid_protocol_message
  {state message label}
  `{V : VLSM state message label}
  : forall (pm : protocol_message),
  exists (s : protocol_state),
  exists (pm' : protocol_message),
  valid_trace_message s pm' /\ proj1_sig pm = proj1_sig pm'.
Proof.
  intros. destruct pm as [m Hpm].  simpl. destruct Hpm as [s s' l m' Hps Hv Ht | s s' l m m' Hps Hpm Hv Ht ]
  ; exists (exist _ s Hps)
  ; ( exists (exist _ m' (create_protocol_message s s' l m' Hps Hv Ht))
    || exists (exist _ m' (receive_protocol_message s s' l m m' Hps Hpm Hv Ht))
    )
  ; simpl
  ; split; try reflexivity
  ; exists (exist _ s Hps)
  ; split; try (left; reflexivity)
  .
  - exists None; exists l; unfold labeled_valid_message_production; simpl; rewrite Ht; simpl; split; try assumption; reflexivity.
  - exists (Some (exist _ m Hpm)); exists l; unfold labeled_valid_message_production; simpl; rewrite Ht; simpl; split; try assumption; reflexivity.
Qed.

Inductive trace_from_to
  {state message label}
  `{V : VLSM state message label}
  : protocol_state -> protocol_state -> list protocol_state -> Prop
  :=
  | trace_from_to_one
    : forall s1 s2, valid_transition s1 s2 -> trace_from_to s1 s2 [s1; s2]
  | trace_from_to_more
    : forall s1 s3 ts s2, valid_transition s1 s2 -> trace_from_to s2 s3 ts -> trace_from_to s1 s3 (s1 :: ts)
  .

Lemma extend_trace_from_to_left
  {state message label}
  `{V : VLSM state message label}
  : forall s1 s2 s3 ls,
  trace_from_to s2 s3 ls ->
  valid_transition s1 s2 ->
  trace_from_to s1 s3 (s1 :: ls).
Proof.
  intros s1 s2 s3 ls Ht23 Hv12.
  apply trace_from_to_more with s2; assumption.
Qed.

Lemma extend_trace_from_to_right
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
  (ps : protocol_state)
  : Prop
  :=
  initial_state_prop (proj1_sig ps).

Definition protocol_finite_trace_prop
  {state message label}
  `{V : VLSM state message label}
  (ts : list protocol_state)
  : Prop
  := filtered_finite_trace initial_protocol_state_prop ts.

Definition filtered_infinite_trace
  {state message label}
  `{V : VLSM state message label}
  (subset : protocol_state -> Prop)
  (ts : Stream protocol_state)
  : Prop
  :=
  subset (hd ts) /\ infinite_trace_from (hd ts) ts.

Definition protocol_infinite_trace_prop
  {state message label}
  `{V : VLSM state message label}
  (ts : Stream protocol_state)
  : Prop
  := filtered_infinite_trace initial_protocol_state_prop ts.

Definition protocol_trace_prop
  {state message label}
  `{V : VLSM state message label}
  (t : Trace)
  : Prop
  :=
  match t with
  | Finite ts => protocol_finite_trace_prop ts
  | Infinite ts => protocol_infinite_trace_prop ts
  end.

Definition protocol_trace
  {state message label}
  `{V : VLSM state message label}
  : Type := { t : Trace | protocol_trace_prop t}.

Definition first
  {state message label}
  `{V : VLSM state message label}
  (pt : protocol_trace) : protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact h.
  - destruct t as [h t].
    exact h.
Defined.

Definition last
  {state message label}
  `{V : VLSM state message label}
  (pt : protocol_trace) : option protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact (Some (last t h)).
  - exact None.
Defined.

Lemma procotol_state_reachable
  {state message label}
  `{V : VLSM state message label}
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
  {state message label}
  `{V : VLSM state message label}
  (s : protocol_state)
  : Prop
  :=
  ~ exists s' : protocol_state, valid_transition s s'.

Definition final_state
  {state message label}
  `{V : VLSM state message label}
  : Type := { s : protocol_state | final_state_prop s}.

Definition terminating_trace
  {state message label}
  `{V : VLSM state message label}
  (t : protocol_trace)
  : Prop
  :=
  match last t with
  | Some ps => final_state_prop ps
  | None => False
  end.

Definition infinite_trace
  {state message label}
  `{V : VLSM state message label}
  (t : protocol_trace)
  : Prop
  :=
  last t = None.

Definition complete_trace
  {state message label}
  `{V : VLSM state message label}
  (t : protocol_trace)
  : Prop
  :=
  infinite_trace t \/ terminating_trace t.

