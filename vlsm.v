Require Import List Streams.
Import ListNotations.

Class VLSM :=
  { state : Type
  ; initial_state_prop : state -> Prop
  ; protocol_state_inhabited : { p : state | initial_state_prop p}
  ; message : Type
  ; message_inhabited : { _ : message | True }
  ; label : Type
  ; label_inhabited : { _ : label | True }
  ; transition : option message -> label -> state -> (state * option message)%type
  ; valid : option message -> label -> state  -> Prop
  }.

Definition initial_state `{VLSM} : Type := { i : state | initial_state_prop i }.

Inductive
  protocol_state_prop
  `{VLSM}
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
  `{VLSM}
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

Definition protocol_state `{VLSM} : Type := { s : state | protocol_state_prop s }.
Definition protocol_message `{VLSM} : Type := { s : message | protocol_message_prop s }.

Definition labeled_valid_transition
  `{VLSM}
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
  `{VLSM}
  (ps ps' : protocol_state)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_transition opm l ps ps'.

Inductive valid_trace `{VLSM} : protocol_state -> protocol_state -> Prop :=
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

Lemma extend_valid_trace `{VLSM}
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
 `{VLSM}
  (s s' : protocol_state)
  : Prop
  :=
  s = s' \/ valid_trace s s'.

Lemma extend_valid_reflexive_trace `{VLSM}
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
  `{VLSM}
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
  `{VLSM}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_message_production opm l s m'.

Definition valid_trace_message
 `{VLSM}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists s', valid_reflexive_trace s s' /\ valid_message_production s' m'.

Lemma valid_protocol_message
 `{VLSM}
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
  `{VLSM}
  : protocol_state -> protocol_state -> list protocol_state -> Prop
  :=
  | filtered_trace_one
    : forall s1 s2, valid_transition s1 s2 -> trace_from_to s1 s2 [s1; s2]
  | filtered_trace_more
    : forall s1 s3 ts s2, valid_transition s1 s2 -> trace_from_to s2 s3 ts -> trace_from_to s1 s3 (s1 :: ts)
  .

CoInductive infinite_trace_from
  `{VLSM}
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
  `{VLSM}
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
  `{VLSM}
  (ps : protocol_state)
  : Prop
  :=
  initial_state_prop (proj1_sig ps).

Definition protocol_finite_trace_prop
  `{VLSM}
  (ts : list protocol_state)
  : Prop
  := filtered_finite_trace initial_protocol_state_prop ts.

Definition filtered_infinite_trace
  `{VLSM}
  (subset : protocol_state -> Prop)
  (ts : Stream protocol_state)
  : Prop
  :=
  subset (hd ts) /\ infinite_trace_from (hd ts) ts.

Definition protocol_infinite_trace_prop
  `{VLSM}
  (ts : Stream protocol_state)
  : Prop
  := filtered_infinite_trace initial_protocol_state_prop ts.

Definition protocol_trace_prop
  `{VLSM}
  (t : Trace)
  : Prop
  :=
  match t with
  | Finite ts => protocol_finite_trace_prop ts
  | Infinite ts => protocol_infinite_trace_prop ts
  end.

Definition protocol_trace `{VLSM} : Type := { t : Trace | protocol_trace_prop t}.

Definition first `{VLSM} (pt : protocol_trace) : protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact h.
  - destruct t as [h t].
    exact h.
Defined.

Definition last `{VLSM}  (pt : protocol_trace) : option protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact (Some (last t h)).
  - exact None.
Defined.

Lemma procotol_state_reachable
  `{VLSM}
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
  - right. destruct IHps.
    + remember (exist _ s' (next_protocol_state_no_message s s' l om' Hps Hv Ht)) as ps'.
      remember (exist _ s H0) as is.
      remember (exist _ s (initial_protocol_state (exist _ s H0))) as ps.
      assert (Hips : initial_protocol_state_prop ps)
        by (subst; unfold initial_protocol_state_prop; assumption).
      assert (Hvt : valid_transition ps ps').
      { subst; exists None. exists l. unfold labeled_valid_transition. simpl. split; try assumption. rewrite Ht. reflexivity. }
      assert (Pt : trace_from_to ps ps' [ps; ps']) by (apply filtered_trace_one; assumption).
      assert (Hpt : protocol_trace_prop (Finite [ps; ps']))
        by (split; assumption).
      exists (exist _ (Finite [ps; ps']) Hpt). exists ps'. subst. simpl. split; reflexivity.
    + destruct H0 as [pt [ps' [Heq_last Heq_s]]].
      destruct pt as [t Hpt].
      destruct t as [t | t].
      * unfold protocol_trace_prop in Hpt. unfold protocol_finite_trace_prop in Hpt.
        unfold filtered_finite_trace in Hpt.
        destruct t as [|h t]; try contradiction.
        destruct t as [|h' t]; try contradiction.
        destruct Hpt as [Hhi Htrace].
        

      * simpl in Heq_last. inversion Heq_last.

destruct IHps as [is [ps [Htrace Heq]]].
    exists is.
    remember (exist _ s' (next_protocol_state_no_message s s' l om' Hps Hv Ht)) as ps'.
    assert (Hvt : valid_transition ps ps').
    { subst; exists None. exists l. unfold labeled_valid_transition. simpl. split; try assumption. rewrite Ht. reflexivity. }
    exists ps'.
    split ; try (subst; reflexivity).
    right. apply extend_valid_reflexive_trace with ps; assumption.
  - destruct IHps as [is [ps [Htrace Heq]]].
    exists is.
    remember (exist _ s' (next_protocol_state_with_message s s' l m om' Hps Hpm Hv Ht)) as ps'.
    assert (Hvt : valid_transition ps ps').
    { subst; exists (Some (exist _ m Hpm)). exists l. unfold labeled_valid_transition. simpl. split; try assumption. rewrite Ht. reflexivity. }
    exists ps'.
    split ; try (subst; reflexivity).
    right. apply extend_valid_reflexive_trace with ps; assumption.
Qed.

Definition final_state_prop
  `{VLSM}
  (s : protocol_state)
  : Prop
  :=
  ~ exists s' : protocol_state, valid_transition s s'.

Definition final_state `{VLSM} : Type := { s : protocol_state | final_state_prop s}.

Definition filtered_terminating_trace
  `{VLSM}
  (subset : protocol_state -> Prop)
  (i : protocol_state)
  (f : final_state)
  (t : list protocol_state)
  : Prop
  :=
  filtered_trace_from_to subset i (proj1_sig f) t.


(*
Inductive in_state `{VLSM} : state -> list protocol_message -> Prop :=
  | initial_empty
    : forall s : state,
      initial s -> message_list_prop' s []
  | lambda_transition
    : forall (s s' : state) (l : label) (msgs : list protocol_message),
    valid None l s ->
    transition None l s = (s', None) ->
    message_list_prop' s msgs ->
    message_list_prop' s' msgs
  | create_message
    : forall (s s' : state) (l : label) (m' : message) (msgs : list protocol_message)
    (ps : protocol_state_prop s)
    (v : valid None l s)
    (e : transition None l s = (s', Some m')),
    message_list_prop' s msgs ->
    message_list_prop'
      s'
      ((exist _ m' (create_protocol_message s s' l m' ps v e)) :: msgs)
  | receive_message
    : forall (s s' : state) (l : label) (m : protocol_message) (v : valid (Some (proj1_sig m)) l s)
    (e : transition (Some (proj1_sig m)) l s = (s', None)) (msgs : list protocol_message),
    message_list_prop' s msgs ->
    message_list_prop' s'  (m :: msgs)
  | receive_create_message
    : forall (s s' : state) (l : label) (m : protocol_message) (m' : message)
    (ps : protocol_state_prop s)
    (v : valid (Some (proj1_sig m)) l s) 
    (e : transition (Some (proj1_sig m)) l s = (s', Some m')) (msgs : list protocol_message),
    message_list_prop' s msgs ->
    message_list_prop'
      s'
      ((exist _ m' (receive_protocol_message s s' l (proj1_sig m) m' ps (proj2_sig m) v e)) :: m :: msgs)
  .

Lemma message_list_functional
  `{VLSM}
  : forall (s : state) (PS : protocol_state_prop s),
  exists! msgs : list protocol_message, message_list_prop' s msgs.
Proof.
  intros. 
  induction PS; rewrite <- unique_existence; split.
  - exists []. constructor; assumption.
  - intros x y Hx Hy.
    specialize (initial_prop s H0) as Hinit.
    inversion Hx; inversion Hy; subst; try reflexivity.
    + specialize (Hinit None l s1 None). contradiction.
    + specialize (Hinit None l s1 (Some m')). contradiction.
    + specialize (Hinit (Some (proj1_sig m)) l s1 None). contradiction.
    + specialize (Hinit (Some (proj1_sig m)) l s1 (Some m')). contradiction.
Qed.

Inductive message_list_prop `{VLSM} : protocol_state -> list protocol_message -> Prop :=
  | initial_empty
    : forall (s : state) (i : initial s),
    message_list_prop (exist _ s (initial_protocol_state s i)) []
  | lambda_transition
    : forall (p : protocol_state) (l : label) (v : valid None l (proj1_sig p)) (s:state)
      (e : transition None l (proj1_sig p) = (s, None)) (msgs : list protocol_message),
    message_list_prop p msgs ->
    message_list_prop (exist _ s (next_protocol_state_no_message (proj1_sig p) s l None (proj2_sig p) v e)) msgs
  | create_message
    : forall (p : protocol_state) (l : label) (v : valid None l (proj1_sig p)) (s:state) (m : message)
      (e : transition None l (proj1_sig p) = (s, Some m)) (msgs : list protocol_message),
    message_list_prop p msgs ->
    message_list_prop
      (exist _ s (next_protocol_state_no_message (proj1_sig p) s l (Some m) (proj2_sig p) v e))
      ((exist _ m (create_protocol_message (proj1_sig p) s l m (proj2_sig p) v e)) :: msgs)
  | receive_message
    : forall (p : protocol_state) (l : label) (m : protocol_message) (v : valid (Some (proj1_sig m)) l (proj1_sig p)) (s:state)
      (e : transition (Some (proj1_sig m)) l (proj1_sig p) = (s, None)) (msgs : list protocol_message),
    message_list_prop p msgs ->
    message_list_prop
      (exist _ s (next_protocol_state_with_message (proj1_sig p) s l (proj1_sig m) None (proj2_sig p) (proj2_sig m) v e))
      (m :: msgs)
  | receive_create_message
    : forall (p : protocol_state) (l : label) (m : protocol_message) (v : valid (Some (proj1_sig m)) l (proj1_sig p)) (s':state) (m' : message)
      (e : transition (Some (proj1_sig m)) l (proj1_sig p) = (s', Some m')) (msgs : list protocol_message),
      message_list_prop p msgs ->
    message_list_prop
      (exist _ s' (next_protocol_state_with_message (proj1_sig p) s' l (proj1_sig m) (Some m') (proj2_sig p) (proj2_sig m) v e))
      ((exist _ m' (receive_protocol_message (proj1_sig p) s' l (proj1_sig m) m' (proj2_sig p) (proj2_sig m) v e)) :: m :: msgs)
  .
*)