From Casper
Require Import vlsm.

Definition composed2_proto_message_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (m : message) : Prop
  :=
  (@proto_message_prop _ S1 m) \/ (@proto_message_prop _ S2 m).

Lemma composed2_proto_message_decidable
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : forall m : message, {composed2_proto_message_prop S1 S2 m} + {~ composed2_proto_message_prop S1 S2 m}.
Proof.
  intros.
  destruct (@proto_message_decidable _ S1 m) as [Hm1 | Hm1'].
  - left. left. assumption.
  - destruct (@proto_message_decidable _ S2 m) as [Hm2 | Hm2'].
    + left. right. apply Hm2.
    + right. intros H. destruct H as [H | H]; contradiction.
Qed.

Definition composed2_proto_message
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  :=
  { m : message | composed2_proto_message_prop S1 S2 m }.

Definition composed2_initial_state_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (s : (@state message S1) * (@state message S2)) : Prop
  :=
  match s with
  | (s1, s2) => initial_state_prop s1 /\ initial_state_prop s2
  end.

Definition composed2_initial_state
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  :=
  { s : (@state message S1) * (@state message S2) | composed2_initial_state_prop S1 S2 s }.

Lemma composed2_protocol_state_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : inhabited (composed2_initial_state S1 S2).
Proof.
  destruct (@protocol_state_inhabited message S1) as [s1].
  destruct (@protocol_state_inhabited message S2) as [s2].
  destruct s1 as [i1 Hi1]. destruct s2 as [i2 Hi2].
  constructor. exists (i1, i2). split; assumption.
Qed.

Definition composed2_initial_message_prop
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (m : composed2_proto_message S1 S2) : Prop.
destruct m as [m Hm].
destruct (@proto_message_decidable _ S1 m) as [H1 | _]; destruct (@proto_message_decidable _ S2 m) as [H2 | _].
- exact (initial_message_prop (exist _ m H1) \/ initial_message_prop (exist _ m H2)).
- exact (initial_message_prop (exist _ m H1)).
- exact (initial_message_prop (exist _ m H2)).
- exact False.
Defined.

Lemma composed2_message_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : inhabited (composed2_proto_message S1 S2)
  .
Proof.
  destruct (@message_inhabited message S1) as [[m Hm]].
  constructor.  exists m. left. assumption.
Qed.

Lemma composed2_label_inhabited
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : inhabited ((@label message S1) + (@label message S2)).
Proof.
  destruct (@label_inhabited message S1) as [l].
  constructor.  left.  exact l.
Qed.


Definition lift_proto_message1
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (m1 : @proto_message _ S1)
  : composed2_proto_message S1 S2.
destruct m1 as [m1 Hm1].
exists m1.
unfold composed2_proto_message_prop. left. assumption.
Defined.


Definition lift_proto_message2
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (m2 : @proto_message _ S2)
  : composed2_proto_message S1 S2.
destruct m2 as [m2 Hm2].
exists m2.
unfold composed2_proto_message_prop. right. assumption.
Defined.

Definition composed2_transition
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (l : (@label message S1) + (@label message S2))
  (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))
  : (((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))%type.
destruct som as [[s1 s2] [[m Hm]|]].
- destruct l as [l1 | l2].
  + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
    * remember (transition l1 (s1, Some (exist _ m H1))) as som'.
      exact ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som')).
    * exact ((s1, s2), None).
  + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    * remember (transition l2 (s2, Some (exist _ m H2))) as som'.
      exact ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som')).
    * exact ((s1, s2), None).
- destruct l as [l1 | l2].
  + remember (transition l1 (s1, None)) as som'.
    exact ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som')).
  + remember (transition l2 (s2, None)) as som'.
      exact ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som')).
Defined.

Definition composed2_valid
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (l : (@label message S1) + (@label message S2))
  (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))
  : Prop.
destruct som as [[s1 s2] [[m Hm]|]].
- destruct l as [l1 | l2].
  + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
    * exact (valid l1 (s1, Some (exist _ m H1))).
    * exact False.
  + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    * exact (valid l2 (s2, Some (exist _ m H2))).
    * exact False.
- destruct l as [l1 | l2].
  + exact (valid l1 (s1, None)).
  + exact (valid l2 (s2, None)).
Defined.

Lemma composed2_valid_decidable
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (l : (@label message S1) + (@label message S2))
  (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))
  : {composed2_valid S1 S2 l som} + {~composed2_valid S1 S2 l som}.
Proof.
  destruct som as [[s1 s2] [[m Hm]|]].
  - destruct l as [l1 | l2]; simpl.
    + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
      * apply valid_decidable.
      * right. intro. assumption.
    + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
      * apply valid_decidable.
      * right. intro. assumption.
  - destruct l as [l1 | l2]; simpl; apply valid_decidable.
Qed.

Definition composed2_valid_constrained
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop)
  (l : (@label message S1) + (@label message S2))
  (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))
  :=
  composed2_valid S1 S2 l som /\ constraint l som.

Lemma composed2_valid_constraint_decidable
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  (l : (@label message S1) + (@label message S2))
  (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2))
  : {composed2_valid_constrained S1 S2 constraint l som} + {~composed2_valid_constrained S1 S2 constraint l som}.
Proof.
  unfold composed2_valid_constrained.
  destruct (constraint_decidable l som) as [Hc | Hnc].
  - destruct (composed2_valid_decidable S1 S2 l som) as [Hv | Hnv].
    + left. split; try assumption.
    + right. intros [Hv _]. contradiction.
  - right. intros [_ Hc]. contradiction.
Qed.

Definition compose2_vlsm
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  : VLSM message
  :=
  {| state := (@state message S1) * (@state message S2)
  ; label := (@label message S1) + (@label message S2)
  ; proto_message_prop := composed2_proto_message_prop S1 S2
  ; proto_message_decidable := composed2_proto_message_decidable S1 S2
  ; initial_state_prop := composed2_initial_state_prop S1 S2
  ; protocol_state_inhabited := composed2_protocol_state_inhabited S1 S2
  ; initial_message_prop := composed2_initial_message_prop S1 S2
  ; message_inhabited := composed2_message_inhabited S1 S2
  ; label_inhabited := composed2_label_inhabited S1 S2
  ; transition := composed2_transition S1 S2
  ; valid := composed2_valid S1 S2
  ; valid_decidable := composed2_valid_decidable S1 S2
  |}.

Definition compose2_vlsm_constrained
  {message}
  (S1 : VLSM message)
  (S2 : VLSM message)
  (constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop)
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  : VLSM message
  :=
  {| state := (@state message S1) * (@state message S2)
  ; label := (@label message S1) + (@label message S2)
  ; proto_message_prop := composed2_proto_message_prop S1 S2
  ; proto_message_decidable := composed2_proto_message_decidable S1 S2
  ; initial_state_prop := composed2_initial_state_prop S1 S2
  ; protocol_state_inhabited := composed2_protocol_state_inhabited S1 S2
  ; initial_message_prop := composed2_initial_message_prop S1 S2
  ; message_inhabited := composed2_message_inhabited S1 S2
  ; label_inhabited := composed2_label_inhabited S1 S2
  ; transition := composed2_transition S1 S2
  ; valid := composed2_valid_constrained S1 S2 constraint
  ; valid_decidable := composed2_valid_constraint_decidable S1 S2 constraint_decidable
  |}.
