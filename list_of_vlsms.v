Require Import List.
Import ListNotations.

From Casper
Require Import vlsm.


Definition composed_list_state {message} (Ss : list (VLSM message)) : Type :=
  fold_right prod unit (List.map (@state message) Ss).

Definition composed_list_label {message} (Ss : list (VLSM message)) : Type :=
  fold_right sum Empty_set (List.map (@label message) Ss).

Definition composed_list_proto_message_prop
  {message}
  (Ss : list (VLSM message))
  (m : message) : Prop
  :=
  List.Exists (fun s => (@proto_message_prop message s m)) Ss.

Lemma composed_list_proto_message_decidable
  {message}
  (Ss : list (VLSM message))
  : forall m : message, {composed_list_proto_message_prop Ss m} + {~composed_list_proto_message_prop Ss m}.
Proof.
  intros.
  apply Exists_dec. intros s.
  apply proto_message_decidable.
Qed.

Definition composed_list_proto_message
  {message}
  (Ss : list (VLSM message))
  := { m : message | composed_list_proto_message_prop Ss m }.

Fixpoint composed_list_initial_state_prop
  {message}
  (Ss : list (VLSM message))
  : composed_list_state Ss -> Prop.
destruct Ss as [|Sh St]; unfold composed_list_state; simpl; intros.
- exact True.
- destruct X as [sh st].
  exact (@initial_state_prop _ Sh sh /\ composed_list_initial_state_prop _ St st).
Defined.

Definition composed_list_initial_state
  {message}
  (Ss : list (VLSM message))
  := { s : composed_list_state Ss | composed_list_initial_state_prop Ss s }.

Lemma composed_list_protocol_state_inhabited
  {message}
  (Ss : list (VLSM message))
  : inhabited (composed_list_initial_state Ss).
Proof.
  induction Ss as [| Sh St IHt].
  - constructor. exists tt. exact I.
  - destruct IHt as [[it Hit]].
    destruct (@protocol_state_inhabited _ Sh) as [[ih Hih]].
    constructor. exists (ih, it). split; assumption.
Qed.

Fixpoint composed_list_initial_message_prop
  {message}
  (Ss : list (VLSM message))
  : composed_list_proto_message Ss -> Prop.
destruct Ss as [|Sh St]; unfold composed_list_state; simpl; intros m.
- exact False.
- destruct m as [m Hm].
  destruct (@proto_message_decidable _ Sh m) as [Hh | _]; destruct (composed_list_proto_message_decidable St m) as [Ht | _].
  + exact (initial_message_prop (exist _ m Hh) \/ composed_list_initial_message_prop _ St (exist _ m Ht)).
  + exact (initial_message_prop (exist _ m Hh)).
  + exact (composed_list_initial_message_prop _ St (exist _ m Ht)).
  + exact False.
Defined.

Lemma composed_list_message_inhabited
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : inhabited (composed_list_proto_message Ss)
  .
Proof.
  destruct Ss as [| Sh St]; try contradiction.
  destruct (@message_inhabited _ Sh) as [[m Hm]].
  constructor.
  exists m. apply Exists_cons_hd. assumption.
Qed.

Lemma composed_list_label_inhabited
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : inhabited (composed_list_label Ss).
Proof.
  destruct Ss as [| Sh St]; try contradiction.
  destruct (@label_inhabited message Sh) as [l].
  constructor. left. exact l.
Qed.

Definition lift_proto_messageH
  {message}
  (Sh : VLSM message)
  (St : list (VLSM message))
  (mh : @proto_message _ Sh)
  : composed_list_proto_message (Sh :: St).
destruct mh as [mh Hmh].
exists mh.
apply Exists_cons_hd. assumption.
Defined.

Definition lift_proto_messageT
  {message}
  (Sh : VLSM message)
  (St : list (VLSM message))
  (mt : composed_list_proto_message St)
  : composed_list_proto_message (Sh :: St).
destruct mt as [mt Hmt].
exists mt.
apply Exists_cons_tl. assumption.
Defined.

Fixpoint composed_list_transition
  {message}
  (Ss : list (VLSM message))
  : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> composed_list_state Ss * option (composed_list_proto_message Ss).
destruct Ss as [| Sh St]; unfold composed_list_label; unfold composed_list_state; simpl
; intros l [s om].
- inversion l.
- destruct s as [sh st]. destruct om as [[m Hm]|].
  + destruct l as [lh | lt].
    * destruct (@proto_message_decidable _ Sh m) as [Hh | _].
      { remember (transition lh (sh, Some (exist _ m Hh))) as som'.
        exact ((fst som', st), option_map (lift_proto_messageH Sh St) (snd som')).
      }
      exact ((sh, st), None).
    * destruct (composed_list_proto_message_decidable St m) as [Ht | _].
      { remember (composed_list_transition _ St lt (st, Some (exist _ m Ht))) as som'.
        exact ((sh, fst som'), option_map (lift_proto_messageT Sh St) (snd som')).
      }
      exact ((sh, st), None).
  + destruct l as [lh | lt].
    * remember (transition lh (sh, None)) as som'.
      exact ((fst som', st), option_map (lift_proto_messageH Sh St) (snd som')).
    * remember (composed_list_transition _ St lt (st, None)) as som'.
      exact ((sh, fst som'), option_map (lift_proto_messageT Sh St) (snd som')).
Defined.

Fixpoint composed_list_valid
  {message}
  (Ss : list (VLSM message))
  : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop.
destruct Ss as [| Sh St]; unfold composed_list_label; unfold composed_list_state; simpl
; intros l [s om].
- inversion l.
- destruct s as [sh st]. destruct om as [[m Hm]|].
  + destruct l as [lh | lt].
    * destruct (@proto_message_decidable _ Sh m) as [Hh | _].
      { exact (valid lh (sh, Some (exist _ m Hh))). }
      exact False.
    * destruct (composed_list_proto_message_decidable St m) as [Ht | _].
      { exact (composed_list_valid _ St lt (st, Some (exist _ m Ht))). }
      exact False.
  + destruct l as [lh | lt].
    * exact (valid lh (sh, None)).
    * exact (composed_list_valid _ St lt (st, None)).
Defined.

Lemma composed_list_valid_decidable
  {message}
  (Ss : list (VLSM message))
  : forall l som, {composed_list_valid Ss l som} + {~composed_list_valid Ss l som}.
Proof.
  induction Ss as [| Sh St]; unfold composed_list_label; unfold composed_list_state; simpl; intros l [s om].
  - inversion l.
  - destruct s as [sh st]. destruct om as [[m Hm]|].
    + destruct l as [lh | lt].
      * destruct (@proto_message_decidable _ Sh m) as [Hh | _]; try (right; intro; contradiction).
        apply valid_decidable.
      * destruct (composed_list_proto_message_decidable St m) as [Ht | _]; try (right; intro; contradiction).
        apply IHSt.
    + destruct l as [lh | lt].
      * apply valid_decidable.
      * apply IHSt.
Qed.

Definition composed_list_valid_constrained
  {message}
  (Ss : list (VLSM message))
  (constraint : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop)
  (l : composed_list_label Ss)
  (som : composed_list_state Ss * option (composed_list_proto_message Ss) )
  :=
  composed_list_valid Ss l som /\ constraint l som.


Lemma composed_list_valid_constrained_decidable
  {message}
  (Ss : list (VLSM message))
  {constraint : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop}
  (constraint_decidable : forall (l : composed_list_label Ss) (som : composed_list_state Ss * option (composed_list_proto_message Ss)), {constraint l som} + {~constraint l som})
  (l : composed_list_label Ss)
  (som : composed_list_state Ss * option (composed_list_proto_message Ss) )
  : {composed_list_valid_constrained Ss constraint l som} + {~composed_list_valid_constrained Ss constraint l som}.
Proof.
  unfold composed_list_valid_constrained.
  destruct (constraint_decidable l som) as [Hc | Hnc].
  - destruct (composed_list_valid_decidable Ss l som) as [Hv | Hnv].
    + left. split; try assumption.
    + right. intros [Hv _]. contradiction.
  - right. intros [_ Hc]. contradiction.
Qed.


Definition composed_list_vlsm
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : VLSM message
  :=
  {| state := composed_list_state Ss
  ; label := composed_list_label Ss
  ; proto_message_prop := composed_list_proto_message_prop Ss
  ; proto_message_decidable := composed_list_proto_message_decidable Ss
  ; initial_state_prop := composed_list_initial_state_prop Ss
  ; protocol_state_inhabited := composed_list_protocol_state_inhabited Ss
  ; initial_message_prop := composed_list_initial_message_prop Ss
  ; message_inhabited := composed_list_message_inhabited Ss Ssnn
  ; label_inhabited := composed_list_label_inhabited Ss Ssnn
  ; transition := composed_list_transition Ss
  ; valid := composed_list_valid Ss
  ; valid_decidable := composed_list_valid_decidable Ss
  |}.

Definition composed_list_vlsm_constrained
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  (constraint : composed_list_label Ss -> composed_list_state Ss * option (composed_list_proto_message Ss) -> Prop)
  (constraint_decidable : forall (l : composed_list_label Ss) (som : composed_list_state Ss * option (composed_list_proto_message Ss)), {constraint l som} + {~constraint l som})
  : VLSM message
  :=
  {| state := composed_list_state Ss
  ; label := composed_list_label Ss
  ; proto_message_prop := composed_list_proto_message_prop Ss
  ; proto_message_decidable := composed_list_proto_message_decidable Ss
  ; initial_state_prop := composed_list_initial_state_prop Ss
  ; protocol_state_inhabited := composed_list_protocol_state_inhabited Ss
  ; initial_message_prop := composed_list_initial_message_prop Ss
  ; message_inhabited := composed_list_message_inhabited Ss Ssnn
  ; label_inhabited := composed_list_label_inhabited Ss Ssnn
  ; transition := composed_list_transition Ss
  ; valid := composed_list_valid_constrained Ss constraint
  ; valid_decidable := composed_list_valid_constrained_decidable Ss constraint_decidable
  |}.
