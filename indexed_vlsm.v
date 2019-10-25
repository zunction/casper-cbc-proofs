
Require Import ClassicalDescription.

From Casper
Require Import vlsm.

Section ComposingIndexedVLSMs.

Definition icomposed_state
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : Type
  :=
  forall i : index, (@state _ (IS i)).

Definition icomposed_label
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : Type
  := sigT (fun i => @label _ (IS i)).

Definition icomposed_proto_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (m : message)
  : Prop
  :=
  exists i : index, @proto_message_prop message (IS i) m.

Lemma icomposed_proto_message_decidable
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : forall m : message, {icomposed_proto_message_prop IS m} + {~icomposed_proto_message_prop IS m}.
Proof.
  intros.
  apply excluded_middle_informative.
Qed.

Definition icomposed_proto_message
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  := { m : message | icomposed_proto_message_prop IS m }.

Definition icomposed_initial_state_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (s : icomposed_state IS)
  : Prop
  :=
  forall i : index, @initial_state_prop _ (IS i) (s i).

Require Import ClassicalChoice ChoiceFacts.

Print DependentFunctionalChoice_on.

Lemma icomposed_protocol_state_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : exists s : icomposed_state IS, icomposed_initial_state_prop IS s.
Proof.
  unfold icomposed_state.
  unfold icomposed_initial_state_prop.
  assert (Hchoice : forall i : index, exists s : (@state _ (IS i)),
    @initial_state_prop _ (IS i) s).
  { intros. destruct (@protocol_state_inhabited _ (IS i)) as [s His].
    exists s. assumption.
  }
  specialize (non_dep_dep_functional_choice choice); intros depFunChoice.
  specialize (depFunChoice index (fun i => (@state _ (IS i)))).
  specialize (depFunChoice (fun i => @initial_state_prop _ (IS i))).
  simpl in depFunChoice.
  specialize (depFunChoice Hchoice). assumption.
Qed.

Definition icomposed_initial_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (m : icomposed_proto_message IS)
  : Prop
  :=
  exists (i : index) (mi : @initial_message _ (IS i)), proj1_sig (proj1_sig mi) = proj1_sig m.


Lemma inhabited_exists : forall A, inhabited A <-> exists x : A, True.
Proof.
  intros; split; intros.
  - destruct H. exists X. exact I.
  - destruct H as [a _]. constructor. exact a.
Qed.

Lemma icomposed_message_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (icomposed_proto_message IS)
  .
Proof.
  unfold icomposed_proto_message. unfold icomposed_proto_message_prop.
  destruct Hi as [i]. specialize (@message_inhabited _ (IS i)).
  intros. destruct X as [m _]. destruct m as [m Hpm].
  split. exists m. exists i. assumption.
Qed.

Lemma composed_label_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (icomposed_label IS).
Proof.
  unfold icomposed_label.
  destruct Hi as [i].
  destruct (@label_inhabited message (IS i)) as [l _].
  constructor.
  exists i. exact l.
Qed.

Definition lift_proto_messageI
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (i : index)
  (mi : @proto_message _ (IS i))
  : icomposed_proto_message IS.
destruct mi as [m Hm].
exists m. exists i. assumption.
Defined.

Definition icomposed_transition
  {index : Set} {message : Type} 
  (IS : index -> VLSM message)
  (l : icomposed_label IS)
  (som : icomposed_state IS * option (icomposed_proto_message IS))
  : icomposed_state IS * option (icomposed_proto_message IS).
destruct som as [s om].
destruct l as [i li].
destruct om as [[m _]|].
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + remember (transition li (s i, Some (exist _ m Hi))) as som'.
    destruct som' as [si' om'].
    split.
    * intros j. 
destruct Ss as [| Sh St]; unfold composed_label; unfold composed_state; simpl
; intros l [s om].
- inversion l.
- destruct s as [sh st]. destruct om as [[m Hm]|].
  + destruct l as [lh | lt].
    * destruct (@proto_message_decidable _ Sh m) as [Hh | _].
      { remember (transition lh (sh, Some (exist _ m Hh))) as som'.
        exact ((fst som', st), option_map (lift_proto_messageH Sh St) (snd som')).
      }
      exact ((sh, st), None).
    * destruct (composed_proto_message_decidable St m) as [Ht | _].
      { remember (composed_transition _ St lt (st, Some (exist _ m Ht))) as som'.
        exact ((sh, fst som'), option_map (lift_proto_messageT Sh St) (snd som')).
      }
      exact ((sh, st), None).
  + destruct l as [lh | lt].
    * remember (transition lh (sh, None)) as som'.
      exact ((fst som', st), option_map (lift_proto_messageH Sh St) (snd som')).
    * remember (composed_transition _ St lt (st, None)) as som'.
      exact ((sh, fst som'), option_map (lift_proto_messageT Sh St) (snd som')).
Defined.

Fixpoint composed_valid
  {message}
  (Ss : list (VLSM message))
  : composed_label Ss -> composed_state Ss * option (composed_proto_message Ss) -> Prop.
destruct Ss as [| Sh St]; unfold composed_label; unfold composed_state; simpl
; intros l [s om].
- inversion l.
- destruct s as [sh st]. destruct om as [[m Hm]|].
  + destruct l as [lh | lt].
    * destruct (@proto_message_decidable _ Sh m) as [Hh | _].
      { exact (valid lh (sh, Some (exist _ m Hh))). }
      exact False.
    * destruct (composed_proto_message_decidable St m) as [Ht | _].
      { exact (composed_valid _ St lt (st, Some (exist _ m Ht))). }
      exact False.
  + destruct l as [lh | lt].
    * exact (valid lh (sh, None)).
    * exact (composed_valid _ St lt (st, None)).
Defined.

Definition composed_valid_constrained
  {message}
  (Ss : list (VLSM message))
  (constraint : composed_label Ss -> composed_state Ss * option (composed_proto_message Ss) -> Prop)
  (l : composed_label Ss)
  (som : composed_state Ss * option (composed_proto_message Ss) )
  :=
  composed_valid Ss l som /\ constraint l som.

Definition composed_vlsm
  {message}
  (Ss : list (VLSM message))
  (Ssnn : Ss <> [])
  : VLSM message
  :=
  {| state := composed_state Ss
  ; label := composed_label Ss
  ; proto_message_prop := composed_proto_message_prop Ss
  ; proto_message_decidable := composed_proto_message_decidable Ss
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
  (constraint : composed_label Ss -> composed_state Ss * option (composed_proto_message Ss) -> Prop)
  : VLSM message
  :=
  {| state := composed_state Ss
  ; label := composed_label Ss
  ; proto_message_prop := composed_proto_message_prop Ss
  ; proto_message_decidable := composed_proto_message_decidable Ss
  ; initial_state_prop := composed_initial_state_prop Ss
  ; protocol_state_inhabited := composed_protocol_state_inhabited Ss
  ; initial_message_prop := composed_initial_message_prop Ss
  ; message_inhabited := composed_message_inhabited Ss Ssnn
  ; label_inhabited := composed_label_inhabited Ss Ssnn
  ; transition := composed_transition Ss
  ; valid := composed_valid_constrained Ss constraint
  |}.

End ComposingVLSMs.


