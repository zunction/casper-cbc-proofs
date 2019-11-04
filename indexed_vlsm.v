
Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
Require Import vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
*)

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

Definition icomposed_initial_state
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  := { s : icomposed_state IS | icomposed_initial_state_prop IS s }.

Lemma icomposed_protocol_state_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : inhabited (icomposed_initial_state IS).
Proof.
  unfold icomposed_initial_state. unfold icomposed_state. unfold icomposed_initial_state_prop.
  assert (Hchoice : exists s : forall i : index, @state _ (IS i), forall i : index, @initial_state_prop _ (IS i) (s i)).
  { apply (non_dep_dep_functional_choice choice). simpl.
    intros i. destruct (@protocol_state_inhabited _ (IS i)) as [[s His]].
    exists s. assumption.
  }
  destruct Hchoice as [s His].
  constructor. exists s. assumption.
Qed.

Definition icomposed_initial_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (m : icomposed_proto_message IS)
  : Prop
  :=
  exists (i : index) (mi : @initial_message _ (IS i)), proj1_sig (proj1_sig mi) = proj1_sig m.


Lemma icomposed_message_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (icomposed_proto_message IS)
  .
Proof.
  unfold icomposed_proto_message. unfold icomposed_proto_message_prop.
  destruct Hi as [i]. destruct (@message_inhabited _ (IS i)) as [[m Hpm]].
  constructor. exists m. exists i. assumption.
Qed.

Lemma icomposed_label_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (icomposed_label IS).
Proof.
  unfold icomposed_label.
  destruct Hi as [i].
  destruct (@label_inhabited message (IS i)) as [l].
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

Class EqDec X :=
  eq_dec : forall x y : X, {x = y} + {x <> y}.

Definition icomposed_transition
  {index : Set} {message : Type} `{Heqd : EqDec index}
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
    * intros j. destruct (eq_dec j i).
      { subst. exact si' . }
      exact (s j).
    * exact (option_map (lift_proto_messageI IS i) om').
  + exact (s, None).
- remember (transition li (s i, None)) as som'.
    destruct som' as [si' om'].
    split.
    * intros j. destruct (eq_dec j i).
      { subst. exact si'. }
      exact (s j).
    * exact (option_map (lift_proto_messageI IS i) om').
Defined.

Definition icomposed_valid
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (l : icomposed_label IS)
  (som : icomposed_state IS * option (icomposed_proto_message IS))
  : Prop.
destruct som as [s om].
destruct l as [i li].
destruct om as [[m _]|].
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + exact (valid li (s i, Some (exist _ m Hi))).
  + exact False.
- exact (valid li (s i, None)).
Defined.

Definition composed_valid_constrained
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (l : icomposed_label IS)
  (som : icomposed_state IS * option (icomposed_proto_message IS))
  :=
  icomposed_valid IS l som /\ constraint l som.


(* Free VLSM composition *)

Definition composed_vlsm
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : VLSM message
  :=
  {| state := icomposed_state IS
  ; label := icomposed_label IS
  ; proto_message_prop := icomposed_proto_message_prop IS
  ; proto_message_decidable := icomposed_proto_message_decidable IS
  ; initial_state_prop := icomposed_initial_state_prop IS
  ; protocol_state_inhabited := icomposed_protocol_state_inhabited IS
  ; initial_message_prop := icomposed_initial_message_prop IS
  ; message_inhabited := icomposed_message_inhabited IS Hi
  ; label_inhabited := icomposed_label_inhabited IS Hi
  ; transition := icomposed_transition IS
  ; valid := icomposed_valid IS
  |}.


(* Constrained VLSM composition *)

Definition composed_vlsm_constrained
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  : VLSM message
  :=
  {| state := icomposed_state IS
  ; label := icomposed_label IS
  ; proto_message_prop := icomposed_proto_message_prop IS
  ; proto_message_decidable := icomposed_proto_message_decidable IS
  ; initial_state_prop := icomposed_initial_state_prop IS
  ; protocol_state_inhabited := icomposed_protocol_state_inhabited IS
  ; initial_message_prop := icomposed_initial_message_prop IS
  ; message_inhabited := icomposed_message_inhabited IS Hi
  ; label_inhabited := icomposed_label_inhabited IS Hi
  ; transition := icomposed_transition IS
  ; valid := composed_valid_constrained IS constraint
  |}.

Class composed_vlsm_class (message : Type) `{VLSM message} :=
  { index : Set
  ; istate : state -> index -> Type
  ; ilabel : label -> index
  }.

Definition composed_vlsm_istate
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  (s : @state message (composed_vlsm IS Hi))
  (i : oindex)
  : Type
  := @state message (IS i).

Definition composed_vlsm_ilabel
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  (s : @label message (composed_vlsm IS Hi))
  : oindex
  :=
  projT1 s.

Instance composed_vlsm_class_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> VLSM message}
  {Hi : inhabited oindex}
  : @composed_vlsm_class message (composed_vlsm IS Hi)
  :=
  { index := oindex
  ; istate := composed_vlsm_istate
  ; ilabel := composed_vlsm_ilabel
  }.
