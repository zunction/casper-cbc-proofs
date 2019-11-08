
Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
Require Import vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
*)

Definition indexed_state
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : Type
  :=
  forall i : index, (@state _ (IS i)).

Definition indexed_label
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : Type
  := sigT (fun i => @label _ (IS i)).

Definition indexed_proto_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (m : message)
  : Prop
  :=
  exists i : index, @proto_message_prop message (IS i) m.

Lemma indexed_proto_message_decidable
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : forall m : message, {indexed_proto_message_prop IS m} + {~indexed_proto_message_prop IS m}.
Proof.
  intros.
  apply excluded_middle_informative.
Qed.

Definition indexed_proto_message
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  := { m : message | indexed_proto_message_prop IS m }.

Definition indexed_initial_state_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (s : indexed_state IS)
  : Prop
  :=
  forall i : index, @initial_state_prop _ (IS i) (s i).

Definition indexed_initial_state
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  := { s : indexed_state IS | indexed_initial_state_prop IS s }.

Lemma indexed_protocol_state_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  : inhabited (indexed_initial_state IS).
Proof.
  unfold indexed_initial_state. unfold indexed_state. unfold indexed_initial_state_prop.
  assert (Hchoice : exists s : forall i : index, @state _ (IS i), forall i : index, @initial_state_prop _ (IS i) (s i)).
  { apply (non_dep_dep_functional_choice choice). simpl.
    intros i. destruct (@protocol_state_inhabited _ (IS i)) as [[s His]].
    exists s. assumption.
  }
  destruct Hchoice as [s His].
  constructor. exists s. assumption.
Qed.

Definition indexed_initial_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (m : indexed_proto_message IS)
  : Prop
  :=
  exists (i : index) (mi : @initial_message _ (IS i)), proj1_sig (proj1_sig mi) = proj1_sig m.


Lemma indexed_message_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (indexed_proto_message IS)
  .
Proof.
  unfold indexed_proto_message. unfold indexed_proto_message_prop.
  destruct Hi as [i]. destruct (@message_inhabited _ (IS i)) as [[m Hpm]].
  constructor. exists m. exists i. assumption.
Qed.

Lemma indexed_label_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : inhabited (indexed_label IS).
Proof.
  unfold indexed_label.
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
  : indexed_proto_message IS.
destruct mi as [m Hm].
exists m. exists i. assumption.
Defined.

Class EqDec X :=
  eq_dec : forall x y : X, {x = y} + {x <> y}.

Definition indexed_transition
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : indexed_state IS * option (indexed_proto_message IS).
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

Definition indexed_valid
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : Prop.
destruct som as [s om].
destruct l as [i li].
destruct om as [[m _]|].
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + exact (valid li (s i, Some (exist _ m Hi))).
  + exact False.
- exact (valid li (s i, None)).
Defined.


Definition indexed_valid_constrained
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  :=
  indexed_valid IS l som /\ constraint l som.


(* Free VLSM composition *)

Definition indexed_vlsm
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  : VLSM message
  :=
  {| state := indexed_state IS
  ; label := indexed_label IS
  ; proto_message_prop := indexed_proto_message_prop IS
  ; proto_message_decidable := indexed_proto_message_decidable IS
  ; initial_state_prop := indexed_initial_state_prop IS
  ; protocol_state_inhabited := indexed_protocol_state_inhabited IS
  ; initial_message_prop := indexed_initial_message_prop IS
  ; message_inhabited := indexed_message_inhabited IS Hi
  ; label_inhabited := indexed_label_inhabited IS Hi
  ; transition := indexed_transition IS
  ; valid := indexed_valid IS
  |}.

(* 
Lemma indexed_valid_decidable
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)),
  {indexed_valid IS l som} + {~indexed_valid IS l som}.
Proof.
  destruct som as [s om].
  destruct l as [i li]; simpl.
  destruct om as [[m _]|]; simpl.
  - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
    + apply valid_decidable.
    + right; intro; contradiction.
  - apply valid_decidable.
Qed.

  ; valid_decidable := indexed_valid_decidable IS

 *)

(* Constrained VLSM composition *)

Definition indexed_vlsm_constrained
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (Hi : inhabited index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : VLSM message
  :=
  {| state := indexed_state IS
  ; label := indexed_label IS
  ; proto_message_prop := indexed_proto_message_prop IS
  ; proto_message_decidable := indexed_proto_message_decidable IS
  ; initial_state_prop := indexed_initial_state_prop IS
  ; protocol_state_inhabited := indexed_protocol_state_inhabited IS
  ; initial_message_prop := indexed_initial_message_prop IS
  ; message_inhabited := indexed_message_inhabited IS Hi
  ; label_inhabited := indexed_label_inhabited IS Hi
  ; transition := indexed_transition IS
  ; valid := indexed_valid_constrained IS constraint
  |}.

(* 

Definition indexed_valid_constrained_decidable
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)),
  {indexed_valid_constrained IS constraint l som} + {~indexed_valid_constrained IS constraint l som}.
Proof.
  intros.
  unfold indexed_valid_constrained.
  destruct (constraint_decidable l som) as [Hc | Hnc].
  - destruct (indexed_valid_decidable IS l som) as [Hv | Hnv].
    + left. split; try assumption.
    + right. intros [Hv _]. contradiction.
  - right. intros [_ Hc]. contradiction.
Qed.

  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  ; valid_decidable := indexed_valid_constrained_decidable IS constraint_decidable

 *)