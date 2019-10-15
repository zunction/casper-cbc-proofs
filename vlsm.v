Require Import List.
Import ListNotations.

Class VLSM :=
  { state : Type
  ; initial : state -> Prop
  ; protocol_state_inhabited : { p : state | initial p}
  ; message : Type
  ; message_inhabited : { _ : message | True }
  ; label : Type
  ; label_inhabited : { _ : label | True }
  ; transition : option message -> label -> state -> (state * option message)%type
  ; valid : option message -> label -> state  -> Prop
  }.


Inductive
  protocol_state_prop
  `{VLSM}
  : state -> Prop
  := 
    | initial_protocol_state
      : forall s : state,
      initial s ->
      protocol_state_prop s
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
