Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia Reals
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    Lib.Measurable
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    VLSM.DependentMessages
    .

(** * VLSM Limited Equivocation *)

Section limited_state_equivocation.

Context {message : Type}
  (index := Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  {Hmeasurable : Measurable index}
  (equivocating : set index)
  {reachable_threshold : ReachableThreshold index}
  .

Definition equivocators_limited_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs finite_index l som
  /\ (sum_weights (equivocating_indices IM index_listing (fst som'))
      <= proj1_sig threshold)%R.

Definition equivocators_limited_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_limited_equivocations_constraint.

End limited_state_equivocation.

Section limited_message_equivocation.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  {validator : Type}
  {ValMeasurable : Measurable validator}
  {ValEqDec : EqDecision validator}
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (X := free_composite_vlsm IM)
  (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  (A : validator -> index)
  (sender : message -> option validator)
  (globally_known_equivocators : composite_state IM -> set validator)
  {Hdm : DependentMessages sender A IM Hbs Hbr}
  {reachable_threshold : ReachableThreshold validator}
  .

Existing Instance X_has_been_observed_capability.

Definition known_equivocators_transition_no_equiv_prop : Prop :=
  forall
    l s iom s' oom,
    composite_transition IM l (s, iom) = (s', oom) ->
    no_additional_equivocations_constraint X l (s, iom) ->
    set_eq (globally_known_equivocators s') (globally_known_equivocators s).

Definition known_equivocators_transition_equiv_prop : Prop :=
  forall
    l s im s' oom v,
    composite_transition IM l (s, Some im) = (s', oom) ->
    ~ no_additional_equivocations_constraint X l (s, Some im) ->
    dependent_messages_global_full_node_condition finite_index s im ->
    sender im = Some v ->
    set_eq
      (globally_known_equivocators s')
      (set_add decide_eq v (globally_known_equivocators s)).

Definition globally_known_equivocators_weight
  (s : composite_state IM)
  : R
  :=
  sum_weights (globally_known_equivocators s).

Definition full_node_limited_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  dependent_messages_full_node_constraint finite_index l som /\
  let (s', om') := composite_transition IM l som in
  (globally_known_equivocators_weight s' < proj1_sig threshold)%R.

End limited_message_equivocation.