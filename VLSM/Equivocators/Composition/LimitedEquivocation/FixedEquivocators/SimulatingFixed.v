Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia
  Program Program.Equality
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation VLSM.SubProjectionTraces
    VLSM.ProjectionTraces
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    VLSM.Equivocators.Composition.Projections
    VLSM.Equivocators.Composition.SimulatingFree.SimulatingFree
    VLSM.Equivocators.Composition.LimitedEquivocation.FixedEquivocation
    .


Section from_nodes_to_equivocators.
Context
  {message : Type}
  `{EqDecision message}
  (index : Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM Hbs finite_index equivocating Hi0_equiv)
  (X : VLSM message := fixed_equivocation_vlsm_composition IM Hbs Hbr equivocating Hi0_equiv finite_index)
  (equivocators_free_Hbs := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (FreeE : VLSM message := free_composite_vlsm (equivocator_IM IM))
  (FreeE_has_been_sent_capability : has_been_sent_capability FreeE := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  (comopsite_initial_decidable := composite_decidable_initial_message IM finite_index Hdec_init)
  (Free := free_composite_vlsm IM)
  (Free_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (Free_has_been_received_capability : has_been_received_capability Free := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (Free_has_been_observed_capability : has_been_observed_capability Free := has_been_observed_capability_from_sent_received Free)
  (Free_no_additional_equivocation_decidable := no_additional_equivocations_dec Free comopsite_initial_decidable)
  (index_equivocating_prop : index -> Prop := sub_index_prop equivocating)
  (equivocating_index : Type := sub_index equivocating)
  (equivocating_i0 : Inhabited equivocating_index := sub_index_i0 equivocating Hi0_equiv)
  (equivocating_IM := sub_IM IM equivocating)
  (equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating)
  (free_equivocating_vlsm_composition : VLSM message := free_composite_vlsm equivocating_IM)
  (sub_equivocator_IM := sub_IM (equivocator_IM IM) equivocating)
  .

Existing Instance i0.
Existing Instance equivocators_free_Hbs.
Existing Instance Free_has_been_observed_capability.
Existing Instance Free_has_been_sent_capability.
Existing Instance equivocating_i0.
Existing Instance equivocating_index_eq_dec.

Definition lift_label_to_equivocators
  (l : composite_label IM)
  (d : MachineDescriptor (IM (projT1 l)))
  : composite_label (equivocator_IM IM)
  := existT _ (projT1 l) (projT2 l, d).

Lemma fixed_equivocators_protocol_trace_project_rev
  (isX : vstate X)
  (trX : list (vtransition_item X))
  (HtrX : finite_protocol_trace X isX trX)
  : exists
    (is : composite_state (equivocator_IM IM)),
    equivocators_state_project IM (zero_descriptor _) is = isX /\
    exists
      (tr : list (composite_transition_item (equivocator_IM IM)))
      (eqv_descriptors : equivocator_descriptors IM),
      let lst_tr := last (map destination tr) is in
      not_equivocating_equivocator_descriptors IM eqv_descriptors lst_tr /\
      equivocators_trace_project IM eqv_descriptors tr = Some (trX, zero_descriptor _) /\
      finite_protocol_trace XE is tr.
Proof.
  destruct HtrX as [HtrX HisX].
  specialize (lift_initial_to_equivocators_state IM Hbs finite_index isX HisX) as His.
  remember (lift_to_equivocators_state IM isX) as is.
  assert (Hisp : protocol_state_prop XE is).
  { apply initial_is_protocol. assumption. }
  exists is.
  split; [subst; reflexivity|].
  induction trX using rev_ind.
  - exists []. simpl.
    exists (zero_descriptor IM).
    split; [apply (zero_descriptor_not_equivocating IM is)|].
    split; [reflexivity|].
    split; [|assumption].
    constructor. assumption.
  - apply finite_protocol_trace_from_app_iff in HtrX.
    destruct HtrX as [HtrX HxX].
    specialize (IHtrX HtrX).
    destruct IHtrX as [tr [eqv_descriptors [Hdescriptors [Hpr_tr [Htr _]]]]].
    pose (ilx := projT1 (l x)).
    specialize (Hdescriptors ilx) as Hdescriptors_ilx.
    destruct (eqv_descriptors ilx) as [sn | di df] eqn:Heq_eqv_descriptors_ilx
    ; [contradiction|].
    pose (lx := lift_label_to_equivocators (l x) (eqv_descriptors ilx)).
    apply first_transition_valid in HxX.
    destruct HxX as [[Hlst_trX [HinputX [Hv Hfixed]]] HtX].
    apply not_equivocating_equivocator_descriptors_proper in Hdescriptors as Hdescriptors_proper.
    specialize
      (preloaded_equivocators_protocol_trace_from_project IM eqv_descriptors is tr
        Hdescriptors_proper) as Hpre.
    spec Hpre.
    { revert Htr. apply VLSM_incl_finite_protocol_trace_from.
      apply VLSM_incl_trans with (machine (free_composite_vlsm (equivocator_IM IM))).
      - apply equivocators_fixed_equivocations_vlsm_incl_free.
      - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    }
    destruct Hpre as [_trX [_initial_descriptors [_Hpr_tr [_ Hpr_lst]]]].
    rewrite Hpr_tr in _Hpr_tr. inversion _Hpr_tr. subst _trX _initial_descriptors.
    clear _Hpr_tr.
    replace (equivocators_state_project IM (zero_descriptor IM) is) with isX in Hpr_lst
      by (subst is; reflexivity).
(*
    
    rewrite Heqis in Hpr_lst at 2. simpl in Hpr_lst.
    destruct Hfixed as [Hno_equiv | Hfixed].
    + match type of Hdescriptors with
      | not_equivocating_equivocator_descriptors _ _ ?l => remember l as lst
      end.
    destruct (composite_transition (equivocator_IM IM) lx (lst, input x)) as (s', om') eqn:Ht.
    exists (tr ++ [{| l := lx; input := input x; output := output x; destination := s' |}]).
    exists eqv_descriptors.
    subst lx. destruct x. destruct l as [i l]. rewrite Heq_eqv_descriptors_ilx in Ht.  simpl in *.
    unfold vtransition in Ht. simpl in Ht.
    destruct x. simpl in *
    unfold fixed_equivocation_constraint, no_additional_equivocations_constraint in Hfixed.
    unfold no_ad
  specialize (seeded_equivocators_protocol_trace_project_rev IM Hbs _ finite_index).
*)  
Admitted.

End from_nodes_to_equivocators.