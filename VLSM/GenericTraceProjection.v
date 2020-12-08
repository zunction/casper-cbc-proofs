Require Import List.

From CasperCBC
  Require Import
  Lib.Preamble
  VLSM.Common
  VLSM.Composition
  .

(**
   This module defines a more general approach to
   VLSM projection, based on an extensional definition
   of when the state type of one VLSM is part of the
   state type of another, and of when transitions can
   be projected or lifted between VLSMs with related
   states.

   This allows a generic definition of the projection
   operation and validity lemmas that separate the
   generic parts about iterating a projection over
   every step from the VLSM-specific reasoning about
   projecting individual transitions.

   In constrast, VLSM.ProjectionTypes only works if
   the larger VLSM uses [composite_state] as the state type,
   and the target is a single component, while this
   approach can be instantiated for projecting on a subset
   or permutation of indices, reassociating nested
   composition of VLSMs, etc.

   Currently this only defines projections from the
   larger VLSM to the smaller.
   It would be easy to add injections, taking an assumption
   mostly like [transition_projection_prop] except that
   validity in the smaller vlsm implies validity in the larger.

   I don't know if this extends nicely to <<equivocator_vlsm>>,
   where the set of <<MachineDescriptor>>s that are valid for
   indexing into an <<equivocator_vlsm>> state can change
   as execution proceeds.
 *)

Set Implicit Arguments.
Record vlsm_component_ops {message} (A B:VLSM_type message) :=
  {get_component : @state _ B -> @state _ A;
   set_component: @state _ B -> @state _ A -> @state _ B;
   split_label : @label _ B -> option (@label _ A)}.
Record vlsm_component_props {message} {A B:VLSM message} (ops: vlsm_component_ops (type A) (type B)) :=
  {H_set_get: forall s, set_component ops s (get_component ops s) = s;
   H_get_set: forall s a, get_component ops (set_component ops s a) = a;
   H_set_set: forall s a b, set_component ops (set_component ops s a) b = set_component ops s b;
  }.

Definition transition_projection_prop {message} {A B:VLSM message} (ops: vlsm_component_ops (type A) (type B)) : Prop := forall l,
    match split_label ops l with
    | Some lj =>
      (forall s om,
          (let (s',om') := vtransition B l (s,om)
           in (get_component ops s',om'))
          =
          vtransition A lj (get_component ops s,om))
      /\ (forall s om,
             vvalid B l (s,om) -> vvalid A lj (get_component ops s,om))
    | None =>
      forall s om,
        get_component ops (fst (vtransition B l (s,om))) = get_component ops s
    end.


Definition transition_item_projection {message A B} (ops: @vlsm_component_ops message A B)
           (item: @transition_item _ B) : option (@transition_item _ A) :=
  let (l,input,destination,output) := item in
  match split_label ops l with
  | None => None
  | Some lj => Some
    {| l:= lj;
       input := input;
       destination := get_component ops destination;
       output:=output|}
  end.

Fixpoint trace_projection {message A B} (ops: @vlsm_component_ops message A B)
         (tr: list (@transition_item _ B)) {struct tr} : list (@transition_item _ A)
  := match tr with
     | nil => nil
     | cons item tr' =>
       match transition_item_projection ops item with
       | None => trace_projection ops tr'
       | Some item' => item' :: trace_projection ops tr'
       end
     end.

Lemma In_trace_projection {message A B} (ops: @vlsm_component_ops message A B)
      (tr: list (@transition_item _ B)) item:
  In item tr ->
  forall item',
    transition_item_projection ops item = Some item' ->
    In item' (trace_projection ops tr).
Proof.
  intros Hin item' Hitem'.
  induction tr.
  solve[destruct Hin].
  destruct Hin as [->|Hin_tl].
  * simpl. rewrite Hitem'. left. reflexivity.
  * specialize (IHtr Hin_tl).
    simpl. destruct (transition_item_projection ops a);[right|];exact IHtr.
Qed.

Lemma component_protocol_state_prop
      {message A B} (ops: @vlsm_component_ops message (type A) (type B))
      (Hops: vlsm_component_props ops)
      (H_transitions_project: transition_projection_prop ops)
      (Hinits: forall (s: state), @initial_state_prop _ _ (sign B) s ->
                                  @initial_state_prop _ _ (sign A) (get_component ops s))
      (Hmessages: forall omsg, option_protocol_message_prop B omsg -> option_protocol_message_prop A omsg)
      (s:state)
      (H : protocol_state_prop B s):
      protocol_state_prop A (get_component ops s).
Proof.
  destruct H as [om H].
  change s with (fst (s,om)).
  set (som:=(s,om)) in H |- *;clearbody som;clear s om.
  induction H;simpl fst.
  + destruct is. simpl in s. subst s.
    apply Hinits in i.
    exists None.
    exact (protocol_initial_state A (exist _ _ i)).
  + assert (initial_state_prop (VLSM_sign:=sign A) (get_component ops s)) as i
        by (apply Hinits;apply proj2_sig).
    exists None.
    exact (protocol_initial_state A (exist _ _ i)).
  + unfold protocol_state_prop.
    pose proof (H_transitions_project l) as Hlabel.
    destruct (split_label ops l).
    ++ clear H IHprotocol_prop2.
       simpl in IHprotocol_prop1;clear _om;destruct IHprotocol_prop1 as [_om IH].
       assert (option_protocol_message_prop A om) as Hom
           by (apply Hmessages;exists _s;assumption).
       clear _s H0;destruct Hom as [_s Hom].
       destruct Hlabel as [Htransition Hvalid].
       apply Hvalid in Hv;clear Hvalid.
       specialize (Htransition s om).
       unfold vtransition in Htransition.
       simpl in Htransition.
       exists (snd (vtransition B l (s,om))).
       change (transition l (s,om)) with (vtransition B l (s,om)) in Htransition |- *.
       set (result:=vtransition B l (s,om)) in Htransition |- *.
       clearbody result.
       rewrite (surjective_pairing result) in Htransition.
       refine (eq_ind_r (protocol_prop A) _ Htransition).
       econstructor;eassumption.

    ++ simpl in * |- *.
       destruct IHprotocol_prop1 as [om' IH].
       exists om'.
       rewrite <- (Hlabel s om) in IH.
       exact IH.
Qed.

Lemma trace_projection_valid {message A B} (ops: @vlsm_component_ops message (type A) (type B))
      (Hops: vlsm_component_props ops)
      (H_transitions_project: transition_projection_prop ops)
      (Hinits: forall (s: state), @initial_state_prop _ _ (sign B) s ->
                                  @initial_state_prop _ _ (sign A) (get_component ops s))
      (Hmessages: forall omsg, option_protocol_message_prop B omsg -> option_protocol_message_prop A omsg)
      start (tr: list transition_item) (Htr: finite_protocol_trace_from B start tr):
  finite_protocol_trace_from A (get_component ops start) (trace_projection ops tr).
Proof.
  induction Htr.
  * constructor.
    revert H;apply component_protocol_state_prop;assumption.
  * simpl.
    pose proof (H_transitions_project l) as Hsplit.
    destruct (split_label ops l).
    + constructor. exact IHHtr. clear IHHtr.
      destruct Hsplit as [Htransitions Hvalid].
      destruct H as [Hpvalid Htrans].
      split.
      2:{
        specialize (Htransitions s' iom).
        set (Bresult := transition l (s',iom)) in Htrans.
        change (vtransition B l _) with Bresult in Htransitions.
        rewrite Htrans in Htransitions. clear Bresult Htrans.
        set (jresult := vtransition A l0 _) in Htransitions.
        change (transition _ _) with jresult.
        destruct jresult.
        symmetry;assumption.
      }
      destruct Hpvalid as [Hprot_s [Hprot_msg Hv]].
      split.
      revert Hprot_s. apply component_protocol_state_prop;assumption.
      split.
      apply Hmessages. assumption.
      apply Hvalid. assumption.
    + specialize (Hsplit s' iom).
      destruct H as [_ Htrans].
      simpl in Htrans.
      set (result := transition l (s',iom)) in Htrans.
      change (vtransition _ _ _) with result in Hsplit.
      rewrite <- Hsplit, Htrans.
      assumption.
Qed.

Lemma trace_projection_projects_last
      {message A B} (ops: @vlsm_component_ops message (type A) (type B))
      (Hops: vlsm_component_props ops)
      (H_transitions_project: transition_projection_prop ops)
      start (tr: list (@transition_item message (type B)))
      (Htr: finite_protocol_trace_from B start tr):
  forall s,
    last (map destination tr) start = s ->
    last (map destination (trace_projection ops tr)) (get_component ops start) =
    get_component ops s.
Proof.
  intros s i.
  move Htr at bottom.
  induction Htr;[simpl in * |- *;congruence|].
  destruct H as [_ Htrans].
  rename i into Hlast.
  simpl map in Hlast.
  rewrite ListExtras.unroll_last in Hlast.
  specialize (IHHtr Hlast);clear Hlast.
  rewrite <- IHHtr; clear IHHtr.

  unfold trace_projection;fold (trace_projection ops).
  unfold transition_item_projection.
  pose proof (H_transitions_project l) as Hsplit_prop.
  destruct (split_label ops l).
  * (* if step is kept *)
    simpl transition_item_projection.
    simpl map.
    rewrite ListExtras.unroll_last.
    reflexivity.
  * (* if step is dropped, is must not have affected the component *)
    specialize (Hsplit_prop s' iom).
    f_equal.
    rewrite <- Hsplit_prop;clear Hsplit_prop.
    set (out := vtransition _ _ _).
    replace out with (s0,oom).
    reflexivity.
Qed.

(**
   This section proves that the basic case of projecting a single
   index from a [composite_vlsm] is an instance of the
   general notion of component developed above.
 *)
Section composite_components.
  Context
    {message : Type}
    {index : Type}
    {Heqd : EqDecision index}
    (IM : index -> VLSM message)
    {i0 : Inhabited index}
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (B := composite_vlsm IM constraint)
    (*
    {Hsents : forall i, has_been_sent_capability (IM i)}
    {index_listing: list index}
    {Hfinite: FinFun.Listing index_listing} *)
  .

  Definition proj_ops i:
    vlsm_component_ops (type (IM i)) (composite_type IM).
  Proof.
    constructor.
    refine (fun s => s i).
    refine (fun s si j => if decide_eq i j then _ else s j).
    rewrite <- e. exact si.
    refine (fun '(existT _ j lj) => if decide_eq i j then Some _ else None).
    rewrite e. exact lj.
  Defined.

  Lemma proj_ops_props_preloaded_preloaded i:
    @vlsm_component_props message
      (pre_loaded_with_all_messages_vlsm (IM i))
      (pre_loaded_with_all_messages_vlsm (composite_vlsm IM constraint))
      (proj_ops i).
  Proof.
    constructor.
    + intro s.
      apply FunctionalExtensionality.functional_extensionality_dep.
      intro x.
      simpl.
      destruct (decide (i = x)).
      * rewrite f_equal_dep. reflexivity.
      * reflexivity.
    + intros s a.
      simpl.
      destruct (decide (i = i)).
      * rewrite <- (Eqdep_dec.eq_rect_eq_dec Heqd). reflexivity.
      * elim n. reflexivity.
    + intros s a b.
      apply FunctionalExtensionality.functional_extensionality_dep.
      intro x.
      simpl.
      destruct (decide (i = x));reflexivity.
  Qed.

  Lemma transition_proj_prop_preloaded_preloaded i:
    @transition_projection_prop message
        (pre_loaded_with_all_messages_vlsm (IM i))
        (pre_loaded_with_all_messages_vlsm (composite_vlsm IM constraint))
        (proj_ops i).
  Proof.
    intro l.
    destruct l.
    simpl split_label.
    destruct (decide (i = x)).
    2:{
      intros s om.
      unfold vtransition. simpl.
      unfold vtransition. simpl.
      set (xresult:=vtransition (IM x) v (s x, om)).
      destruct xresult.
      simpl.
      unfold state_update.
      destruct (decide (i = x));congruence.
    }
    split.
    {
      intros s om.
      repeat progress (unfold vtransition;simpl transition).
      subst x.
      unfold eq_rect_r.
      simpl eq_sym.
      rewrite <- (Eqdep_dec.eq_rect_eq_dec Heqd).
      set (result := vtransition (IM i) v (s i, om)).
      change (transition _ _) with result.
      destruct result.
      f_equal.
      unfold get_component;simpl.
      apply state_update_eq.
    }
    {
      intros s om.
      subst x.
      unfold eq_rect_r.
      simpl.
      intros [H _].
      simpl in H.
      assumption.
    }
  Qed.

  Lemma component_inits i:
    forall s,
      @initial_state_prop _ _ (sign (pre_loaded_with_all_messages_vlsm (composite_vlsm IM constraint))) s ->
      @initial_state_prop _ _ (sign (pre_loaded_with_all_messages_vlsm (IM i))) (get_component (proj_ops i) s).
  Proof.
    simpl.
    intros s H.
    unfold vinitial_state_prop in H.
    simpl in H.
    unfold composite_initial_state_prop in H.
    apply H.
  Qed.

End composite_components.
