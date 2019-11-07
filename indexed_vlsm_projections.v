From Casper
Require Import vlsm indexed_vlsm composed_vlsm.

Definition vlsm_projection_initial_state_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (is : istate i)
  : Prop
  :=
  exists s : initial_state, istate_proj i (proj1_sig s) = proj1_sig is.

Definition vlsm_projection_initial_state
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  :=
  { s : istate i | vlsm_projection_initial_state_prop i s }.

Lemma vlsm_projection_protocol_state_inhabited
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : inhabited (vlsm_projection_initial_state i).
Proof.
  destruct protocol_state_inhabited as [s].
  remember (proj_istate (proj1_sig s) i) as iis.
  assert (Hiis : vlsm_projection_initial_state_prop i iis)
    by (exists s; subst; reflexivity).
  constructor. exact (exist _ iis Hiis).
Qed.

Definition lift_proto_message
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : proto_message
  :=
  let m0 := proj1_sig m in
  let Hcm := iproto_message_consistent i m0 (proj2_sig m) in
  (exist _ m0 Hcm).

Definition vlsm_projection_initial_message_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : Prop
  :=
  protocol_message_prop (lift_proto_message i m).

Definition ilabel_type 
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  :=
  { l : label | ilabel l = i }.

Definition vlsm_projection_valid
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop i m})
  : Prop
  :=
  let l := proj1_sig il in
  let (is, oim) := isom in
  let om := option_map (lift_proto_message i) oim in
  exists s : state, istate_proj i s = proj1_sig is /\ valid l (s, om)
  /\ noneOrAll (option_map (iproto_message_prop i) (option_map (@proj1_sig message proto_message_prop) (snd (transition l (s, om)))))
  .


Lemma vlsm_projection_valid_decidable
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : forall (il : ilabel_type i) (isom : istate i * option {m : message | iproto_message_prop i m}),
  {vlsm_projection_valid i il isom} + {~vlsm_projection_valid i il isom}.
Admitted.

Require Import ClassicalChoice ClassicalEpsilon.


Definition vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop i m})
  : istate i * option {m : message | iproto_message_prop i m}.
remember (option_map (lift_proto_message i) (snd isom)) as om.
destruct (vlsm_projection_valid_decidable i il isom) as [Hv | Hnv].

(*
destruct isom as [is iom].
destruct il as [l Hl].

destruct is as [is His].
apply constructive_indefinite_description in His.
destruct His as [s His].

remember (option_map (lift_proto_message i) iom) as om.

remember (transition l (s, om)) as t.
destruct t as [s' om'].

exact (proj_istate s' i, None).
*)
- unfold vlsm_projection_valid in Hv.
  remember (proj1_sig il) as l.
  destruct isom as [is oim].
  apply constructive_indefinite_description in Hv.
  destruct Hv as [s [Heq [Hv Hmsg]]].
  simpl in Heqom. rewrite <- Heqom in *.
  remember (transition l (s,om)) as som'.
  destruct som' as [s' om']. simpl in Hmsg.
  remember (proj_istate s' i) as is'. 
  destruct om' as [m'|]; simpl in Hmsg.
  * exact (is', Some (exist _ (proj1_sig m') Hmsg)).
  * exact (is', None).
- exact (fst isom, None).
Defined.

Definition vlsm_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (ilabel_inhabited : inhabited (ilabel_type i))
  : VLSM (message : Type)
  :=
  {|  state := istate i
  ;   label := ilabel_type i
  ;   proto_message_prop := iproto_message_prop i
  ;   proto_message_decidable := iproto_message_decidable i
  ;   initial_state_prop := vlsm_projection_initial_state_prop i
  ;   initial_message_prop := vlsm_projection_initial_message_prop i
  ;   transition := vlsm_projection_transition i
  ;   protocol_state_inhabited := vlsm_projection_protocol_state_inhabited i
  ;   message_inhabited := iproto_message_inhabited i
  ;   label_inhabited := ilabel_inhabited
  ;   valid := vlsm_projection_valid i
  ;   valid_decidable := vlsm_projection_valid_decidable i
  |}.

Lemma indexed_vlsm_projection_label_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (i : oindex)
  : inhabited (@ilabel_type message (indexed_vlsm IS (inhabits i)) (@indexed_vlsm_composed_instance oindex message Heqd IS (inhabits i)) i).
Proof.
  destruct (@label_inhabited message (IS i)) as [l].
  unfold ilabel_type. unfold label; simpl. unfold indexed_vlsm_ilabel. unfold indexed_label.
  constructor.
  exists (existT _ i l).
  reflexivity.
Qed.

Definition indexed_vlsm_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_vlsm IS (inhabits i))
    (@indexed_vlsm_composed_instance oindex message Heqd IS (inhabits i))
    i
    (indexed_vlsm_projection_label_inhabited IS i)
  .

Lemma indexed_vlsm_constrained_projection_label_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  (i : oindex)
  : inhabited (@ilabel_type message (indexed_vlsm_constrained IS (inhabits i) constraint constraint_decidable) (@indexed_vlsm_constrained_composed_instance oindex message Heqd IS (inhabits i) constraint constraint_decidable) i).
Proof.
  destruct (@label_inhabited message (IS i)) as [l].
  unfold ilabel_type. unfold label; simpl. unfold indexed_vlsm_ilabel. unfold indexed_label.
  constructor.
  exists (existT _ i l).
  reflexivity.
Qed.

Definition indexed_vlsm_constrained_projection
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_vlsm_constrained IS (inhabits i) constraint constraint_decidable)
    (@indexed_vlsm_constrained_composed_instance oindex message Heqd IS (inhabits i) constraint constraint_decidable)
    i
    (indexed_vlsm_constrained_projection_label_inhabited IS constraint constraint_decidable i)
  .

Lemma protocol_state_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  : forall (j : index) (s :  @protocol_state _ (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)),
  @protocol_state_prop message
    (indexed_vlsm_constrained_projection IS constraint constraint_decidable j)
    (@proj_istate
      message
      (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@indexed_vlsm_constrained_composed_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      (proj1_sig s)
      j
    ).
Proof.
  intro.
  apply (protocol_state_ind (fun s : @state _ (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)  => @protocol_state_prop message
    (indexed_vlsm_constrained_projection IS constraint constraint_decidable j)
    (@proj_istate
      message
      (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@indexed_vlsm_constrained_composed_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      s
      j
    ))); intros.
  - apply protocol_state_prop_iff. left. 
    remember (@proj_istate
      message
      (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@indexed_vlsm_constrained_composed_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      (proj1_sig is)
      j
    ) as js.
    unfold initial_state.
    unfold initial_state_prop; simpl. unfold vlsm_projection_initial_state_prop.
    assert (His : exists s0 : initial_state, @istate_proj message
      (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@indexed_vlsm_constrained_composed_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
       j (proj1_sig s0) = proj1_sig js)
      by (exists is; subst; reflexivity).
    exists (exist _ js His); reflexivity.
  - assert (Hps' : @protocol_state_prop message (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable) (fst (protocol_transition l (s, om)))).
    { apply protocol_state_prop_iff. right. exists s. exists l. exists om. split; try assumption. reflexivity. }
    destruct (protocol_transition l (s, om)) as (s', om') eqn:Ht. simpl.
    destruct l as [i li]; destruct s as [s Hps]. destruct om as [[[m Hm] Hpm]|]; simpl in Ht.
    + simpl in Hv. destruct Hv as [Hv Hc]. simpl in Hv.
      destruct (proto_message_decidable m) as [Hpmi | Hpmi]; simpl ; try (inversion Ht; subst; assumption).
      remember (@proj_istate
        message
        (indexed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
        (@indexed_vlsm_constrained_composed_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
        s
        i
      ) as si.
      remember (exist proto_message_prop m Hpmi) as mi.
(* 
      destruct (@transition message (indexed_vlsm_constrained_projection IS constraint constraint_decidable j) (existT _ i li)  (si, Some mi)) as [si' omi'] eqn:Hti.
      inversion Ht as [[Htf Htm]].
      destruct (eq_dec j i); try assumption.
      rewrite e; unfold eq_rect_r; unfold eq_rect; unfold eq_sym.
      simpl in Hind. rewrite e in Hind.
      apply (@next_protocol_state_with_message _ (indexed_vlsm_constrained_projection IS constraint constraint_decidable j) (s i) si' li mi omi'); try assumption.
      * assert (Himi : @initial_message_prop _ (indexed_vlsm_projection IS constraint i) mi).
        { unfold initial_message_prop; simpl. unfold indexed_vlsm_projection_initial_message_prop. subst. simpl.
          simpl in Hpm.
          assert (ex_intro (fun i0 : index => proto_message_prop m) i Hpmi = Hm) by apply proof_irrelevance.
          rewrite H. assumption.
        }
        remember (exist _ mi Himi) as imi.
        specialize (@initial_protocol_message message (indexed_vlsm_projection IS constraint i)); intros Hinitial_msg.
        specialize (Hinitial_msg imi).
        rewrite Heqimi in Hinitial_msg; simpl in Hinitial_msg. assumption.
      * split; try assumption.
        
      apply 
 *)

Admitted.  
