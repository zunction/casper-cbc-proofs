From Casper
Require Import vlsm indexed_vlsm.


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
  `{V : VLSM message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (m : {x : message | iproto_message_prop x})
  : proto_message
  :=
  let m0 := proj1_sig m in
  let Hcm := iproto_message_consistent m0 (proj2_sig m) in
  (exist _ m0 Hcm).

Definition vlsm_projection_initial_message_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  (m : {x : message | iproto_message_prop x})
  : Prop
  :=
  protocol_message_prop (lift_proto_message iproto_message_consistent m).

Definition ilabel_type 
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  :=
  { l : label | ilabel l = i }.

Definition noneOrAll
  (op : option Prop)
  : Prop
  :=
  match op with
  | None => True
  | (Some p) => p
  end.

Definition vlsm_projection_valid
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop m})
  : Prop
  :=
  let l := proj1_sig il in
  let (is, oim) := isom in
  let om := option_map (lift_proto_message iproto_message_consistent) oim in
  exists s : state, istate_proj i s = proj1_sig is /\ valid l (s, om)
  /\ noneOrAll (option_map iproto_message_prop (option_map (@proj1_sig message proto_message_prop) (snd (transition l (s, om)))))
  /\
  forall s' : state, istate_proj i s' = proj1_sig is -> valid l (s', om) ->
    (   snd (transition l (s, om)) = snd (transition l (s', om))
    /\  istate_proj i (fst (transition l (s, om))) = istate_proj i (fst (transition l (s, om)))
    ).


Lemma vlsm_projection_valid_decidable
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  : forall (il : ilabel_type i) (isom : istate i * option {m : message | iproto_message_prop m}),
  {vlsm_projection_valid iproto_message_consistent i il isom} + {~vlsm_projection_valid iproto_message_consistent i il isom}.
Admitted.

Require Import ClassicalChoice ClassicalEpsilon.


Definition vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop m})
  : istate i * option {m : message | iproto_message_prop m}.
remember (option_map (lift_proto_message iproto_message_consistent) (snd isom)) as om.
destruct (vlsm_projection_valid_decidable iproto_message_consistent i il isom) as [Hv | Hnv].
- unfold vlsm_projection_valid in Hv.
  remember (proj1_sig il) as l.
  destruct isom as [is oim].
  apply constructive_indefinite_description in Hv.
  destruct Hv as [s [Heq [Hv [Hmsg Hall]]]].
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
  {iproto_message_prop : message -> Prop}
  {iproto_message_decidable : forall m : message, {iproto_message_prop m} + {~iproto_message_prop m}}
  {iproto_message_inhabited : inhabited {m : message | iproto_message_prop m}}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  (ilabel_inhabited : inhabited (ilabel_type i))
  : VLSM (message : Type)
  :=
  {|  state := istate i
  ;   label := ilabel_type i
  ;   proto_message_prop := iproto_message_prop
  ;   proto_message_decidable := iproto_message_decidable
  ;   initial_state_prop := vlsm_projection_initial_state_prop i
  ;   initial_message_prop := vlsm_projection_initial_message_prop iproto_message_consistent i
  ;   transition := vlsm_projection_transition iproto_message_consistent i
  ;   protocol_state_inhabited := vlsm_projection_protocol_state_inhabited i
  ;   message_inhabited := iproto_message_inhabited
  ;   label_inhabited := ilabel_inhabited
  ;   valid := vlsm_projection_valid iproto_message_consistent i
  ;   valid_decidable := vlsm_projection_valid_decidable iproto_message_consistent i
  |}.

Definition indexed_vlsm_projection_proto_message_prop
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (i : index)
  : message -> Prop
  :=
  @proto_message_prop message (IS i).

Definition indexed_vlsm_projection_proto_message
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (i : index)
  : Type
  :=
  {m : message | indexed_vlsm_projection_proto_message_prop IS i m}.

Definition indexed_vlsm_projection_proto_message_decidable
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (i : index)
  : forall m : message, {indexed_vlsm_projection_proto_message_prop IS i m} + {~indexed_vlsm_projection_proto_message_prop IS i m}
  :=
  @proto_message_decidable message (IS i).

Definition indexed_vlsm_projection_message_inhabited
  {index : Set} {message : Type}
  (IS : index -> VLSM message)
  (i : index)
  : inhabited (indexed_vlsm_projection_proto_message IS i)
  :=
  @message_inhabited message (IS i).

Lemma indexed_vlsm_projection_proto_message_consistent
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (i : index)
  : forall m : message, indexed_vlsm_projection_proto_message_prop IS i m -> @proto_message_prop message (composed_vlsm IS (inhabits i)) m.
Proof.
  unfold indexed_vlsm_projection_proto_message_prop.
  intros m Hmi.
  unfold proto_message_prop; simpl. unfold icomposed_proto_message_prop. exists i. assumption.
Qed.

Lemma indexed_vlsm_projection_label_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (i : oindex)
  : inhabited (@ilabel_type message (composed_vlsm IS (inhabits i)) (@composed_vlsm_class_instance oindex message Heqd IS (inhabits i)) i).
Proof.
  destruct (@label_inhabited message (IS i)) as [l].
  unfold ilabel_type. unfold label; simpl. unfold composed_vlsm_ilabel. unfold icomposed_label.
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
  @vlsm_projection message (composed_vlsm IS (inhabits i)) (@composed_vlsm_class_instance oindex message Heqd IS (inhabits i))
    (indexed_vlsm_projection_proto_message_prop IS i)
    (indexed_vlsm_projection_proto_message_decidable IS i)
    (indexed_vlsm_projection_message_inhabited IS i)
    (indexed_vlsm_projection_proto_message_consistent IS i)
    i
    (indexed_vlsm_projection_label_inhabited IS i)
  .

Lemma indexed_vlsm_constrained_projection_proto_message_consistent
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : icomposed_label IS) (som : icomposed_state IS * option (icomposed_proto_message IS)), {constraint l som} + {~constraint l som})
  (i : index)
  : forall m : message, indexed_vlsm_projection_proto_message_prop IS i m -> @proto_message_prop message (composed_vlsm_constrained IS (inhabits i) constraint constraint_decidable) m.
Proof.
  unfold indexed_vlsm_projection_proto_message_prop.
  intros m Hmi.
  unfold proto_message_prop; simpl. unfold icomposed_proto_message_prop. exists i. assumption.
Qed.

Lemma indexed_vlsm_constrained_projection_label_inhabited
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : icomposed_label IS) (som : icomposed_state IS * option (icomposed_proto_message IS)), {constraint l som} + {~constraint l som})
  (i : oindex)
  : inhabited (@ilabel_type message (composed_vlsm_constrained IS (inhabits i) constraint constraint_decidable) (@composed_vlsm_constrained_instance oindex message Heqd IS (inhabits i) constraint constraint_decidable) i).
Proof.
  destruct (@label_inhabited message (IS i)) as [l].
  unfold ilabel_type. unfold label; simpl. unfold composed_vlsm_ilabel. unfold icomposed_label.
  constructor.
  exists (existT _ i l).
  reflexivity.
Qed.

Definition indexed_vlsm_constrained_projection
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : icomposed_label IS) (som : icomposed_state IS * option (icomposed_proto_message IS)), {constraint l som} + {~constraint l som})
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (composed_vlsm_constrained IS (inhabits i) constraint constraint_decidable)
    (@composed_vlsm_constrained_instance oindex message Heqd IS (inhabits i) constraint constraint_decidable)
    (indexed_vlsm_projection_proto_message_prop IS i)
    (indexed_vlsm_projection_proto_message_decidable IS i)
    (indexed_vlsm_projection_message_inhabited IS i)
    (indexed_vlsm_constrained_projection_proto_message_consistent IS constraint constraint_decidable i)
    i
    (indexed_vlsm_constrained_projection_label_inhabited IS constraint constraint_decidable i)
  .

Lemma protocol_state_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : icomposed_label IS) (som : icomposed_state IS * option (icomposed_proto_message IS)), {constraint l som} + {~constraint l som})
  : forall (j : index) (s :  @protocol_state _ (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)),
  @protocol_state_prop message
    (indexed_vlsm_constrained_projection IS constraint constraint_decidable j)
    (@proj_istate
      message
      (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@composed_vlsm_constrained_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      (proj1_sig s)
      j
    ).
Proof.
  intro.
  apply (protocol_state_ind (fun s : @state _ (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)  => @protocol_state_prop message
    (indexed_vlsm_constrained_projection IS constraint constraint_decidable j)
    (@proj_istate
      message
      (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@composed_vlsm_constrained_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      s
      j
    ))); intros.
  - apply protocol_state_prop_iff. left. 
    remember (@proj_istate
      message
      (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@composed_vlsm_constrained_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
      (proj1_sig is)
      j
    ) as js.
    unfold initial_state.
    unfold initial_state_prop; simpl. unfold vlsm_projection_initial_state_prop.
    assert (His : exists s0 : initial_state, @istate_proj message
      (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
      (@composed_vlsm_constrained_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
       j (proj1_sig s0) = proj1_sig js)
      by (exists is; subst; reflexivity).
    exists (exist _ js His); reflexivity.
  - assert (Hps' : @protocol_state_prop message (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable) (fst (protocol_transition l (s, om)))).
    { apply protocol_state_prop_iff. right. exists s. exists l. exists om. split; try assumption. reflexivity. }
    destruct (protocol_transition l (s, om)) as (s', om') eqn:Ht. simpl.
    destruct l as [i li]; destruct s as [s Hps]. destruct om as [[[m Hm] Hpm]|]; simpl in Ht.
    + simpl in Hv. destruct Hv as [Hv Hc]. simpl in Hv.
      destruct (proto_message_decidable m) as [Hpmi | Hpmi]; simpl ; try (inversion Ht; subst; assumption).
      remember (@proj_istate
        message
        (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)
        (@composed_vlsm_constrained_instance index message Heqd IS (inhabits j) constraint constraint_decidable)
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
