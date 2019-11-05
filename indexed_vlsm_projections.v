From Casper
Require Import vlsm indexed_vlsm.


Definition indexed_vlsm_projection_initial_state_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (is : istate i)
  : Prop
  :=
  exists s : initial_state, istate_proj i (proj1_sig s) = proj1_sig is.

Definition indexed_vlsm_projection_initial_state
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  :=
  { s : istate i | indexed_vlsm_projection_initial_state_prop i s }.

Lemma indexed_vlsm_projection_protocol_state_inhabited
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : inhabited (indexed_vlsm_projection_initial_state i).
Proof.
  destruct protocol_state_inhabited as [s].
  remember (istate_proj i (proj1_sig s)) as is.
  assert (His : exists s, istate_proj i s = is) by (exists (proj1_sig s); subst; reflexivity).
  remember (exist (fun is : iproto_state i => exists s : state, istate_proj i s = is) is His) as iis.
  assert (Hiis : indexed_vlsm_projection_initial_state_prop i iis)
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

Definition indexed_vlsm_projection_initial_message_prop
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

Definition indexed_vlsm_projection_valid
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


Lemma indexed_vlsm_projection_valid_decidable
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  : forall (il : ilabel_type i) (isom : istate i * option {m : message | iproto_message_prop m}),
  {indexed_vlsm_projection_valid iproto_message_consistent i il isom} + {~indexed_vlsm_projection_valid iproto_message_consistent i il isom}.
Admitted.

Require Import ClassicalChoice ClassicalEpsilon.


Definition indexed_vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  {iproto_message_prop : message -> Prop}
  (iproto_message_consistent : forall m : message, iproto_message_prop m -> proto_message_prop m)
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop m})
  : istate i * option {m : message | iproto_message_prop m}.
remember (option_map (lift_proto_message iproto_message_consistent) (snd isom)) as om.
destruct (indexed_vlsm_projection_valid_decidable iproto_message_consistent i il isom) as [Hv | Hnv].
- unfold indexed_vlsm_projection_valid in Hv.
  remember (proj1_sig il) as l.
  destruct isom as [is oim].
  apply constructive_indefinite_description in Hv.
  destruct Hv as [s [Heq [Hv [Hmsg Hall]]]].
  simpl in Heqom. rewrite <- Heqom in *.
  remember (transition l (s,om)) as som'.
  destruct som' as [s' om']. simpl in Hmsg.
  remember (istate_proj i s') as is'. 
  assert (His' : exists s'', istate_proj i s'' = is') by (exists s'; subst; reflexivity).
  destruct om' as [m'|]; simpl in Hmsg.
  * exact (exist _ is' His', Some (exist _ (proj1_sig m') Hmsg)).
  * exact (exist _ is' His', None).
- exact (fst isom, None).
Defined.

Definition indexed_vlsm_projection
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
  ;   initial_state_prop := indexed_vlsm_projection_initial_state_prop i
  ;   initial_message_prop := indexed_vlsm_projection_initial_message_prop iproto_message_consistent i
  ;   transition := indexed_vlsm_projection_transition iproto_message_consistent i
  ;   protocol_state_inhabited := indexed_vlsm_projection_protocol_state_inhabited i
  ;   message_inhabited := iproto_message_inhabited
  ;   label_inhabited := ilabel_inhabited
  ;   valid := indexed_vlsm_projection_valid iproto_message_consistent i
  ;   valid_decidable := indexed_vlsm_projection_valid_decidable iproto_message_consistent i
  |}.

(* 
Lemma protocol_state_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (constraint_decidable : forall (l : icomposed_label IS) (som : icomposed_state IS * option (icomposed_proto_message IS)), {constraint l som} + {~constraint l som})
  : forall (j : index) (s :  @protocol_state _ (composed_vlsm_constrained IS (inhabits j) constraint constraint_decidable)),
  @protocol_state_prop _ (indexed_vlsm_projection IS constraint j) (proj1_sig s j).
Proof.
  intro.
  apply (protocol_state_ind (fun s : @state _ (composed_vlsm_constrained IS (inhabits j) constraint)  => @protocol_state_prop _ (indexed_vlsm_projection IS constraint j) (s j))); intros.
  - apply protocol_state_prop_iff. left. destruct is as [s His]. simpl.
    specialize (His j). remember (exist _ (s j) His) as isj.
    exists isj. subst. reflexivity.
  - assert (Hps' : @protocol_state_prop message (composed_vlsm_constrained IS (inhabits j) constraint) (fst (protocol_transition l (s, om)))).
    { apply protocol_state_iff.
     
    destruct (protocol_transition l (s, om)) as (s', om') eqn:Ht. simpl.
    destruct l as [i li]; destruct s as [s Hps]. destruct om as [[[m Hm] Hpm]|]; simpl in Ht.
    + simpl in Hv. destruct Hv as [Hv Hc]. simpl in Hv.
      destruct (proto_message_decidable m) as [Hpmi | Hpmi]; simpl ; try (inversion Ht; subst; assumption).
      remember (exist proto_message_prop m Hpmi) as mi.
      destruct (transition li (s i, Some mi)) as [si' omi'] eqn:Hti.
      inversion Ht as [[Htf Htm]].
      destruct (eq_dec j i); try assumption.
      rewrite e; unfold eq_rect_r; unfold eq_rect; unfold eq_sym.
      simpl in Hind. rewrite e in Hind.
      apply (@next_protocol_state_with_message _ (indexed_vlsm_projection IS constraint i) (s i) si' li mi omi'); try assumption.
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
Admitted.  

 *)