From Casper
Require Import vlsm indexed_vlsm.

Definition indexed_vlsm_projection_initial_message_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  (iproto_message_prop : message -> Prop)
  (i : index)
  (m : {x : message | iproto_message_prop x})
  : Prop
  :=
  let m0 := proj1_sig m in
  match proto_message_decidable m0 with
  | left Hcm => protocol_message_prop (exist _ m0 Hcm)
  | _ => False
  end
  .

Print indexed_vlsm_projection_initial_message_prop.

Definition indexed_vlsm_projection_valid
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (i : index)
  (l : @label _ (IS i))
  (som : @state _ (IS i) * option (@proto_message _ (IS i)))
  : Prop
  := @valid _ (IS i) l som
  /\ exists (s' : @protocol_state _ (composed_vlsm_constrained IS (inhabits i) constraint))
            (om' : option (@protocol_message _ (composed_vlsm_constrained IS (inhabits i) constraint))),
      fst (@transition _ (IS i) l som) = (proj1_sig s') i
      /\ option_map (@proj1_sig message _) (snd (@transition _ (IS i) l som)) = option_map (@proj1_sig message _) (option_map (@proj1_sig proto_message _) om').

Definition indexed_vlsm_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  (i : index)
  : VLSM (message : Type)
  :=
  {|  state := @state _ (IS i)
  ;   label := @label _ (IS i)
  ;   proto_message_prop := @proto_message_prop _ (IS i)
  ;   proto_message_decidable := @proto_message_decidable _ (IS i)
  ;   initial_state_prop := @initial_state_prop _ (IS i)
  ;   initial_message_prop := indexed_vlsm_projection_initial_message_prop IS constraint i
  ;   transition := @transition _ (IS i)
  ;   protocol_state_inhabited := @protocol_state_inhabited _ (IS i)
  ;   message_inhabited := @message_inhabited _ (IS i)
  ;   label_inhabited := @label_inhabited _ (IS i)
  ;   valid := indexed_vlsm_projection_valid IS constraint i
  |}.

Lemma protocol_state_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  : forall (j : index) (s :  @protocol_state _ (composed_vlsm_constrained IS (inhabits j) constraint)),
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

(*
Lemma constraint_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> VLSM message)
  (constraint : icomposed_label IS -> icomposed_state IS * option (icomposed_proto_message IS) -> Prop)
  : forall
    (j : index)
    (lj : @label _ (IS j))
    (s :  @protocol_state _ (composed_vlsm_constrained IS (inhabits j) constraint))
    (om : option (@protocol_message _ (composed_vlsm_constrained IS (inhabits j) constraint)))
    (Hc : constraint (existT _ j lj) (proj1_sig s, option_map (proj1_sig _ _) om))
  , (@valid _ (indexed_vlsm_projection IS constraint j) lj (proj1_sig s j, option_map (proj1_sig _ _) om)) 
  .
Proof.
Admitted.

*)