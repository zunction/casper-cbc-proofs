From Casper
Require Import vlsm composed_vlsm.

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
  .


(* 
message : Type
H : VLSM message
CV : composed_vlsm_class message
i : index
l : label
Hl : ilabel l = i
is : iproto_state i
s : state
His : istate_proj i s = is
iom : option {m : message | iproto_message_prop i m}
om : option proto_message
Heqom : om = option_map (lift_proto_message i) iom
s' : state
m' : proto_message
Heqt : (s', Some m') = transition l (s, om)
Hmsg : iproto_message_prop i (proj1_sig m')
*)
Definition transitioning_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (isom isom' : istate i * option {m : message | iproto_message_prop i m})
  :=
  exists (s s' : state),
    proj_istate s i = fst isom /\
    proj_istate s' i = fst isom' /\
    transition (proj1_sig il) (s, (option_map (lift_proto_message i) (snd isom))) = (s', (option_map (lift_proto_message i) (snd isom')))
  .

Lemma vlsm_projection_transition_existance
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop i m})
  : exists isom' : istate i * option {m : message | iproto_message_prop i m}, 
      transitioning_projection i il isom isom'.
Proof.
  destruct isom as [is iom].
  destruct il as [l Hl].
  destruct is as [is [s His]].
  remember (option_map (lift_proto_message i) iom) as om.

  specialize transition_projection_type_preservation; intros Hmsg.
  specialize (Hmsg s om l i Hl).

  remember (transition l (s, om)) as t.
  destruct t as [s' om'].

  destruct om' as [m'|]; simpl in Hmsg.
  - exists (proj_istate s' i, Some (exist _ (proj1_sig m') Hmsg)).
    exists s. exists s'. rewrite <- His.
    simpl. repeat split; try reflexivity.  rewrite <- Heqom. rewrite <- Heqt.
    apply f_equal. apply f_equal.
    unfold lift_proto_message; simpl.
    apply exist_eq. reflexivity.
  - exists (proj_istate s' i, None).
    exists s. exists s'. rewrite <- His. 
    simpl. repeat split; try reflexivity.
    rewrite <- Heqom. symmetry.  assumption.
Qed.

Require Import Coq.Logic.ClassicalEpsilon.

Definition vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (isom : istate i * option {m : message | iproto_message_prop i m})
  : istate i * option {m : message | iproto_message_prop i m}
  :=
  (proj1_sig
    (constructive_indefinite_description
      (transitioning_projection i il isom)
      (vlsm_projection_transition_existance i il isom)
    )
  ).

Lemma vlsm_projection_transition_irrelevance
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : ilabel_type i)
  (s1 s2 : istate i)
  (Heqi : proj1_sig s1 = proj1_sig s2)
  (om : option {m : message | iproto_message_prop i m})
  : vlsm_projection_transition i il (s1, om) = vlsm_projection_transition i il (s2, om).
Proof.
  assert (Heq : s1 = s2 ).
  { destruct s1 as [s1 Hs1]. destruct s2 as [s2 Hs2]. apply exist_eq. assumption. }
  subst. reflexivity.
Qed.

Definition vlsm_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
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
  ;   label_inhabited := ilabel_type_inhabited i
  ;   valid := vlsm_projection_valid i
  |}.


Lemma protocol_state_projection
  {message : Type}
  {V : VLSM message}
  `{CV : @composed_vlsm_class message V}
  : forall (i : index) (s :  protocol_state),
  @protocol_state_prop _ (vlsm_projection i) (proj_istate (proj1_sig s) i).
Proof.
  intros i [s Hps]. simpl. induction Hps as [is | s s'' l om' Hps Hp Hv Ht| s s'' l m om' Hps Hp Hpm Hv Ht].
  - apply protocol_state_prop_iff. left. 
    remember (proj_istate (proj1_sig is) i) as iis.
    unfold initial_state.
    unfold initial_state_prop; simpl. unfold vlsm_projection_initial_state_prop.
    assert (His : exists s0 : initial_state, istate_proj i (proj1_sig s0) = proj1_sig iis)
      by (exists is; subst; reflexivity).
    exists (exist _ iis His); reflexivity.
  - remember None as om. 
(* 
    assert (Hps' : protocol_state_prop (fst (transition l (s, om)))).
    { apply protocol_state_prop_iff. right. exists (exist _ s Hps). exists l. exists None. 
      unfold protocol_valid; unfold protocol_transition; simpl. split; subst; try assumption; reflexivity. }
 *)
    remember (ilabel l) as j.
    destruct (index_eq_dec i j); subst.
    + apply protocol_state_prop_iff. right.
      exists (exist _ (proj_istate s (ilabel l)) Hp).
      remember (ilabel l) as j. symmetry in Heqj.
      exists (exist _ l Heqj).
      exists None. split.
      * unfold protocol_valid. simpl. exists s. split; try reflexivity. assumption.
      * simpl. unfold vlsm_projection_transition.
        remember
          (@constructive_indefinite_description
           (prod (@istate message V CV j)
              (option (@sig message (fun m : message => @iproto_message_prop message V CV j m))))
           (@transitioning_projection message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
           (@vlsm_projection_transition_existance message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
          ) as sjom'.
      clear Heqsjom'.
      destruct sjom' as [sjom' Hsjom'].
      rename om' into om''.
      destruct sjom' as [sj' om'].
      destruct Hsjom' as [s0 [s0' Hsjom']]. simpl in Hsjom'.
      destruct Hsjom' as [Heqs0 [Heqs0' Ht0]]. simpl.
      specialize transition_projection_consistency; intros Hpc.
      apply proj_istate_eq in Heqs0.
      specialize (Hpc s0 s None l j Heqs0 Heqj).
      rewrite Ht in Hpc. simpl in Hpc. destruct Hpc as [Hmsg Hst].
      apply proj_istate_eq in Hst. rewrite <- Hst. 
      rewrite Ht0. simpl. assumption.
    + specialize (transition_projection_state_preservation s None l i); intros Htp.
      assert (ni : ilabel l <> i) by (intro; subst; contradiction).
      specialize (Htp ni). rewrite Ht in Htp. simpl in Htp.
      apply proj_istate_eq in Htp.
      rewrite Htp. assumption.
  - remember (Some m) as om.
    remember (ilabel l) as j.
    destruct (index_eq_dec i j); subst.
(* 
    + apply protocol_state_prop_iff. right.
      remember (ilabel l) as j. exists (exist _ (proj_istate s j) Hp).
      symmetry in Heqj.
      exists (exist _ l Heqj).
      
      exists (Some (lift_proto_message j (exist _ m Hpm))). split.
      * unfold protocol_valid. simpl. exists s. split; try reflexivity. assumption.
      * simpl. unfold vlsm_projection_transition.
        remember
          (@constructive_indefinite_description
           (prod (@istate message V CV j)
              (option (@sig message (fun m : message => @iproto_message_prop message V CV j m))))
           (@transitioning_projection message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
           (@vlsm_projection_transition_existance message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
          ) as sjom'.
      clear Heqsjom'.
      destruct sjom' as [sjom' Hsjom'].
      rename om' into om''.
      destruct sjom' as [sj' om'].
      destruct Hsjom' as [s0 [s0' Hsjom']]. simpl in Hsjom'.
      destruct Hsjom' as [Heqs0 [Heqs0' Ht0]]. simpl.
      specialize transition_projection_consistency; intros Hpc.
      apply proj_istate_eq in Heqs0.
      specialize (Hpc s0 s None l j Heqs0 Heqj).
      rewrite Ht in Hpc. simpl in Hpc. destruct Hpc as [Hmsg Hst].
      apply proj_istate_eq in Hst. rewrite <- Hst. 
      rewrite Ht0. simpl. assumption.
 *)
Admitted.
