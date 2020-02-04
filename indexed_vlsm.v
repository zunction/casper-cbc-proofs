Require Import List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
     Require Import preamble vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
 *)

Section indexing. 

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          (IS : index -> LSM_sig message).

  Definition indexed_state : Type :=
    forall n : index, (@state _ (IS n)).

  Definition indexed_label
    : Type
    := sigT (fun n => @label _ (IS n)).

  Definition indexed_proto_message_prop
             (m : message)
    : Prop
    :=
      exists n : index, @proto_message_prop message (IS n) m.

  Lemma indexed_proto_message_decidable
    : forall m : message, {indexed_proto_message_prop m} + {~indexed_proto_message_prop m}.
  Proof.
    intros.
    apply excluded_middle_informative.
  Qed.

  Definition indexed_proto_message
    := { m : message | indexed_proto_message_prop m }.

  Definition indexed_initial_state_prop
             (s : indexed_state)
    : Prop
    :=
      forall n : index, @initial_state_prop _ (IS n) (s n).

  Definition indexed_initial_state
    := { s : indexed_state | indexed_initial_state_prop s }.

  Definition indexed_s0
    : indexed_initial_state.
    exists (fun (n : index) => proj1_sig (@s0 _ (IS n))).
    intro i. destruct s0 as [s Hs]. assumption.
  Defined.

  Definition indexed_initial_message_prop
             (m : indexed_proto_message)
    : Prop
    :=
      exists (n : index) (mi : @initial_message _ (IS n)), proj1_sig (proj1_sig mi) = proj1_sig m.

  (* An explicit argument for the initial state witness is no longer required: *) 
  Definition indexed_m0
    : indexed_proto_message.
    destruct (@m0 _ (IS i0)) as [m Hpm].
    exists m. exists i0. assumption.
  Defined.

  Definition indexed_l0
    : indexed_label
    := existT _ i0 (@l0 message (IS i0)) .

  Definition lift_proto_messageI
             (n : index)
             (mi : @proto_message _ (IS n))
    : indexed_proto_message.
    destruct mi as [m Hm].
    exists m. exists n. assumption.
  Defined.

  Definition indexed_sig
    : LSM_sig message
    :=
      {| state := indexed_state 
         ; label := indexed_label
         ; proto_message_prop := indexed_proto_message_prop
         ; proto_message_decidable := indexed_proto_message_decidable
         ; initial_state_prop := indexed_initial_state_prop
         ; s0 := indexed_s0
         ; initial_message_prop := indexed_initial_message_prop
         ; m0 := indexed_m0
         ; l0 := indexed_l0 
      |}.

  Definition state_update
             (s : @state message (indexed_sig))
             (i : index)
             (si : @state message (IS i))
             (j : index)
    : @state message (IS j)
    :=
    match eq_dec j i with
    | left e => eq_rect_r (fun i => @state message (IS i)) si e
    | _ => s j
    end.

  Lemma state_update_neq 
             (s : @state message (indexed_sig))
             (i : index)
             (si : @state message (IS i))
             (j : index)
             (Hneq : j <> i)
    : state_update s i si j = s j.
  Proof.
    unfold state_update. destruct (eq_dec j i); try contradiction. reflexivity.
  Qed.

  Lemma state_update_eq 
             (s : @state message (indexed_sig))
             (i : index)
             (si : @state message (IS i))
    : state_update s i si i = si.
  Proof.
    unfold state_update. destruct (eq_dec i i) eqn:Heq; try contradiction.
    assert (e = eq_refl) by apply proof_irrelevance.  rewrite H. simpl.
    reflexivity.
  Qed.

  Definition indexed_transition
             (IM : forall n : index, @VLSM message (IS n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)).
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + destruct (@transition _ _ _ li (s i, Some (exist _ m Hi))) as [si' om'].
        exact (state_update s i si', option_map (lift_proto_messageI i) om').
      + exact (s, None).
    - destruct (@transition _ _ _ li (s i, None)) as [si' om'].
      exact (state_update s i si', option_map (lift_proto_messageI i) om').
  Defined.

  Definition indexed_valid
             (IM : forall n : index, @VLSM message (IS n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : Prop.
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + exact (@valid _ _ _ li (s i, Some (exist _ m Hi))).
      + exact False.
    - exact (@valid _ _ _ li (s i, None)).
  Defined.

  Definition indexed_valid_decidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : {indexed_valid IM l som} + {~indexed_valid IM l som}.
    destruct som as [s om].
    destruct l as [i li]; simpl.
    destruct om as [[m _]|]; simpl.
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + apply valid_decidable.
        apply IDM; assumption. 
      + right; intro; contradiction.
    - apply valid_decidable.
      apply IDM; assumption.
  Defined.

  (* Constrained VLSM composition *)

  Definition indexed_valid_constrained
             (IM : forall n : index, @VLSM message (IS n))
             (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    :=
      indexed_valid IM l som /\ constraint l som.

  Definition indexed_vlsm_constrained
             (IM : forall n : index, @VLSM message (IS n))
             (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
    : @VLSM message (indexed_sig)
    :=
      {|  transition := indexed_transition IM
          ;   valid := indexed_valid_constrained IM constraint
      |}.

  Definition indexed_valid_constrained_decidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : {@valid _ _ (indexed_vlsm_constrained IM constraint) l som} + {~@valid _ _ (indexed_vlsm_constrained IM constraint) l som}.
    intros.
    unfold indexed_valid_constrained.
    destruct (constraint_decidable l som) as [Hc | Hnc].
    - destruct (indexed_valid_decidable IDM l som) as [Hv | Hnv].
      + left. split; try assumption.
      + right. intros [Hv _]. contradiction.
    - right. intros [_ Hc]. contradiction.
  Defined.

  Definition indexed_vlsm_constrained_vdecidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
    : @VLSM_vdecidable _ _ (indexed_vlsm_constrained IM constraint)
    :=
      {|  valid_decidable := indexed_valid_constrained_decidable IDM constraint_decidable
      |}.

  (* Free VLSM composition *)

  Definition free_constraint 
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : Prop
    :=
      True.

  Definition free_constraint_decidable
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : {free_constraint l som} + {~free_constraint l som}
    := left I.

  Definition indexed_vlsm_free
             (IM : forall n : index, @VLSM message (IS n))
    : @VLSM message (indexed_sig)
    :=
      indexed_vlsm_constrained IM free_constraint
  .

  Definition indexed_vlsm_free_vdecidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
    : @VLSM_vdecidable _ _ (indexed_vlsm_free IM)
    :=
      indexed_vlsm_constrained_vdecidable IDM free_constraint_decidable.


End indexing.


(* From indexed_vlsm_projections.v *)
Section projections. 

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          {IS : index -> LSM_sig message}
          (IM : forall n : index, VLSM (IS n))
          (S := indexed_sig i0 IS)
          (constraint : @label _ S -> @state _ S * option (@proto_message _ S) -> Prop)
          (X := indexed_vlsm_constrained i0 IS IM constraint)
          .

  Lemma indexed_valid_message
             {l : @label _ S}
             {s : @state _ S}
             {m  : @proto_message _ S}
      : @valid _ S X l (s, Some m)
      -> @proto_message_prop _ (IS (projT1 l)) (proj1_sig m)
      .
  Proof.
    intros Hv.
    inversion Hv. unfold indexed_valid in H.
    destruct l. destruct m.
    destruct (proto_message_decidable x0); try assumption.
    inversion H.
  Qed.

  Lemma indexed_transition_output
             {l : @label _ S}
             {s : @state _ S}
             {om  : option (@proto_message _ S)}
             {s' : @state _ S}
             {m'  : @proto_message _ S}
      : @transition _ S X l (s, om) = (s', Some m')
      -> @proto_message_prop _ (IS (projT1 l)) (proj1_sig m')
      .
  Proof.
    unfold transition. simpl. destruct l. destruct om.
    - destruct p.
      destruct (proto_message_decidable x0).
      + destruct (transition l (s x, Some (exist proto_message_prop x0 p0))) eqn:Ht.
        destruct o; simpl; intros Heq; inversion Heq.
        destruct p1. simpl. assumption.
      + intros Heq; inversion Heq.
    - destruct (transition l (s x, None)) eqn:Ht.
      destruct o; simpl; intros Heq; inversion Heq.
      destruct p. simpl. assumption.
  Qed.



  Definition indexed_vlsm_constrained_projection_sig (i : index) : LSM_sig message
    :=
      {|  state := @state _ (IS i)
          ;   label := @label _ (IS i)
          ;   proto_message_prop := @proto_message_prop _ (IS i)
          ;   proto_message_decidable := @proto_message_decidable _ (IS i)
          ;   initial_state_prop := @initial_state_prop _ (IS i)
          ;   initial_message_prop := fun pmi => exists xm : (@protocol_message _ _ X), proj1_sig (proj1_sig xm) = proj1_sig pmi
          ;   s0 := @s0 _ (IS i)
          ;   m0 := @m0 _ (IS i)
          ;   l0 := @l0 _ (IS i)
      |}.


  Definition indexed_vlsm_constrained_projection
             (i : index)
    : VLSM (indexed_vlsm_constrained_projection_sig i).
    unfold indexed_vlsm_constrained_projection_sig; simpl.
    split; simpl; unfold proto_message; simpl.
    - exact (@transition _ _ (IM i)).
    - intros l som. destruct (@transition _ _ (IM i) l som) as  [si' omi']. 
      exact
        (   @valid _ _ (IM i) l som
            /\  exists s' : @protocol_state _ _ X, exists om' : option (@protocol_message _ _ X),
              (  (proj1_sig s') i = si'
                 /\ option_map (@proj1_sig _ _) (option_map (@proj1_sig _ _) om') = option_map (@proj1_sig _ _) omi' 
              )
        ).
  Defined.

  Section fixed_projection.

    Context
      (j : index)
      (Proj := indexed_vlsm_constrained_projection j)
      .

    Lemma transition_projection : @transition message (indexed_vlsm_constrained_projection_sig j) Proj = @transition message (IS j) (IM j).
    Proof. reflexivity.  Qed.

    Lemma state_projection : @state message (indexed_vlsm_constrained_projection_sig j) = @state message (IS j).
    Proof. reflexivity. Qed.

    Lemma proto_message_projection : @proto_message message (indexed_vlsm_constrained_projection_sig j) = @proto_message message (IS j).
    Proof. reflexivity. Qed.

    Lemma proto_message_prop_projection : @proto_message_prop message (indexed_vlsm_constrained_projection_sig j) = @proto_message_prop message (IS j).
    Proof. reflexivity. Qed.


(** 2.4.4.1 Projection friendly composition constraints **)

    Definition projection_friendly
      :=
      forall
        (lj : @label _ (IS j))
        (sj : protocol_state Proj)
        (om : option (protocol_message Proj))
      , protocol_valid Proj lj (sj, om)
      -> exists (s : protocol_state X),
        (proj1_sig s) j = proj1_sig sj
        /\
        constraint (existT _ j lj)
        ( proj1_sig s
        , option_map (lift_proto_messageI IS j) (option_map (@proj1_sig proto_message _) om)
        )
      .

    Fixpoint finite_trace_projection_list
      (trx : list (@in_state_out _ S))
      : list (@in_state_out _ (sign Proj))
      :=
      match trx with
      | [] => []
      | item :: trx =>
        let tail := finite_trace_projection_list trx in
        let s := destination item in
        let l := l item in
        let x := projT1 l in
        match eq_dec j x with
        | left e =>
          let lj := eq_rect_r _ (projT2 l) e in
          match input item with
          | None =>
            match output item with
            | None =>
              @Build_in_state_out _ (sign Proj) lj None (s j) None :: tail
            | Some (exist _ out _) =>
              match @proto_message_decidable _ (sign Proj) out with
              | left Pout =>
                @Build_in_state_out _ (sign Proj) lj None (s j) (Some (exist _ out Pout)) :: tail
              | _ => tail
              end
            end
          | Some (exist _ inp _) =>
            match @proto_message_decidable _ (sign Proj) inp with
            | left Pinp =>
              let inpj := Some (exist _ inp Pinp) in
              match output item with
              | None =>
                @Build_in_state_out _ (sign Proj) lj inpj (s j) None :: tail
              | Some (exist _ out _) =>
                match @proto_message_decidable _ (sign Proj) out with
                | left Pout =>
                  @Build_in_state_out _ (sign Proj) lj inpj (s j) (Some (exist _ out Pout)) :: tail
                | _ => tail
                end
              end
            | _ => tail
            end
          end
        | _ => tail
        end
      end.

    Lemma finite_ptrace_projection
      (s : @state _ S)
      (Psj : protocol_state_prop Proj (s j))
      (trx : list (@in_state_out _ S))
      (Htr : finite_ptrace_from X s trx)
       : finite_ptrace_from Proj (s j) (finite_trace_projection_list trx).
    Proof.
      induction Htr.
      - constructor. assumption.
      - destruct l as [x lx]; simpl.
        destruct H as [Ps' [Piom [[Hv Hc] Ht]]].
        assert (Hpp : protocol_prop X (s, oom)).
        { rewrite <- Ht. destruct Ps' as [_om Ps']. destruct Piom as [_s Piom].
          apply (protocol_generated _ _ _ _ Ps' _ _ Piom). split; assumption.
        }
        assert (Hps : protocol_state_prop X s) by (exists oom; assumption).
        unfold indexed_valid in Hv.
        destruct (eq_dec j x).
        + subst x.
          assert
            (Heqlx :
              (@eq_rect_r index j (fun n : index => @label message (IS n)) lx j (@eq_refl index j))
              = lx
            ) by reflexivity.
          destruct iom as [[inp Pimp]|].
          * unfold transition in  Ht. simpl in Ht.
            destruct (proto_message_decidable inp); try inversion Hv.
            destruct (transition lx (s' j, Some (exist proto_message_prop inp p))) eqn:Hteq.
            assert (Hini : @initial_message_prop _  (sign Proj) (exist proto_message_prop inp p))
              by (exists (exist _ (exist (fun m : message => proto_message_prop m) inp Pimp) Piom); reflexivity).
            remember (exist _ (exist proto_message_prop inp p) Hini) as inim.
            assert (Hinip : @protocol_prop _ _ Proj ((@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))), Some (proj1_sig inim)))
              by (apply (@protocol_initial_message _ _ Proj inim)).
            assert
              (Hiniproj :
                (@proj1_sig (@sig message (@proto_message_prop message (IS j)))
                   (@initial_message_prop message
                      (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))
                   (@exist (@sig message (@proto_message_prop message (IS j)))
                      (@initial_message_prop message
                         (@sign message (indexed_vlsm_constrained_projection_sig j)
                            Proj))
                      (@exist message (@proto_message_prop message (IS j)) inp p)
                      Hini))
                =
               (@exist message (@proto_message_prop message (IS j)) inp p)
              ) by reflexivity.
            specialize (@protocol_generated _ _ Proj lx (s' j)); intro Generated.
            destruct Psj as [_om Psj]. specialize (Generated _om Psj).
            specialize (Generated  (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))) (Some (proj1_sig inim)) Hinip).
            rewrite Heqinim in Generated.
            rewrite Hiniproj in Generated.
            { destruct oom as [[out Pout]|]; inversion Ht.
            - assert (Hpm : protocol_message_prop X (exist _ out Pout)) by (exists s; assumption).
              destruct o; inversion H1. destruct p0; inversion H2. subst out.
              destruct (proto_message_decidable x); try contradiction.
              constructor.
              + rewrite H0. apply IHHtr. rewrite <- H0. rewrite state_update_eq.
                exists
                  (@Some (@proto_message message (IS j))
                     (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p0)).
                unfold state at 1; simpl. unfold proto_message at 1; simpl.
                unfold proto_message at 2 in Hteq; simpl in Hteq. rewrite <- Hteq.
                apply Generated.
                unfold valid. simpl. 
                assert
                  (Htt : (@transition message (IS j) (IM j) lx
                           (@pair (@state message (IS j))
                              (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                              (s' j)
                              (@Some (@sig message (@proto_message_prop message (IS j)))
                                 (@exist message (@proto_message_prop message (IS j)) inp p))))
                        =
                        (@transition message (IS j) (IM j) lx
                          (@pair (@state message (IS j))
                             (option (@sig message (@proto_message_prop message (IS j)))) 
                             (s' j)
                             (@Some (@sig message (@proto_message_prop message (IS j)))
                                (@exist message (@proto_message_prop message (IS j)) inp p))))
                ) by reflexivity.
                rewrite Htt. rewrite Hteq.
                split; try assumption.
                exists (exist _ s Hps).
                exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                simpl. split; try reflexivity. subst.  apply state_update_eq.
              + repeat split; try assumption.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))).
                  subst. simpl in Hinip. assumption.
                * rewrite Heqlx.
                  simpl.
                  assert
                    (Hteq' :
                       @transition message (IS j) (IM j) lx
                          (@pair (@state message (IS j))
                             (option (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))) 
                             (s' j)
                             (@Some (@sig message (@proto_message_prop message (IS j)))
                                (@exist message (@proto_message_prop message (IS j)) inp p)))                      
                     =
                      (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0
                        (@Some (@proto_message message (IS j))
                           (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p0)))
                    ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. split; try assumption.
                  exists (exist _ s Hps).
                  exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
              * rewrite Heqlx.
                assert
                  (Hteq' :
                    (@transition message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj) Proj lx
                       (@pair (@state message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))
                          (option (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))) 
                          (s' j)
                          (@Some (@sig message (@proto_message_prop message (IS j)))
                             (@exist message (@proto_message_prop message (IS j)) inp p))))
                     =
                      (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0
                        (@Some (@proto_message message (IS j))
                           (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p0)))
                    ) by (rewrite <- Hteq; reflexivity).
                rewrite Hteq'. subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                apply f_equal. apply exist_eq. reflexivity.
            - rewrite Heqlx. rewrite H0. 
              apply finite_ptrace_extend; try assumption.
              + apply IHHtr. exists None. destruct o; try inversion H1.
                assert
                  (Hteq' :
                    (@transition message (IS j) (IM j) lx
                      (@pair (@state message (IS j)) (option (@sig message (@proto_message_prop message (IS j)))) 
                         (s' j)
                         (@Some (@sig message (@proto_message_prop message (IS j)))
                            (@exist message (@proto_message_prop message (IS j)) inp p))))
                    =
                    (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                     (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) (s j)
                     (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j))))
                  ) by (rewrite Hteq; subst; try rewrite state_update_eq; reflexivity).
                rewrite <- Hteq'.
                apply Generated. unfold valid; simpl. 
                assert
                  (Hteq'' :
                     @transition message (IS j) (IM j) lx
                      (@pair (@state message (IS j)) (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                         (s' j)
                         (@Some (@sig message (@proto_message_prop message (IS j)))
                            (@exist message (@proto_message_prop message (IS j)) inp p)))
                    =
                    @pair (@state message (indexed_vlsm_constrained_projection_sig j))
                       (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) 
                       (s j) (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                  ) by (rewrite <- Hteq'; reflexivity).
                rewrite Hteq''. split; try assumption.
                exists (exist _ s Hps).  exists None.
                split; reflexivity.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))).
                  subst. simpl in Hinip. assumption.
                * simpl.
                  assert
                    (Hteq' :
                      @transition message (IS j) (IM j) lx
                        (@pair (@state message (IS j)) (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                           (s' j)
                           (@Some (@sig message (@proto_message_prop message (IS j)))
                              (@exist message (@proto_message_prop message (IS j)) inp p)))
                     =
                     (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0 o)
                    ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. split; try assumption.
                  exists (exist _ s Hps). 
                  exists None. destruct o; inversion H1.
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
                * assert
                    (Hteq' :
                      (@transition message (indexed_vlsm_constrained_projection_sig j) Proj lx
                         (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                            (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) (s' j)
                            (@Some (@sig message (@proto_message_prop message (IS j)))
                               (@exist message (@proto_message_prop message (IS j)) inp p))))
                       =
                      (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0 o)
                      ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. destruct o; inversion H1.
                  subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
            }
          * unfold transition in  Ht. simpl in Ht.
            destruct (transition lx (s' j, None)) eqn:Hteq.
            specialize (@protocol_generated _ _ Proj lx (s' j)); intro Generated.
            destruct Psj as [_om Psj]. specialize (Generated _om Psj).
            specialize (Generated  (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))) None).
            specialize (Generated  (protocol_initial_state Proj vlsm.s0)).
            { destruct oom as [[out Pout]|]; inversion Ht.
            - assert (Hpm : protocol_message_prop X (exist _ out Pout)) by (exists s; assumption).
              destruct o; inversion H1. destruct p; inversion H2. subst out.
              destruct (proto_message_decidable x); try contradiction.
              constructor.
              + rewrite H0. apply IHHtr. rewrite <- H0. rewrite state_update_eq.
                exists
                 (@Some (@proto_message message (IS j))
                   (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p)).
                assert
                  (Hteq' :
                      (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                         (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) s0
                         (@Some (@proto_message message (IS j))
                            (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p)))
                      =
                      (@transition message (IS j) (IM j) lx
                          (@pair (@state message (IS j)) (option (@proto_message message (IS j))) (s' j)
                             (@None (@proto_message message (IS j)))))
                  ) by (rewrite Hteq; reflexivity).

                rewrite Hteq'.
                apply Generated.
                unfold valid. simpl.
                assert
                  (Hteq'' :
                     @transition message (IS j) (IM j) lx
                      (@pair (@state message (IS j)) (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                         (s' j) (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j))))
                      =
                       (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                         (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) s0
                         (@Some (@proto_message message (IS j))
                            (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p)))
                  ) by (rewrite Hteq'; reflexivity).
                rewrite Hteq''. 
                split; try assumption.
                exists (exist _ s Hps).
                exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                simpl. split; try reflexivity. subst.  apply state_update_eq.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))).
                  subst. apply (protocol_initial_state Proj vlsm.s0).
                * rewrite Heqlx.
                  simpl.
                  assert
                    (Hteq' :
                      @transition message (IS j) (IM j) lx
                        (@pair (@state message (IS j))
                           (option (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))) 
                           (s' j) (@None (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))))
                     =
                     (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0
                        (@Some (@proto_message message (IS j))
                           (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p)))
                    ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. split; try assumption.
                  exists (exist _ s Hps). 
                  exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
              * rewrite Heqlx.
                assert
                  (Hteq' :
                    (@transition message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj) Proj lx
                       (@pair (@state message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))
                          (option (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))) 
                          (s' j) (@None (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj)))))
                     =
                     (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0
                        (@Some (@proto_message message (IS j))
                           (@exist message (fun m : message => @proto_message_prop message (IS j) m) x p)))
                    ) by (rewrite <- Hteq; reflexivity).
                rewrite Hteq'. subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                apply f_equal. apply exist_eq. reflexivity.
            - rewrite Heqlx. rewrite H0. 
              apply finite_ptrace_extend.
              + apply IHHtr. exists None. destruct o; try inversion H1.
                assert
                  (Hteq' :
                   (@transition message (IS j) (IM j) lx
                      (@pair (@state message (IS j)) (option (@proto_message message (IS j))) (s' j)
                         (@None (@proto_message message (IS j)))))
                    =
                    (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                       (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) (s j)
                       (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j))))
                  ) by (rewrite Hteq; subst; try rewrite state_update_eq; reflexivity).
                rewrite <- Hteq'.
                apply Generated. unfold valid; simpl. 
              assert
                (Hteq'' :
                  @transition message (IS j) (IM j) lx
                    (@pair (@state message (IS j)) (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                       (s' j) (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j)))) 
                  =
                  (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                     (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) (s j)
                     (@None (@proto_message message (indexed_vlsm_constrained_projection_sig j))))
                ) by (rewrite <- Hteq'; reflexivity).
              rewrite Hteq''. split; try assumption.
              exists (exist _ s Hps).  exists None.
              split; reflexivity.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IS j)) _ (@vlsm.s0 message (IS j))).
                  subst. apply (protocol_initial_state Proj vlsm.s0).
                * simpl.
                  assert
                    (Hteq' :
                      @transition message (IS j) (IM j) lx
                        (@pair (@state message (IS j)) (option (@proto_message message (indexed_vlsm_constrained_projection_sig j)))
                           (s' j) (@None (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj))))
                     =
                     (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0 o)
                    ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. split; try assumption.
                  exists (exist _ s Hps). 
                  exists None. destruct o; inversion H1.
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
              * 
                assert
                  (Hteq' :
                    (@transition message (indexed_vlsm_constrained_projection_sig j) Proj lx
                       (@pair (@state message (indexed_vlsm_constrained_projection_sig j))
                          (option (@proto_message message (indexed_vlsm_constrained_projection_sig j))) (s' j)
                          (@None (@proto_message message (@sign message (indexed_vlsm_constrained_projection_sig j) Proj)))))
                     =
                    (@pair (@state message (IS j)) (option (@proto_message message (IS j))) s0 o)
                    ) by (rewrite <- Hteq; reflexivity).
                rewrite Hteq'. subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                destruct o; inversion H1. reflexivity.
            }
        + assert (Heq : s j = s' j); try (rewrite Heq in IHHtr; apply IHHtr; assumption).
          unfold transition in  Ht. simpl in Ht.
          destruct iom as [[im Pim]|].
          * destruct (proto_message_decidable im) as [Pimj | _]
            ; try inversion Hv.
            destruct (transition lx (s' x, Some (exist proto_message_prop im Pimj))).
            inversion Ht. rewrite state_update_neq; try reflexivity; assumption.
          * destruct (transition lx (s' x, None)).
            inversion Ht. rewrite state_update_neq; try reflexivity; assumption.
    Qed.

  End fixed_projection.

End projections.


Section free_projections. 

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          {IS : index -> LSM_sig message}
          (IM : forall i : index, VLSM (IS i))
          .


  Definition indexed_vlsm_free_projection_sig
             (i : index)
    : LSM_sig message
    :=
      indexed_vlsm_constrained_projection_sig i0 IM (free_constraint IS) i.

  Definition indexed_vlsm_free_projection
             (i : index)
    : VLSM (indexed_vlsm_free_projection_sig i)
    :=
      indexed_vlsm_constrained_projection i0 IM (free_constraint IS) i.
End free_projections.
