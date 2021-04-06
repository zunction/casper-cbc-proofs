Require Import Bool List ListSet Reals FinFun Program RelationClasses Relations Relations_1 Sorting Basics.
Require Import Lia.
Import ListNotations.
From CasperCBC
  Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras Lib.TopSort
    CBC.Protocol CBC.Common CBC.Definitions
    VLSM.Common VLSM.Composition VLSM.Decisions VLSM.Equivocation VLSM.ProjectionTraces.
    

Section FullNodeLike.

Context
  {CV : consensus_values}
  {CV_eq_dec : EqDecision C}
  {message : Type}
  {mdec : EqDecision message}
  (happens_before : message -> message -> Prop)
  (happens_before' := clos_trans _ happens_before)
  (Hstrict : StrictOrder happens_before')
  (happens_before_dec : RelDecision happens_before)
  (happens_before'_dec : RelDecision happens_before')
  (predSet : message -> set message)
  (HpredSetCorrect : forall (m1 m2 : message), happens_before m1 m2 <-> In m1 (predSet m2))
  (downSet : message -> set message)
  (downSet' := fun (m : message) => set_union mdec (downSet m) [m])
  (HdownSetCorrect : forall (m1 m2 : message), happens_before' m1 m2 <-> In m1 (downSet m2))
  {index : Type}
  {index_listing : list index}
  (n := length index_listing)
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  {i0 : Inhabited index}
  (sender : message -> index)
  {IM : index -> VLSM message}
  (computable_sent : forall (i : index), computable_sent_messages (IM i))
  (computable_received : forall (i : index), computable_received_messages (IM i)). 
  
  Lemma minimal_element_P
    (P : message -> Prop)
    (Pdec : forall m, Decision (P m))
    (m : message)
    (Hm : P m) :
    exists m_min, P m_min /\ (
      forall m', P m' -> ~ happens_before' m' m_min).
  Proof.
    remember (downSet m) as d.
    remember (filter (fun m => bool_decide (P m)) d) as dP.
    destruct dP.
    - exists m.
      split;[intuition|].
      intros.
      intros contra.
      specialize (HdownSetCorrect m' m) as Hdown.
      apply Hdown in contra.
      assert (In m' (filter (fun m => bool_decide (P m)) d)). {
        apply filter_In.
        rewrite Heqd. 
        split;[intuition|].
        apply bool_decide_eq_true; intuition.
      }
      rewrite <- HeqdP in H0.
      intuition.
    - remember (min_predecessors happens_before' (m0 :: dP) dP m0) as m_min.
      assert (Hmin_inf : In m_min (m0 :: dP)). {
        specialize (min_predecessors_in happens_before' (m0 :: dP) dP m0) as Hin'.
        destruct Hin'.
        + rewrite Heqm_min. rewrite H. intuition.
        + rewrite Heqm_min. intuition.
      }
      
      assert (Hmin : In m_min d /\ P m_min). {
        rewrite HeqdP in Hmin_inf.
        apply filter_In in Hmin_inf.
        rewrite bool_decide_eq_true in Hmin_inf.
        intuition.
      }
      destruct Hmin as [Hmind HminP].
      exists m_min.
      split.
      + intuition.
      + intros.
        specialize (min_predecessors_zero happens_before' (m0 :: dP) (fun m => True)) as Hzero.
        spec Hzero. {
          rewrite Forall_forall.
          intros. intuition.
        }
        spec Hzero. {
          unfold preceeds_P.
          simpl.
          split.
          - unfold Irreflexive. unfold RelationClasses.Reflexive. intros.
            unfold complement. apply StrictOrder_Irreflexive.
          - unfold RelationClasses.Transitive. intros.
            apply (RelationClasses.StrictOrder_Transitive (` x) (` y) (` z)); intuition.
        }
        specialize (Hzero dP m0 eq_refl).
        destruct (@bool_decide (In m' d) (in_dec decide_eq m' d)) eqn : eq.
        * rewrite bool_decide_eq_true in eq. 
          assert (In m' (filter (fun m1 : message => bool_decide (P m1)) d)). {
            apply filter_In.
            rewrite bool_decide_eq_true.
            intuition.
          }
          intros contra.
          apply zero_predecessors in Hzero.
          rewrite Forall_forall in Hzero.
          specialize (Hzero m').
          spec Hzero. {
            rewrite HeqdP.
            intuition.
          }
          rewrite bool_decide_eq_false in Hzero.
          rewrite Heqm_min in contra.
          intuition.
        * rewrite bool_decide_eq_false in eq.
          intros contra.
          assert (~ happens_before' m' m). {
            intros contra'.
            apply HdownSetCorrect in contra'.
            rewrite Heqd in eq.
            intuition.
          }
          assert (happens_before' m' m). {
            move Hstrict at bottom.
            unfold happens_before'.
            apply t_trans with (y := m_min).
            intuition.
            rewrite Heqd in Hmind.
            apply HdownSetCorrect in Hmind.
            intuition.
          }
          intuition.
  Qed.
  
  Definition senders 
      (s : set message) := 
      List.map sender s.
  
  Definition sent_set 
    (i : index) 
    (s : vstate (IM i)) := @sent_messages_fn message (IM i) _ s.
  
  Definition received_set
    (i : index)
    (s : vstate (IM i)) := @received_messages_fn message (IM i) _ s.
  
  Definition observed_set
    (i : index)
    (s : vstate (IM i)) := set_union mdec (sent_set i s) (received_set i s).
    
  Definition has_justification 
    (i : index)
    (s : vstate (IM i))
    (m : message) :=
    incl (predSet m) (received_set i s).
  
  Definition has_justification_option
    (i : index)
    (s : vstate (IM i))
    (om : option message) :=
    match om with
    | None => True
    | Some m => has_justification i s m
    end.
  
  Definition fullnode_constraint
    (l : composite_label IM)
    (siom : composite_state IM * option message) :=
    let (s, iom) := siom in
    let i := projT1 l in
    let (s', oom) := vtransition (IM i) (projT2 l) ((s i), iom) in
    has_justification_option i (s i) iom /\ has_justification_option i (s i) oom.
    
  Definition is_equivocating_from_set
    (sm : set message)
    (i : index) :=
    exists (m1 m2 : message), 
    In m1 sm /\
    sender m1 = i /\
    In m2 sm /\ 
    sender m2 = i /\
    ~comparable happens_before m1 m2.
      
  Definition is_equivocating_from_message
     (m : message) :=
     is_equivocating_from_set (downSet m).
    
  Local Instance is_equivocating_from_message_dec : RelDecision is_equivocating_from_message.
  Proof.
  Admitted.
  
  Definition equivocators_from_message
    (m : message) : set index := 
    List.filter (fun (i : index) => (bool_decide (is_equivocating_from_message m i))) index_listing.
  
  Definition honest_validators_from_message
    (m : message) : set index := 
    List.filter (fun (i : index) => negb (bool_decide (is_equivocating_from_message m i))) index_listing.
    
  Definition honest_votes_count 
    (m : message) : nat :=
    length (honest_validators_from_message m).
    
  Definition honest_messages
    (m : message) : set message :=
    List.filter (fun (m' : message) => inb decide_eq (sender m') (honest_validators_from_message m)) (predSet m).
      
  Definition latest_messages
    (m : message) : set message :=
    ListSetExtras.get_maximal_elements (fun m1 m2 => bool_decide (happens_before m1 m2)) (honest_messages m).
    
Section Inspector.

Context
    (X := composite_vlsm IM fullnode_constraint)
    (vote : message -> option C)
    (Hvote : forall (m : message) (oc : option C),
             vote m = oc ->
             (forall (oc' : option C),
             List.count_occ option_eq_dec (List.map vote (latest_messages m)) oc >= 
             List.count_occ option_eq_dec (List.map vote (latest_messages m)) oc')). 
    
    Definition composite_sent
      (s : vstate X) := 
    fold_right (set_union decide_eq) nil (List.map (fun i => sent_set i (s i)) index_listing).
    
    Definition composite_received
      (s : vstate X) := 
    fold_right (set_union decide_eq) nil (List.map (fun i => received_set i (s i)) index_listing).
  
    Definition composite_observed
      (s : vstate X) := 
    fold_right (set_union decide_eq) nil (List.map (fun i => observed_set i (s i)) index_listing).
  
    Lemma protocol_state_closed 
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (m : message) :
      In m (composite_observed s) -> incl (downSet m) (composite_observed s).
    Proof.
    Admitted.
    
    Definition is_equivocating_from_state
      (s : vstate X) :=
      is_equivocating_from_set (composite_observed s).
    
    Local Instance is_equivocating_from_state_dec : RelDecision is_equivocating_from_state.
    Proof.
    Admitted.
    
    Definition equivocators_from_state
      (s : vstate X) :=
      List.filter (fun i => negb (bool_decide (is_equivocating_from_state s i))) index_listing.
      
    Record committee_skeleton : Type := {
      com_state : vstate X;
      value : C;
      com : list (set message);
      q : nat;
      k := length com - 1;
      get_base := last_error com;
      get_top := hd_error com;
    }.
    
    Definition unanimity 
      (value : C)
      (sm : set message) :=
      forall (m : message), In m sm -> vote m = Some value.
      
    Definition honesty
      (s : vstate X)
      (sm : set message) :=
      forall (i : index), In i (senders sm) -> ~ In i (equivocators_from_state s).
      
    Definition convexity 
      (sm : set message) :=
      forall (m1 m2 m3 : message),
      In m1 sm /\ In m3 sm ->
      sender m1 = sender m2 /\ sender m3 = sender m2 ->
      happens_before' m1 m2 /\ happens_before' m2 m3 ->
      In m2 sm.
      
    (* Definition of Ci' *)
    Definition relevant_messages
      (sm1 sm2 : set message) :=
      List.filter (fun m => inb decide_eq (sender m) (senders sm1)) sm2. 
    
    Definition density
      (sm1 sm2 : set message)
      (q : nat) :=
      forall (m : message),
      In m sm1 ->
      length (senders (filter (fun v => bool_decide (happens_before' v m)) (relevant_messages sm1 sm2))) >= q.
    
    Inductive valid_com_prop : vstate X -> C -> nat -> list (set message) -> Prop :=
    | valid_com_base 
      (s : vstate X)
      (value : C)
      (q : nat)
      (sm : set message)
      (H : unanimity value sm /\ honesty s sm /\ convexity sm) : valid_com_prop s value q [sm]
    | valid_com_ind 
        (s : vstate X)
        (value : C)
        (q : nat)
        (sm1 sm2 : set message) 
        (l : list (set message))
        (Hincl : incl sm2 sm1)
        (Hdensity : density sm1 sm2 q)
        (Hconv : convexity sm1)
        (Hgood : valid_com_prop s value q (sm2 :: l)) : valid_com_prop s value q (sm1 :: (sm2 :: l)).
    
    Definition committee : Type := {
      comskel : committee_skeleton | valid_com_prop (com_state comskel) (value comskel) (q comskel) (com comskel)
    }.
    
    Theorem main
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Com : committee)
      (skel := proj1_sig Com)
      (q := (q skel))
      (k := (k skel))
      (value := (value skel))
      (base top : set message)
      (Hbase : get_base skel = Some base)
      (Htop : get_top skel = Some top)
      (Hstate : com_state skel = s)
      (Pdown := fun m' => 
        In m' (composite_observed s) /\
        vote m' <> Some value /\
        (exists m'',  
        In m'' (downSet m') /\ 
        In m'' top))
      (Htouch : exists m, Pdown m) :
      length (equivocators_from_state s) * 2 ^ k >= 
      (2 * q - n) * (2 ^ k - 1).
    Proof.
      destruct Com as [skel' Hcom]. simpl in *.
      subst skel.
      simpl in *.
      remember (com_state skel') as com_state'.
      remember (Inspector.value skel') as value'.
      remember (Inspector.q skel') as q'.
      remember (com skel') as com'.
      induction Hcom.
      - simpl in *.
        unfold k. unfold Inspector.k. 
        rewrite <- Heqcom'. simpl. lia.
      - destruct Htouch as [u' Hdown].
          
        assert (HPdec : forall m, Decision (Pdown m)). {
          intros. unfold Decision.
          unfold Pdown.
          apply Decision_and.
          - apply in_dec; apply mdec.
          - apply Decision_and.
            + apply Decision_not. apply decide_eq.
            + admit.
        }
        
        specialize (minimal_element_P Pdown HPdec u' Hdown) as Hminimal. 
        destruct Hminimal as [u [Hu_P Hu_minimal]].
        
        unfold Pdown in Hu_P.
        rewrite <- and_assoc in Hu_P.
        destruct Hu_P as [Hu_P Huc].
        destruct Huc as [uk Huk].
        
        assert (Huk_u : forall m', happens_before' m' uk -> happens_before' m' u). {
          intros.
          apply t_trans with (y := uk).
          intuition.
          destruct Huk as [Huk _].
          apply HdownSetCorrect in Huk.
          intuition.
        }
        
        remember (equivocators_from_message u) as Eu.
        
        remember (senders (filter (fun v => bool_decide (happens_before' v u)) (relevant_messages sm1 sm2))) as Vk_1.
        
        assert (HVk1_sz : length Vk_1 >= q). {
          rewrite HeqVk_1.
          move Hdensity at bottom.
          unfold density in Hdensity.
          unfold Pdown in Hu_P.
          specialize (Hdensity uk).
          spec Hdensity. {
            destruct Hu_P as [_ Hu_P].
            move Htop at bottom.
            unfold get_top in Htop.
            rewrite <- Heqcom' in Htop.
            simpl in Htop.
            inversion Htop.
            intuition.
          }
          unfold q.
          unfold senders.
          unfold senders in Hdensity.
          rewrite map_length.
          rewrite map_length in Hdensity.
          assert (length
                  (filter (fun v : message => bool_decide (happens_before' v u)) 
                  (relevant_messages sm1 sm2)) >=
                  length
                  (filter (fun v : message => bool_decide (happens_before' v uk))
                  (relevant_messages sm1 sm2))). {
            apply filter_length_fn.
            rewrite Forall_forall.
            intros.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true in H0.
            apply Huk_u.
            intuition.
          }
          lia.
        }
        
        remember (filter (fun i => bool_decide (is_equivocating_from_message u i)) Vk_1) as Veq.
        remember (filter (fun m' => negb (bool_decide (vote m' = Some value))) (latest_messages u)) as latest_divergent.
        remember (filter (fun (i : index) => inb decide_eq i (senders latest_divergent)) Vk_1) as Vchange.
        
        assert (Heq_change_disjoint : ~ (exists i, In i Veq /\ In i Vchange)). {
          intros contra.
          destruct contra as [i contra].
          destruct contra as [Hin_veq Hin_change].
          rewrite HeqVeq in Hin_veq.
          rewrite HeqVchange in Hin_change.
          apply filter_In in Hin_veq.
          apply filter_In in Hin_change.
          rewrite bool_decide_eq_true in Hin_veq.
          rewrite <- in_correct in Hin_change.
          rewrite Heqlatest_divergent in Hin_change.
          destruct Hin_change as [_ Hin_change].
          apply in_map_iff in Hin_change.
          destruct Hin_change as [m'' [Hm''_sender Hm''_in]].
          apply filter_In in Hm''_in.
          destruct Hm''_in as [Hm''_in _].
          unfold latest_messages in Hm''_in.
          apply filter_In in Hm''_in.
          destruct Hm''_in as [Hm''_in _].
          unfold honest_messages in Hm''_in.
          apply filter_In in Hm''_in.
          destruct Hm''_in as [_ Hm''_in].
          rewrite <- in_correct in Hm''_in.
          unfold honest_validators_from_message in Hm''_in.
          apply filter_In in Hm''_in.
          destruct Hm''_in as [_ Hm''_in].
          rewrite negb_true_iff in Hm''_in.
          rewrite bool_decide_eq_false in Hm''_in.
          rewrite Hm''_sender in Hm''_in.
          intuition.
        }
        
        assert (Hineq1 : 2 * (q - (length Veq) - (length Vchange)) <= n - length Eu). {
          move Hvote at bottom.
          assert (Hvote' := Hvote).
          
          assert (~ 2 * (q - (length Veq) - (length Vchange)) > n - length Eu). {
            intros contra.
            assert (vote m = Some value). {
            
            }
          }
          lia.
        }
        
    Admitted.
      
End Inspector.
End FullNodeLike.