Require Import Bool List ListSet Reals FinFun Program RelationClasses Relations Relations_1 Sorting Basics ZArith.
Require Import Lia.
Require Import ZArith.BinInt.
Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras Lib.TopSort
    CBC.Protocol CBC.Common CBC.Definitions
    VLSM.Common VLSM.Composition VLSM.Decisions VLSM.Equivocation VLSM.ProjectionTraces.

From stdpp Require Import base fin_sets.

Section FullNodeLike.

Context
  {CV : consensus_values}
  {CV_eq_dec : Classes.EqDecision C}
  {Cm Ci : Type}
  {message : Type}
  {index : Type}
  `{HfinSetMessage : FinSet message Cm}
  `{HfinSetIndex : FinSet index Ci}
  {mdec : Classes.EqDecision message}
  (happens_before : message -> message -> Prop)
  (happens_before' := clos_trans _ happens_before)
  (Hstrict : StrictOrder happens_before')
  (happens_before_dec : RelDecision happens_before)
  (happens_before'_dec : RelDecision happens_before')
  (predSet : message -> Cm)
  (HpredSetCorrect : forall (m1 m2 : message), happens_before m1 m2 <->  m1 ∈ (predSet m2))
  (downSet : message -> Cm)
  (downSet' := fun (m : message) => (downSet m) ∪ {[ m ]})
  (HdownSetCorrect : forall (m1 m2 : message), happens_before' m1 m2 <-> m1 ∈ (downSet m2))
  {index_listing : list index}
  (n := length index_listing)
  {Hfinite : Listing index_listing}
  {idec : Classes.EqDecision index}
  {i0 : Classes.Inhabited index}
  (sender : message -> index)
  {IM : index -> VLSM message}
  (computable_sent : forall (i : index), computable_sent_messages (IM i))
  (computable_received : forall (i : index), computable_received_messages (IM i)). 
  
  Lemma something_pretentious : 
    StrictOrder (preceeds_P happens_before' (fun _ : message => True)).
  Proof.
    unfold preceeds_P.
    simpl.
    split.
    - unfold Irreflexive. unfold RelationClasses.Reflexive. intros.
      unfold complement. apply StrictOrder_Irreflexive.
    - unfold RelationClasses.Transitive. intros.
      apply (RelationClasses.StrictOrder_Transitive (` x) (` y) (` z)); intuition.
  Qed.
  
  Lemma minimal_element_P
    (P : message -> Prop)
    (Pdec : forall m, Decision (P m))
    (m : message)
    (Hm : P m) :
    ∃ m_min, P m_min /\ (
      forall m', P m' -> ~ happens_before' m' m_min).
  Proof.
    remember (downSet m) as d.
    remember (filter (fun m => bool_decide (P m)) (elements d)) as dP.
    destruct dP eqn : eq_dP.
    - exists m.
      split;[intuition|].
      intros.
      intros contra.
      specialize (HdownSetCorrect m' m) as Hdown.
      apply Hdown in contra.
      assert (Hm' : m' ∈ (set_filter (fun m => bool_decide (P m)) _ d)). {
        apply elem_of_filter.
        rewrite Heqd. 
        split;[intuition|].
        intuition.
      }
      unfold set_filter in Hm'.
      rewrite <- HeqdP in Hm'.
      simpl in Hm'. set_solver.
    - remember (@min_predecessors _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as m_min.
      assert (Hmin_inf : In m_min (m0 :: dP)). {
        specialize (@min_predecessors_in _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as Hin'.
        destruct Hin' as [Hin'|Hin'].
        + rewrite Heqm_min. rewrite Hin'. set_solver.
        + rewrite Heqm_min. set_solver.
      }
      
      assert (Hmin : m_min ∈ d /\ P m_min). {
        rewrite eq_dP in Hmin_inf.
        rewrite HeqdP in Hmin_inf.
        destruct Hmin_inf as [Hmin_f|Hmin_f].
        + rewrite Hmin_f in HeqdP.
          assert (Hmin : m_min ∈ set_filter (λ m1 : message, bool_decide (P m1)) _ d). {
            unfold set_filter.
            rewrite <- HeqdP.
            intuition set_solver.
          }
          apply elem_of_filter in Hmin.
          set_solver.
        + assert (Hmin : m_min ∈ set_filter (λ m1 : message, bool_decide (P m1)) _ d). {
            unfold set_filter.
            apply elem_of_list_to_set.
            rewrite elem_of_list_In.
            intuition.
          }
          apply elem_of_filter in Hmin.
          set_solver.
      }
      destruct Hmin as [Hmind HminP].
      exists m_min.
      split.
      + intuition.
      + intros.
        specialize (@min_predecessors_zero _ happens_before' happens_before'_dec (m0 :: dP) (fun m => True)) as Hzero.
        spec Hzero. {
          rewrite Forall_forall.
          intros. intuition.
        }
        
        spec Hzero. apply something_pretentious.
        
        specialize (Hzero dP m0 eq_refl).
        
        (*destruct (@bool_decide (In m' (elements d)) (in_dec decide_eq m' (elements d))) eqn : eq. *)
        destruct (@decide (m' ∈ d) (elem_of_dec_slow m' d)).
        * assert (Hm' : m' ∈ (set_filter (fun m1 : message => bool_decide (P m1)) _ d)). {
            apply elem_of_filter.
            set_solver.
          }
          
          intros contra.
          apply zero_predecessors in Hzero.
          rewrite Forall_forall in Hzero.
          specialize (Hzero m').
          spec Hzero. {
            rewrite eq_dP.
            rewrite HeqdP.
            rewrite elem_of_list_In.
            simpl. right.
            unfold set_filter in Hm'.
            apply elem_of_list_to_set in Hm'.
            apply elem_of_list_In.
            set_solver.
          }
          rewrite bool_decide_eq_false in Hzero.
          rewrite Heqm_min in contra.
          intuition.
        * intros contra.
          assert (~ happens_before' m' m). {
            intros contra'.
            apply HdownSetCorrect in contra'.
            intuition set_solver.
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
      (s : Cm) : Ci := 
      set_map sender s.
  
  Definition sent_set 
    (i : index) 
    (s : vstate (IM i)) : Cm := list_to_set (@sent_messages_fn message (IM i) _ s).
  
  Definition received_set
    (i : index)
    (s : vstate (IM i)) : Cm := list_to_set (@received_messages_fn message (IM i) _ s).
  
  Definition observed_set
    (i : index)
    (s : vstate (IM i)) : Cm := (sent_set i s) ∪ (received_set i s).
    
  Definition has_justification 
    (i : index)
    (s : vstate (IM i))
    (m : message) :=
    (predSet m) ⊆ (received_set i s).
  
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
    (sm : Cm)
    (i : index) :=
    exists (m1 m2 : message), 
    m1 ∈ sm /\
    sender m1 = i /\
    m2 ∈ sm /\ 
    sender m2 = i /\
    ~comparable happens_before' m1 m2.
  
  Local Instance is_equivocating_from_set_dec : RelDecision is_equivocating_from_set.
  Proof.
  Admitted.
  
  Definition index_set : Ci := (list_to_set index_listing).
  
  Definition equivocators_from_set 
    (sm : Cm) :=
    set_filter (fun i => bool_decide (is_equivocating_from_set sm i)) _ index_set.
      
  Definition is_equivocating_from_message
     (m : message) :=
     is_equivocating_from_set (downSet m).
    
  Local Instance is_equivocating_from_message_dec : RelDecision is_equivocating_from_message.
  Proof.
  Admitted.
  
  Definition equivocators_from_message
    (m : message) : Ci := 
    set_filter (fun (i : index) => (bool_decide (is_equivocating_from_message m i))) _ index_set.
  
  Definition honest_validators_from_message
    (m : message) : Ci := 
    set_filter (fun (i : index) => negb (bool_decide (is_equivocating_from_message m i))) _ index_set.
    
  Definition honest_votes_count 
    (m : message) : nat :=
    size (honest_validators_from_message m).
    
  Definition messages_from
    (m : message) 
    (i : index) : Cm :=
    set_filter (fun (m' : message) => bool_decide (sender m' = i)) _ (downSet m).
    
  Print messages_from.
  
  Definition latest_message_from
    (m : message)
    (i : index) : option message :=
  (@TopSort.get_maximal_element _ mdec happens_before' happens_before'_dec (elements (messages_from m i))).
  
  Definition latest_message_from_strict
    (m : message)
    (i : index) : option message :=
    match bool_decide (is_equivocating_from_message m i) with
    | true => None
    | false => latest_message_from m i
    end.
  
  Lemma latest_message_in_messages_from
    (m m' : message)
    (i : index) 
    (Hlatest : latest_message_from m i = Some m') :
    m' ∈ (messages_from m i).
  Proof.
    unfold latest_message_from in Hlatest.
    apply maximal_element_in with (P := fun x => True) in Hlatest.
    apply elem_of_list_In in Hlatest. set_solver.
    apply something_pretentious.
    rewrite Forall_forall;intuition.
  Qed.
  
  Lemma latest_message_from_compares
    (m m' : message)
    (i : index)
    (Hlatest : latest_message_from m i = Some m') :
    happens_before' m' m.
  Proof.
    unfold latest_message_from in Hlatest.
    apply latest_message_in_messages_from in Hlatest.
    unfold messages_from in Hlatest.
    apply elem_of_filter in Hlatest.
    rewrite <- HdownSetCorrect in Hlatest.
    intuition.
  Qed.
  
  Lemma latest_message_from_exists
    (m : message)
    (i : index)
    (Hsome : exists mi, mi ∈ (messages_from m i)) :
    exists mi', latest_message_from m i = Some mi'.
  Proof.
    apply get_maximal_element_some with (P := fun x => True).
    apply something_pretentious.
    apply Forall_forall. intuition.
    destruct Hsome as [mi Hmi].
    
    destruct (elements (messages_from m i)) eqn : eq.
    - apply elements_empty' in eq.
      set_solver.
    - intuition congruence.
  Qed. 
  
  Definition latest_messages
    (m : message) : Cm :=
  list_to_set (ListExtras.cat_option (List.map (latest_message_from m) (elements (honest_validators_from_message m)))).
  
  Lemma latest_message_in_latest_messages
    (m m' : message)
    (Hlatest : latest_message_from m (sender m') = Some m') 
    (Hne : ~ is_equivocating_from_message m (sender m')) :
    m' ∈ (latest_messages m).
  Proof.
    unfold latest_messages.
    apply elem_of_list_to_set.
    apply elem_of_list_In.
    apply in_cat_option.
    exists (Some m').
    split;[|intuition].
    apply in_map_iff.
    exists (sender m').
    split;[intuition|].
    apply elem_of_list_In.
    apply elem_of_elements.
    apply elem_of_filter.
    split.
    - apply Is_true_iff_eq_true.
      rewrite negb_true_iff.
      rewrite bool_decide_eq_false.
      intuition.
    - unfold index_set.
      apply elem_of_list_to_set.
      apply elem_of_list_In.
      apply Hfinite.
  Qed.
  
  Lemma latest_message_sender
    (m m' : message)
    (i : index)
    (Hlatest : latest_message_from m i = Some m') :
    i = sender m'.
  Proof.
     unfold latest_message_from in Hlatest.
     apply maximal_element_in with (P := (fun x => True)) in Hlatest.
     - apply elem_of_list_In in Hlatest.
       apply elem_of_elements in Hlatest.
       apply elem_of_filter in Hlatest.
       rewrite <- Is_true_iff_eq_true in Hlatest.
       rewrite bool_decide_eq_true in Hlatest.
       intuition.
     - apply something_pretentious.
     - rewrite Forall_forall; intuition.
  Qed.
  
  Lemma latest_message_sender_info
    (m m' : message)
    (Hinm' : m' ∈ (latest_messages m)) : 
    ~ is_equivocating_from_message m (sender m')
    /\ latest_message_from m (sender m') = Some m'.
  Proof.
    unfold latest_messages in Hinm'.
    apply elem_of_list_to_set in Hinm'.
    apply elem_of_list_In in Hinm'.
    apply in_cat_option in Hinm'.
    destruct Hinm' as [om [Hom Heqom]].
    apply in_map_iff in Hom.
    destruct Hom as [omi [Hlatest Hhonest]].
    unfold honest_validators_from_message in Hhonest.
    apply elem_of_list_In in Hhonest.
    apply elem_of_elements in Hhonest.
    apply elem_of_filter in Hhonest.
    rewrite <- Is_true_iff_eq_true in Hhonest.
    destruct Hhonest as [Hhonest Hhonest'].
    rewrite negb_true_iff in Hhonest.
    rewrite bool_decide_eq_false in Hhonest.
    
    assert (Homi : omi = sender m'). {
      rewrite Heqom in Hlatest.
      apply latest_message_sender in Hlatest.
      intuition.
    }
    rewrite <- Homi at 1.
    rewrite Homi in Hlatest.
    rewrite Heqom in Hlatest.
    intuition.
  Qed.
  
  Lemma non_equiv_compare 
    (u v w: message)
    (Hsenders : sender v = sender w)
    (Hless : happens_before' v u /\ happens_before' w u) 
    (Hnon_equiv : ~ (is_equivocating_from_message u (sender v))) :
    comparable happens_before' v w.
  Proof.
    unfold is_equivocating_from_message in Hnon_equiv.
    unfold is_equivocating_from_set in Hnon_equiv.
    destruct (bool_decide (comparable happens_before' v w)) eqn : eqb.
    - rewrite bool_decide_eq_true in eqb. intuition.
    - rewrite bool_decide_eq_false in eqb.
      contradict Hnon_equiv.
      exists v. exists w.
      split;[apply HdownSetCorrect;intuition|].
      split;[intuition|].
      split;[apply HdownSetCorrect;intuition|].
      split;[symmetry;intuition|intuition].
  Qed.
  
  Lemma compare_messages1
    (u v v_dif: message)
    (Hsenders : sender v = sender v_dif)
    (Hlatest : v_dif ∈ (latest_messages u))
    (Hdif : v <> v_dif)
    (Hv_less : happens_before' v u) :
    happens_before' v v_dif.
  Proof.
    apply latest_message_sender_info in Hlatest as Hlatest'.
    
    assert (Hcomp : comparable happens_before' v v_dif). {
      apply non_equiv_compare with (u := u).
      intuition.
      split;[intuition|].
      apply latest_message_from_compares with (i := sender v_dif).
      intuition.
      rewrite Hsenders. intuition.
    }
    
    destruct Hcomp as [|Hcomp];[intuition congruence|].
    destruct Hcomp as [Hcomp|Hcomp].
    - intuition.
    - apply latest_message_sender_info in Hlatest.
      destruct Hlatest as [_ Hlatest].
      apply TopSort.get_maximal_element_correct with (a := v) (P := fun x => true) in Hlatest.
      intuition.
      apply something_pretentious.
      rewrite Forall_forall. intros. intuition.
      intros a b Hab.
      destruct Hab as [Hina Hinb].
      rewrite <- elem_of_list_In in Hina, Hinb.
      rewrite elem_of_elements in Hina, Hinb.
      apply elem_of_filter in Hina.
      apply elem_of_filter in Hinb.
      rewrite <- Is_true_iff_eq_true in Hina, Hinb.
      rewrite bool_decide_eq_true in Hina, Hinb.
      apply non_equiv_compare with (u := u).
      intuition congruence.
      rewrite <- HdownSetCorrect in Hina, Hinb.
      intuition.
      intuition congruence.
      apply elem_of_list_In.
      apply elem_of_elements.
      apply elem_of_filter.
      rewrite <- HdownSetCorrect.
      rewrite <- Is_true_iff_eq_true.
      rewrite bool_decide_eq_true.
      intuition.
  Qed. 
 
Section Inspector.

Context
    (X := composite_vlsm IM fullnode_constraint)
    (vote : message -> option C)
    (Hvote : forall (m : message) (oc : option C),
             vote m = oc ->
             (forall (oc' : option C),
             List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc >= 
             List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc')). 
   
    Definition count_votes_for
      (m : message)
      (oc : option C) :=
    List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc.
    
    Definition composite_sent
      (s : vstate X) : Cm := ⋃ (List.map (fun i : index => sent_set i (s i)) index_listing).
    
    Definition composite_received
      (s : vstate X) : Cm := ⋃ (List.map (fun i : index => received_set i (s i)) index_listing).
      
    Definition composite_observed
      (s : vstate X) := ⋃ (List.map (fun i : index => received_set i (s i)) index_listing).
    
    Lemma protocol_state_closed
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (u v : message)
      (Hcomp : happens_before' v u)
      (Hinu : u ∈ (composite_observed s)) :
      v ∈ (composite_observed s).
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
      set_filter (fun i => negb (bool_decide (is_equivocating_from_state s i))) _ index_set.
    
    Program Definition divergent_last_messages 
      (m : message)
      (v : option C) :=
    set_filter (fun m' => negb (@bool_decide (vote m' = v) _)) _ (latest_messages m).
    Next Obligation.
      intros.
      apply decide_eq.
    Defined.
    Next Obligation.
      intros.
    Admitted.
    
    Definition A
      (m : message)
      (v : option C)
      (carrier : Cm) :=
      let divergent_senders := senders (divergent_last_messages m v) in
      (equivocators_from_message m) ∪ (equivocators_from_set (carrier ∪ (downSet m)) ∩ divergent_senders).
      
    
    Record committee_skeleton : Type := {
      com_state : vstate X;
      value : C;
      com : list Cm;
      q : nat;
      k := length com - 1;
      get_base := last_error com;
      get_top := hd_error com;
    }.
    
    Definition unanimity 
      (value : C)
      (sm : Cm) :=
      forall (m : message), m ∈ sm -> vote m = Some value.
      
    Definition honesty
      (s : vstate X)
      (sm : Cm) :=
      forall (i : index), i ∈ (senders sm) -> i ∉ (equivocators_from_state s).
      
    Definition convexity 
      (sm : Cm) :=
      forall (m1 m2 m3 : message),
      m1 ∈ sm /\ m3 ∈ sm ->
      sender m1 = sender m2 /\ sender m3 = sender m2 ->
      happens_before' m1 m2 /\ happens_before' m2 m3 ->
      m2 ∈ sm.
      
    (* Definition of Ci' *)
    Definition relevant_messages
      (sm1 sm2 : Cm) :=
      set_filter (fun m => inb decide_eq (sender m) (elements (senders sm1))) _ sm2. 
    
    Definition density
      (sm1 sm2 : Cm)
      (q : nat) :=
      forall (m : message),
      m ∈ sm1 ->
      size (senders (set_filter (fun v => bool_decide (happens_before' v m)) _ (relevant_messages sm1 sm2))) >= q.
    
    Inductive valid_com_prop : vstate X -> C -> nat -> list Cm -> Prop :=
    | valid_com_base 
      (s : vstate X)
      (value : C)
      (q : nat)
      (sm : Cm)
      (H : unanimity value sm /\ honesty s sm /\ convexity sm) : valid_com_prop s value q [sm]
    | valid_com_ind 
        (s : vstate X)
        (value : C)
        (q : nat)
        (sm1 sm2 : Cm) 
        (l : list Cm)
        (Hincl : sm1 ⊆ sm2)
        (Hdensity : density sm1 sm2 q)
        (Hconv : convexity sm1)
        (Hgood : valid_com_prop s value q (sm2 :: l)) : valid_com_prop s value q (sm1 :: (sm2 :: l)).
    
    Definition committee : Type := {
      comskel : committee_skeleton | valid_com_prop (com_state comskel) (value comskel) (q comskel) (com comskel)
    }.
    
    Local Open Scope Z_scope.
    
    (* Local Coercion Z_of_nat : nat >-> Z. *)
    
    Theorem main
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Com : committee)
      (skel := proj1_sig Com)
      (q := (q skel))
      (k := (k skel))
      (value := (value skel))
      (base top : Cm)
      (Hbase : get_base skel = Some base)
      (Htop : get_top skel = Some top)
      (Hstate : com_state skel = s)
      (Pdown := fun m' => 
        m' ∈ (composite_observed s) /\
        vote m' <> Some value /\
        (exists m'',  
        m'' ∈ (downSet m') /\ 
        m'' ∈ top))
      (Htouch : exists m, Pdown m) :
      (size (equivocators_from_state s)) * (2 ^ k) >=  
      (2 * q - n) * (2 ^ k - 1).
    Proof.
      destruct Com as [skel' Hcom]. simpl in *.
      subst skel.
      simpl in *.
      remember (com_state skel') as com_state'.
      remember (Inspector.value skel') as value'.
      remember (Inspector.q skel') as q'.
      remember (com skel') as com'.

      generalize dependent base.
      generalize dependent top.
      generalize dependent skel'.
      induction Hcom.
      - intros.
        simpl in *.
        unfold k0. unfold Inspector.k.
        rewrite <- Heqcom'. simpl. lia.
      - intros.
        
        destruct Htouch as [u' Hdown].
        assert (HPdec : forall m, Decision (Pdown m)). {
          intros. unfold Decision.
          unfold Pdown.
          apply Decision_and.
          - apply elem_of_dec_slow. 
          - apply Decision_and.
            + apply Decision_not. apply decide_eq.
            + apply set_Exists_dec.
              intros.
              apply elem_of_dec_slow.
        }
        
        specialize (minimal_element_P Pdown HPdec u' Hdown) as Hminimal. 
        destruct Hminimal as [u [Hu_P Hu_minimal]].
        
        unfold Pdown in Hu_P.
        apply and_assoc in Hu_P.
        
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
        
        remember (senders (set_filter (fun v => bool_decide (happens_before' v u)) _ (relevant_messages sm1 sm2))) as Vk_1.
        
        assert (Hin_Vk : forall i, i ∈ Vk_1 -> exists mi, mi ∈ (messages_from u i)). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          exists mi.
          apply elem_of_filter.
          rewrite <- Is_true_iff_eq_true.
          rewrite bool_decide_eq_true.
          split;[intuition congruence|].
          apply elem_of_filter in Hinmi.
          destruct Hinmi as [Hinmi _].
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite bool_decide_eq_true in Hinmi.
          apply HdownSetCorrect in Hinmi.
          intuition congruence.
        }
        
        assert (Hinvk2 : forall i, i ∈ Vk_1 -> exists mi, sender mi = i /\ mi ∈ sm2 /\ happens_before' mi u). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite bool_decide_eq_true in Hinmi.
          unfold relevant_messages in Hinmi.
          destruct Hinmi as [Hinmi Hinmi'].
          apply elem_of_filter in Hinmi'.
          exists mi; intuition.
        }
        
        assert (Hinvk3 : forall i, i ∈ Vk_1 -> exists mi, sender mi = i /\ mi ∈ sm1). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          destruct Hinmi as [Hinmi Hinmi'].
          apply elem_of_filter in Hinmi'.
          destruct Hinmi' as [Hinmi' _].
          rewrite <- Is_true_iff_eq_true in Hinmi'.
          rewrite <-in_correct in Hinmi'.
          apply elem_of_list_In in Hinmi'.
          apply elem_of_elements in Hinmi'.
          apply elem_of_map in Hinmi'.
          destruct Hinmi' as [mi' Hneed].
          exists mi'. intuition congruence.
        }
        
        assert (HVk1_sz : size Vk_1 >= q). {
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
          (*
          rewrite map_size.
          rewrite map_length in Hdensity.
          assert (length
                  (filter (fun v : message => bool_decide (happens_before' v u)) 
                  (relevant_messages sm1 sm2)) >=
                  length
                  (filter (fun v : message => bool_decide (happens_before' v uk))
                  (relevant_messages sm1 sm2))). {
            rewrite Z.ge_le_iff.
            apply inj_le.
            apply filter_length_fn.
            rewrite Forall_forall.
            intros.
            rewrite bool_decide_eq_true.
            rewrite bool_decide_eq_true in H0.
            apply Huk_u.
            intuition.
          } 
          lia. *)
          admit.
        }
        
        (* remember (set_filter (fun i => bool_decide (is_equivocating_from_message u i)) _ Vk_1) as Veq. *)
        remember (set_filter (fun i => bool_decide (is_equivocating_from_message u i)) _ Vk_1) as Veq.
        remember (divergent_last_messages u (Some value)) as latest_divergent.
        remember ((senders latest_divergent) ∩ Vk_1) as Vchange.
        
        assert (Hin_veq1 : forall i, i ∈ Veq -> is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          apply elem_of_filter in Hi.
          rewrite <- Is_true_iff_eq_true in Hi.
          rewrite bool_decide_eq_true in Hi. intuition.
        }
        
        assert (Hin_veq2 : forall i, i ∈ Vk_1 /\ i ∉ Veq -> ~ is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          intros contra.
          destruct Hi as [Hini Hi].
          contradict Hi; apply elem_of_filter; rewrite <- Is_true_iff_eq_true; rewrite bool_decide_eq_true; intuition.
        }
        
        assert (Hin_veq3 : forall i, i ∈ Vk_1 /\ i ∉ Veq -> exists mi, latest_message_from u i = Some mi). {
          intros i Hi.
          assert (H' := Hi).
          apply Hin_veq2 in H'.
          destruct Hi as [Hi _].
          apply latest_message_from_exists.
          apply Hin_Vk in Hi.
          intuition.
        }
        
        assert (Hin_vchange : forall i, i ∈ Vchange -> ~ is_equivocating_from_message u i /\
                                        (exists mi, latest_message_from u i = Some mi /\ 
                                        vote mi <> Some value)). {
          intros i Hi. rewrite HeqVchange in Hi.
          apply elem_of_intersection in Hi.
          rewrite Heqlatest_divergent in Hi.
          destruct Hi as [Hi _].
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite negb_true_iff in Hinmi.
          rewrite bool_decide_eq_false in Hinmi.
          destruct Hinmi as [Hvote_mi Hlatest].
          assert (Hlatest' := Hlatest).
          apply latest_message_sender_info in Hlatest.
          destruct Hlatest as [Hnon_equiv Hlatest].
          subst i.
          split;[intuition|].
          exists mi.
          split;intuition. 
        }
        
        assert (Heq_change_disjoint : Veq ## Vchange). {
          intros i contra1 contra2.
          apply Hin_vchange in contra2.
          apply Hin_veq1 in contra1.
          intuition.
        }
        
        assert (Hmi: forall i, i ∈ Vk_1 /\ i ∉ Veq /\ i ∉ Vchange -> 
          (exists mi, (latest_message_from u i) = Some mi /\ vote mi = Some value)). {
          intros i Hi.
          destruct Hi as [Hk_1 [Hn_veq Hn_change]].
          specialize (Hin_veq3 i).
          spec Hin_veq3. intuition.
          destruct Hin_veq3 as [mi Hlatest].
          exists mi.
          split; [intuition|].
          
          destruct (@decide (vote mi = Some value) (decide_eq (vote mi) (Some value))). 
          - intuition.
          - contradict Hn_change.
            rewrite HeqVchange.
            apply elem_of_intersection.
            split;[|intuition].
            rewrite Heqlatest_divergent.
            apply elem_of_map.
            
            assert (Hsendermi: sender mi = i) by (apply latest_message_sender in Hlatest; intuition).
            
            exists mi.
            split;[intuition|].
            apply elem_of_filter. rewrite <- Is_true_iff_eq_true. 
            rewrite negb_true_iff. rewrite bool_decide_eq_false.
            split;[intuition|].
            apply latest_message_in_latest_messages.
            rewrite Hsendermi. intuition.
            apply Hin_veq2.
            rewrite Hsendermi.
            intuition.
        }
        
        (*
        assert (Hdectemp: forall i, Decision (~In i Veq /\ ~In i Vchange)). {
          intros.
          apply Decision_and; apply Decision_not; apply in_dec; apply idec.
        } *)
        
        remember (Vk_1 ∖ (Veq ∪ Vchange)) as value_voters.
        
        assert (Hvoters_size1 : (size value_voters + size Veq + size Vchange = size Vk_1)). {
          rewrite Heqvalue_voters.
          assert (Hsizeu : Z.of_nat (size (Veq ∪ Vchange)) = size Veq + size Vchange). {
            specialize (size_union Veq Vchange Heq_change_disjoint) as Hnat.
            lia.
          }
          rewrite <- Zplus_assoc.
          rewrite <- Hsizeu.
          specialize (size_union_alt (Veq ∪ Vchange) Vk_1) as Hinv.
          
          assert (Hveq2: Vk_1 ≡ Veq ∪ Vchange ∪ Vk_1). {
             rewrite <- assoc by (apply union_assoc).
             assert (Htemp: Vchange ∪ Vk_1 ≡ Vk_1). {
                apply subseteq_union_1.
                rewrite HeqVchange.
                apply intersection_subseteq_r.
             }
             rewrite Htemp.
             specialize (subseteq_union_1 Veq Vk_1) as Htemp2.
             spec Htemp2.
             rewrite HeqVeq.
             intuition set_solver.
             intuition.
          }
          rewrite <- Hveq2 in Hinv.
          lia.
        }
        
        assert (Hineq1 : 2 * (q - (size Veq) - (size Vchange)) <= n - size Eu). {
          move Hvote at bottom.
          assert (Hvote' := Hvote).
          
          assert (~ 2 * (q - (size Veq) - (size Vchange)) > n - size Eu). {
            intros contra.
            destruct Hu_P as [_ Hu_P].
            contradict Hu_P.
           
            remember (count_votes_for u (Some value)) as votes_for_value.
            assert (Hvotes_for : votes_for_value >= (q - size Veq - size Vchange)). {
                assert (Hvotes_for' : votes_for_value >= size value_voters). {
                   rewrite Heqvotes_for_value.
                   admit.
                }
                lia.
            }
            
            specialize (Hvote' u (vote u) eq_refl (Some value)).
            rewrite Heqvotes_for_value in Hvotes_for.
                assert (count_votes_for u (Some value) + count_votes_for u (vote u) <= n - size Eu). {
                  admit.
                }
                unfold count_votes_for in *.
                clear- Hvotes_for H13 contra Hvote'.
                admit.
            }
            intuition.
        }
        
        assert (HVeq_incl_Eu : Veq ⊆ Eu). {
          rewrite HeqEu.
          rewrite HeqVeq.
          unfold equivocators_from_message.
          unfold subseteq.
          unfold set_subseteq_instance. intros x Hf.
          apply elem_of_filter in Hf.
          apply elem_of_filter.
          split;[intuition|].
          destruct Hf as [_ Hf].
          apply elem_of_elements.
          admit.
        }
        
        assert (n - size Eu <= n - size Veq). {
          cut (size Veq <= size Eu). {
            lia.
          }
          apply inj_le.
          apply subseteq_size.
          apply HVeq_incl_Eu.
        }
        
        assert (2 * q <= n + size Veq + 2 * (size Vchange)) by lia.
        
        destruct Vchange eqn : eqd_Vchange.
        + admit.
        + assert (Hu': exists u', happens_before' u' u /\
                             (vote u' <> Some value) /\
                             (exists v, In v (downSet u') /\ In v sm2)). {
            move Hin_vchange at bottom.
            specialize (Hin_vchange i).
            spec Hin_vchange. intuition.
            destruct Hin_vchange as [H_i_non_equiv Hinvchange].
            destruct Hinvchange as [u'' [Hlatest_u'' Hvote_u'']].
            
            assert (Hsender_u'': sender u'' = i). {
              apply latest_message_sender in Hlatest_u''.
              intuition.
            }
            
            exists u''.
            split. 
            * apply latest_message_from_compares in Hlatest_u''.
              intuition. 
            * split;[intuition|].
              assert (Hini : In i Vk_1). {
                assert (Htemp : In i (filter (fun i1 : index => inb decide_eq i1 (senders latest_divergent)) Vk_1)). {
                  rewrite <- HeqVchange.
                  intuition.
                }
                apply filter_In in Htemp.
                intuition.
              }
              assert (Hini' := Hini).
              apply Hinvk2 in Hini.
              destruct Hini as [mi [Hsender Hmi]].
              exists mi.
              split;[|intuition].
              
              assert (Hless_mi: happens_before' mi  u''). {
                apply compare_messages1 with (u := u).
                intuition congruence.
                apply latest_message_in_latest_messages.
                intuition congruence.
                intuition congruence.
                admit.
                intuition.
              }
              apply HdownSetCorrect.
              intuition.
          }
          
          move IHHcom at bottom.
          specialize (IHHcom Hstate).
    
          remember (@Build_committee_skeleton s value (sm2 :: l) q) as new_skel.
          specialize (IHHcom new_skel).
          rewrite Heqnew_skel in IHHcom. simpl in IHHcom.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          specialize (IHHcom eq_refl).
          specialize (IHHcom sm2). unfold get_top in IHHcom. simpl in IHHcom.
          specialize (IHHcom eq_refl).
          
          spec IHHcom. {
            destruct Hu' as [u'' Hu''].
            exists u''.
            split.
            - apply protocol_state_closed with (u := u).
              all : intuition.
            - intuition.
          }
    Admitted.
      
End Inspector.
End FullNodeLike.