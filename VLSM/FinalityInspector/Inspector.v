Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting Basics.
Require Import Lia.
Import ListNotations.
From CasperCBC
  Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras
    CBC.Protocol CBC.Common CBC.Definitions
    VLSM.Common VLSM.Composition VLSM.Decisions VLSM.Equivocation VLSM.ProjectionTraces.
    

Section FullNodeLike.

Context
  {message : Type}
  {mdec : EqDecision message}
  (happens_before : message -> message -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (predSet : message -> set message)
  (HpredSetCorrect : forall (m1 m2 : message), happens_before m1 m2 <-> In m2 (predSet m1))
  (downSet : message -> set message)
  (downSet' := fun (m : message) => set_union mdec (downSet m) [m])
  (HdownSetCorrect : forall (m : message), 
                       set_eq
                       (downSet m) 
                       (fold_right (set_union decide_eq) nil (List.map downSet' (predSet m))))
  {index : Type}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  {i0 : Inhabited index}
  {IM : index -> VLSM message}
  (computable_sent : forall (i : index), computable_sent_messages (IM i))
  (computable_received : forall (i : index), computable_received_messages (IM i)). 
  
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

Section Inspector.

Context
    {CV : consensus_values}
    (sender : message -> index)
    (latestFrom : message -> index -> message) 
    (X := composite_vlsm IM fullnode_constraint).
    
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
      is_equivocating_from_set (predSet m).
      
    Definition is_equivocating_from_state
      (s : vstate X) :=
      is_equivocating_from_set (composite_observed s).
      
    Program Definition equivocators_from_state
      (s : vstate X) :=
      List.filter (fun i => negb (@bool_decide (is_equivocating_from_state s i) _)) index_listing.
    Next Obligation.
    Admitted.
    
    Lemma is_equivocating_from_message_dec : RelDecision is_equivocating_from_message.
    Proof.
    Admitted.
    
    Definition senders 
      (s : set message) := 
      List.map sender s.
    
    Definition honest
      (m : message) : set index := 
      List.filter (fun (i : index) => negb (@bool_decide (is_equivocating_from_message m i) 
                                              (is_equivocating_from_message_dec m i))) index_listing.
    
    Definition honest_messages
      (m : message) : set message :=
      List.filter (fun (m : message) => inb idec (sender m) (honest m)) (predSet m).
      
    Definition latest_messages
      (m : message) : set message :=
      ListSetExtras.get_maximal_elements (fun m1 m2 => bool_decide (happens_before m1 m2)) (honest_messages m).
    
    Definition vote
      (m : message) : option C := None.
      
    Record committee_skeleton : Type := {
      com_state : vstate X;
      com_state_Hpr : protocol_state_prop X com_state;
      value : C;
      com : list (set message);
      q : nat;
      k : nat;
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
      happens_before m1 m2 /\ happens_before m2 m3 ->
      In m2 sm.
    
    Definition live_messages
      (sm1 sm2 : set message) :=
      List.filter (fun m => inb idec (sender m) (senders sm2)) sm1. 
    
    Definition density
      (sm1 sm2 : set message)
      (q : nat) :=
      forall (m : message),
      In m sm1 ->
      length (senders (set_inter decide_eq (downSet' m) (live_messages sm1 sm2))) >= q.
    
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
        (Hdensity : density sm2 sm1 q)
        (Hconv : convexity sm1)
        (Hgood : valid_com_prop s value q (sm2 :: l)) : valid_com_prop s value q (sm1 :: (sm2 :: l)).
    
    Definition commitee : Type := {
      comskel : committee_skeleton | valid_com_prop (com_state comskel) (value comskel) (q comskel) (com comskel)
    }.
    
    
      
      
End Inspector.
End FullNodeLike.