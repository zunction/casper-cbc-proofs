From Coq Require Import ssreflect ssrfun ssrbool.

Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program Reals Lra ListSet Nat
  Coq.Logic.FinFun
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    Lib.Measurable
    Lib.ListExtras
    VLSM.Common
    VLSM.Composition
    VLSM.Validating
    VLSM.Equivocation
    .

Require Import List.
    
Inductive Label := Receive | Send.

Inductive Prestate : Type :=
| Cprestate: list Observation -> Prestate
with
Observation : Type :=
| Cobservation: Label -> Premessage -> nat -> Observation
with
Premessage : Type :=
| Cpremessage: Prestate -> nat -> Premessage
.

Instance Label_eqdec : EqDecision Label.
Proof.
  intros l1 l2.
  unfold Decision.
  decide equality.
Qed.

 

Lemma Prestate_eqdec : forall (s1 s2 : Prestate), {s1 = s2} + {s1 <> s2}
with  Observation_eqdec : forall (o1 o2 : Observation), {o1 = o2} + {o1 <> o2}
with  Premessage_eqdec : forall (m1 m2 : Premessage), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
  decide equality. decide equality. decide equality.
Qed.

Instance Prestate_eqdec' : EqDecision Prestate.
Proof.
  intros x y.
  apply Prestate_eqdec.
Qed.

Instance Observation_eqdec' : EqDecision Observation.
Proof.
  intros x y.
  apply Observation_eqdec.
Qed.

Instance Premessage_eqdec' : EqDecision Premessage.
Proof.
  intros x y.
  apply Premessage_eqdec.
Qed.

Definition dummy_prestate := Cprestate [].
Definition dummy_premessage := Cpremessage dummy_prestate 0.
Definition dummy_observation := Cobservation Receive dummy_premessage 0.


Definition observationsOf (prs : Prestate) : list Observation :=
  match prs with
  | Cprestate l => l
  end.

Definition labelOf (ob : Observation) : Label :=
  match ob with
  | Cobservation lbl _ _ => lbl
  end.

Definition messageOf (ob : Observation) : Premessage :=
  match ob with
  | Cobservation _ msg _ => msg
  end.

Definition witnessOf (ob : Observation) : nat :=
  match ob with
  | Cobservation _ _ w => w
  end.

Definition isWitnessedBy (component : nat) (ob : Observation) : bool :=
  bool_decide (witnessOf ob = component).

Definition isReceive (ob : Observation) : bool :=
  match ob with
  | Cobservation Receive _ _ => true
  | _ => false
  end.

Definition isSend (ob : Observation) : bool :=
  match ob with
  | Cobservation Send _ _ => true
  | _ => false
  end.

Definition stateOf (m : Premessage) : Prestate :=
  match m with
  | Cpremessage s _ => s
  end.

Definition authorOf (m : Premessage) : nat :=
  match m with
  | Cpremessage _ a => a
  end.


Instance elmo_type : VLSM_type Premessage :=
  {| state := Prestate;
     Common.label := Label;
  |}.

Definition elmo_state : Type := @state Premessage elmo_type.

Definition elmo_initial_state_prop (ps : elmo_state) : Prop :=
  observationsOf ps = [].

Definition elmo_initial_state
  := sig elmo_initial_state_prop.

Definition elmo_s0 : elmo_initial_state.
Proof.
  unfold elmo_initial_state.
  exists (Cprestate []).
  unfold elmo_initial_state_prop.
  reflexivity.
Defined.

Definition elmo_m0 : Premessage := Cpremessage (Cprestate []) 0.

Definition elmo_sig : VLSM_sign elmo_type :=
  {| initial_state_prop := elmo_initial_state_prop
     ; s0 := elmo_s0
     ; initial_message_prop := (fun x => False)
     ; m0 := elmo_m0
     ; l0 := Receive
     ;
  |}.


(* Check that every message received or sent in m has been received in the prefix by the component *)
Definition fullNode (m : Premessage) (prefix: list Observation) (component: nat) : bool :=
  fold_right andb true
             (map (fun (ob2 : Observation) =>
                     match (labelOf ob2) with
                     | Receive =>
                       if
                         (In_dec Observation_eqdec (Cobservation Receive (messageOf ob2) component) prefix)
                       then true else false
                     | Send => false
                     end
                  )
                  (observationsOf (stateOf m))
             ).


Definition nth_update {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  firstn idx l ++ cons v (skipn (S idx) l).

Program Definition update
           (m : Premessage)
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (curState : list Prestate)
           (curEq : set nat)
  : bool * (list Prestate) * (set nat) :=
  let p := stateOf m in
  let a := authorOf m in
  let lp := length (observationsOf p) in
  let ca := nth a curState dummy_prestate in
  let la := length (observationsOf (ca)) in
  if andb (la <=? lp)
          (bool_decide ((firstn la (observationsOf p))=(observationsOf ca))) then
    (true,
     nth_update curState a (Cprestate (observationsOf p ++ [Cobservation Send m a])),
     curEq)
  else
    if andb (S lp <=? la)
            (andb
               (bool_decide ((firstn lp (observationsOf ca))=(observationsOf p)))
               (bool_decide ((nth lp (observationsOf ca) dummy_observation)=(Cobservation Send m a)))) then
      (true, curState, curEq)
    else
      let newEq := curEq in
      if (Rlt_dec (@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) newEq) treshold) then
        (false, curState, curEq)
      else
        (true, curState, newEq).
Next Obligation.
  lra.
Defined.


Definition isProtocol_step (component : nat) (weights : list pos_R) (treshold : R)
           (args : bool * nat * list Observation * list Prestate * set nat) (ob : Observation)
  : bool * nat * list Observation * list Prestate * set nat
  :=
    let: (result, i, observations, curState, curEq) := args in
    match result with
    | false => args
    | true =>
      let l := labelOf ob in
      let m := messageOf ob in
      let p := stateOf m in
      let a := authorOf m in
      let w := witnessOf ob in
      let prefix := firstn i observations in
      let i := S i in
      (* w <> component *)
      if negb (bool_decide (w=component)) then
        (false, i, observations, curState, curEq)
      else (* w = component *)
        if bool_decide (a=component) then
          match l with
          | Send =>
            let result := bool_decide (observationsOf p = prefix) in
            (result, i, observations, curState, curEq)
          | Receive =>
            let result := bool_decide (In (Cobservation Send m component) prefix) in
            (result, i, observations, curState, curEq)
          end
        else
          (* a <> component *)
          match l with
          | Send =>
            let result := false in
            (result, i, observations, curState, curEq)
          | Receive =>
            if negb (fullNode m prefix component) then
              let result := false in
              (result, i, observations, curState, curEq)
            else
              let: (result, curState, curEq) := update m component weights treshold curState curEq in
              (result, i, observations, curState, curEq)
          end 
    end.

Definition isProtocol
           (prestate : Prestate)
           (component : nat)
           (weights : list pos_R)
           (treshold: R) : bool
  :=
    let initialState := map (fun x => Cprestate nil) weights in
    let initialEq := @nil nat in
    let result := (fold_left (isProtocol_step component weights treshold) (observationsOf prestate) (true, 0, observationsOf prestate, initialState, initialEq )) in
    fst (fst (fst (fst result))).

Definition elmo_valid
           (weights : list pos_R)
           (treshold : R)
           (label : Label)
           (bsom : Prestate * option Premessage)
  : bool :=
  let: (state, message) := bsom in
  match label,message with
  | Send, None => true
  | Send, Some _ => false
  | Receive, None => false
  | Receive, Some m => isProtocol (stateOf m) (authorOf m) weights treshold
  end.

Definition elmo_transition
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (label : Common.label)
           (bsom : Prestate * option Premessage)
  : Prestate * option Premessage
  :=
    let: (state, message) := bsom in
    match label, message with
    | Send, Some _ => (state, None)
    | Send, None
      => let m := Cpremessage state component in
         let ob := Cobservation Send m component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, Some m)
    | Receive, None
      => (state, None)
    | Receive, Some msg
      => let ob := Cobservation Receive msg component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, None)
    end.

Definition elmo_vlsm_machine (component : nat) (weights : list pos_R) (treshold : R)
  : @VLSM_class Premessage elmo_type elmo_sig
  :=
    {| valid := elmo_valid weights treshold
       ; transition := elmo_transition component weights treshold
    |}.


Section capabilities.
  Context
    (component : nat)
    (weights : list pos_R)
    (treshold : R)
    (vlsm := mk_vlsm (elmo_vlsm_machine component weights treshold))
  .

  Check (field_selector input).
  Check oracle_stepwise_props.

  Definition elmo_input_message_oracle (s : Prestate) (m : Premessage) : Prop :=
    List.In m (map messageOf (filter isReceive (filter (isWitnessedBy component) (observationsOf s)))).

  Definition elmo_output_message_oracle (s : Prestate) (m : Premessage) : Prop :=
    List.In m (map messageOf (filter isSend (filter (isWitnessedBy component) (observationsOf s)))).

  Lemma elmo_input_message_oracle_no_inits:
    forall (s : vstate vlsm),
      initial_state_prop (VLSM_sign := sign vlsm) s ->
      forall m, ~elmo_input_message_oracle s m.
  Proof.
    intros s Hinitial m Hcontra.
    simpl in Hinitial. unfold elmo_initial_state_prop in Hinitial.
    unfold elmo_input_message_oracle in Hcontra. rewrite Hinitial in Hcontra.
    simpl in Hcontra.
    exact Hcontra.
  Qed.


  Lemma elmo_input_message_oracle_step_update:
    forall l s im s' om,      
      protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
      forall msg, elmo_input_message_oracle s' msg <->
                  ((field_selector input) msg {|l:=l; input:=im; destination:=s'; output:=om|}
                   \/ elmo_input_message_oracle s msg).
  Proof.
    intros l s im s' om Hpt msg.
    simpl.

    destruct Hpt as [Hvalid Htransition].
    simpl in Htransition.
    unfold vtransition in Htransition. simpl in Htransition.
    
    unfold elmo_input_message_oracle.
    destruct l, im; inversion Htransition; subst; clear Htransition; simpl.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * left. destruct H as [H|H].
          ** congruence.
          ** inversion H.
      + intros [H|H].
        * inversion H; subst.
          right. left. reflexivity.
        * left. exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H.
        * exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H; subst.
          inversion Hvalid.
          destruct H1.
          simpl in H2. unfold vvalid in H2. simpl in H2. inversion H2.
        * exact H.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * inversion H.
      + intros [H|H].
        * inversion H.
        * left. exact H.
  Qed.

  Definition elmo_input_message_oracle_stepwise_props
    : @oracle_stepwise_props _ vlsm (field_selector input) elmo_input_message_oracle
    := {| oracle_no_inits := elmo_input_message_oracle_no_inits;
          oracle_step_update := elmo_input_message_oracle_step_update;
       |}
  .
  
End capabilities.

(* m1 is a prefix of m2 *)
Definition is_prefix_of (m1 m2 : Premessage) : Prop :=
  let s1 := stateOf m1 in
  let s2 := stateOf m2 in
  observationsOf s1 = firstn (length (observationsOf s1)) (observationsOf s2).

Lemma is_prefix_of_dec : RelDecision is_prefix_of.
Proof.
  intros m1 m2.
  unfold is_prefix_of.
  apply list_eq_dec.
  apply Observation_eqdec.
Qed.

Definition equivocation_evidence (m1 m2 : Premessage) : Prop :=
  authorOf m1 = authorOf m2 /\
  ~ is_prefix_of m1 m2 /\
  ~ is_prefix_of m2 m1.

Instance equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  intros m1 m2.
  unfold equivocation_evidence.
  apply Decision_and.
  { unfold Decision. decide equality. }
  apply Decision_and; apply Decision_not; apply is_prefix_of_dec.
Qed.

(* `component` is equivocating and we have an evidence in the state `s` (of another component) *)
Definition is_equivocator (component : nat) (s : Prestate) : bool :=
  let obs := observationsOf s in
  existsb
    (fun ob1 =>
       existsb
         (fun ob2 =>
            bool_decide (labelOf ob1 = Receive) &&
            bool_decide (labelOf ob2 = Receive) &&
            bool_decide (authorOf (messageOf ob1) = component) &&
            bool_decide (authorOf (messageOf ob2) = component) &&
            bool_decide (equivocation_evidence (messageOf ob1) (messageOf ob2))
         )
         obs
    )
    obs.

Section composition.

  Context
    (weights : list pos_R)
    (treshold : R)
    (index : Type)
    {i0 : Inhabited index}
    {IndEqDec : EqDecision index}
    (indices : list index)
    (finite_index : Listing indices)
    (indices_weights_eqlenght : length indices = length weights)
  .

  Fixpoint index_to_component' (idx : index) (component : nat) (indices : list index) :=
    match indices with
    | [] => component
    | x::xs
      => if decide (x = idx)
         then component
         else index_to_component' idx (S component) xs
    end.

  Lemma index_to_component'_valid (idx : index) (component : nat) (indices': list index) :
    In idx indices' -> index_to_component' idx component indices' < length indices' + component.
  Proof.
    intros Hin.
    move: component.
    induction indices'.
    - simpl in Hin. inversion Hin.
    - intros component.
      simpl.
      destruct (decide (a = idx)); simpl.
      + lia.
      + simpl in Hin.
        destruct Hin as [Haeqidx|Hin].
        * contradiction.
        * specialize (IHindices' Hin).
          specialize (IHindices' (S component)).
          lia.
  Qed.

  Definition index_to_component (idx : index) :=
    index_to_component' idx 0 indices.

  Lemma index_to_component_valid (idx : index) : index_to_component idx < length indices.
  Proof.
    pose proof (P := index_to_component'_valid).
    specialize (P idx 0 indices).
    rewrite Nat.add_0_r in P.
    apply P.
    apply finite_index.
  Qed.
  

  Definition IM' (i : index) := elmo_vlsm_machine (index_to_component i) weights treshold.
  Definition IM (i : index) := mk_vlsm (IM' i).

  (* `component` is equivocating and we have an evidence in some state
     of the list `states` *)
  Definition is_equivocator_states (states : list Prestate) (component : nat) : bool :=
    let eq := map (is_equivocator component) states in
    fold_right orb false eq.

  Definition equivocators (states : list Prestate) : list nat :=
    filter (is_equivocator_states states) (seq 0 (length indices)).
  
  Program Definition composition_constraint
             (cl : composite_label IM)
             (sm : composite_state IM * option Premessage) : Prop
    := let cs := fst sm in
       let om := snd sm in
       match om with
       | None => True
       | Some m =>
         let states := map cs indices in
         let transitions := map (fun i => @transition _ _ _ (IM' i)) indices in
         let new_states := zip_with (fun s t => fst (t Receive (s, Some m)))
                                    states
                                    transitions in
         let eqs := equivocators new_states in
         ((@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) eqs) < treshold)%R
       end.
  Next Obligation.
    lra.
  Defined.
  
  
  Definition composite_elmo := @composite_vlsm Premessage index IndEqDec IM i0 composition_constraint.


  Context
        (i : index)
        (Xi := composite_vlsm_constrained_projection IM composition_constraint i)
  .
  
  
  Theorem elmo_validating:
    validating_projection_prop IM composition_constraint i.
  Proof.
    intros li siomi H.
    unfold protocol_valid in H.
    unfold vvalid. unfold valid. unfold machine. simpl.
    unfold projection_valid.
    destruct siomi as [si omi].
    destruct H as [Hpsp [Hopmp Hvalid]].
    unfold valid in Hvalid. unfold machine in Hvalid. simpl in Hvalid. unfold IM in Hvalid.
    unfold IM' in Hvalid. inversion Hvalid.
    unfold vvalid in Hvalid.
  Abort.
  


End composition.
