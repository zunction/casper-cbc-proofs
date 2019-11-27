Require Import Bool List Streams Logic.Epsilon Reals.
Import ListNotations.
From Casper   
Require Import preamble ListExtras ListSetExtras RealsExtras definitions common vlsm composed_vlsm indexed_vlsm commute fullnode.

(* Creating a full-node instance of VLSM *)

Fixpoint unget_messages {C V} (lm : list (@message C V)) : definitions.state :=
  match lm with
  | [] => Empty
  | (c,v,j) :: tl => Next c v j (unget_messages tl)
  end.

Theorem get_unget_idempotent {C V} :
  forall (lm : list (@message C V)),
    get_messages (unget_messages lm) = lm.
Proof.
  induction lm as [|hd tl IHlm]. 
  - reflexivity.
  - destruct hd as [[c v] j].
    simpl. rewrite IHlm.
    reflexivity.
Qed. 

Theorem unget_get_idempotent {C V} :
  forall (s : @definitions.state C V),
    unget_messages (get_messages s) = s.
Proof.
  intros s.
  induction s.
  - reflexivity.
  - simpl. rewrite IHs2.
    reflexivity. 
Qed.

Section Full. 

  Variables (C V : Type) (about_C : StrictlyComparable C) (about_V : StrictlyComparable V) (Hm : Measurable V) (Hrt : ReachableThreshold V) (He : Estimator (@sorted_state C V message_type) C).

  Definition reach (s1 s2 : @definitions.state C V) : Prop :=
    incl (get_messages s1) (get_messages s2).

  Definition proto_message_prop : @message C V -> Prop :=
    fun msg => True. 

  Definition proto_message : Type :=
    { m : @message C V | proto_message_prop m}. 

  Lemma proto_message_decidable :
    forall (msg : @message C V), {proto_message_prop msg} + {~ proto_message_prop msg}. 
  Proof. 
    intros msg.
    left.
    red. auto.
  Qed.

  Definition initial_state_prop : @sorted_state C V message_type -> Prop :=
    fun s => s = @sorted_state0 C V message_type. 

  Program Definition state0 : {s | initial_state_prop s} := _.
  Next Obligation.
    exists (@sorted_state0 C V message_type).
    reflexivity.
  Defined. 

  Program Definition proto_message0 : proto_message := _. 
  Next Obligation.
    assert (about_C_copy := about_C). 
    destruct about_C_copy.
    destruct inhabited as [c _].
    assert (about_V_copy := about_V). 
    destruct about_V_copy.
    destruct inhabited as [v _].
    exists (c,v,proj1_sig (@sorted_state0 C V message_type)).
    red.
    auto.
  Defined.

  Definition message0 : @message C V := proj1_sig proto_message0. 

  Definition initial_message_prop : proto_message -> Prop :=
    fun msg => proj1_sig msg = proj1_sig proto_message0. 
  
  Definition initial_message := { m : proto_message | initial_message_prop m }.

  Program Definition initial_message0 : initial_message := _. 
  Next Obligation.
    exists proto_message0; reflexivity.
  Defined.

  Lemma protocol_state_inhabited : {_ : @sorted_state C V message_type | True}.
  Proof.
    exists (@sorted_state0 C V message_type).
    auto. 
  Qed. 

  Lemma message_inhabited : {m : @message C V | True}. 
  Proof.
    destruct (@message_type C about_C V about_V).
    assert (inhabited_copy := inhabited).
    destruct inhabited_copy as [witness _].
    exists witness; auto. 
  Qed.

  Parameter add_message_sorted : @message C V ->  @sorted_state C V message_type ->  @sorted_state C V message_type. 

  Program Definition make_proto_message_prop (msg : @message C V) : proto_message_prop msg := _. 
  Next Obligation.
    unfold proto_message_prop.
    auto.
  Defined.

  Program Definition make_proto_message (msg : @message C V) (about_msg : proto_message_prop msg) : {msg : @message C V | proto_message_prop msg} := _. 
  Next Obligation.
    exists msg. 
    assumption.     
  Defined.

  Definition vtransition (l : option (C * V)) (sm : @sorted_state C V message_type * option proto_message) :  @sorted_state C V message_type  * option proto_message :=
    match l with 
    | None => match (snd sm) with 
             | None => ((fst sm), None)
             | Some msg => (add_message_sorted (proj1_sig msg) (fst sm), None) 
             end
    | Some (c, v) => match (snd sm) with
                    | None => (fst sm, None)
                    | Some msg => (add_message_sorted (proj1_sig msg) (fst sm), Some (make_proto_message (c,v,proj1_sig (fst sm)) (make_proto_message_prop (c,v,proj1_sig (fst sm)))))
                    end
    end.

  Inductive valid_client : option (C * V) -> @sorted_state C V message_type * option proto_message -> Prop :=
  | client_none : forall (s : @sorted_state C V message_type), valid_client None (s, Some (make_proto_message message0 (make_proto_message_prop message0)))
  | client_receive : forall (s : @sorted_state C V message_type) (msg : C * V * definitions.state),
      reach (snd msg) s ->
      not_heavy (add_message_sorted (msg) s) ->
      valid_client None (s, Some (make_proto_message msg (make_proto_message_prop msg)))
  | client_produce : forall (s : @sorted_state C V message_type) (vl : C * V) (msg : C * V * definitions.state),
      (@estimator (@sorted_state C V message_type) C He) s (fst vl) -> valid_client (Some vl) (s, Some (make_proto_message msg (make_proto_message_prop msg))).

  Definition unoption_message (vmsg : option proto_message) : @message C V :=
    match vmsg with
    | None => message0
    | Some msg => proj1_sig msg
    end. 

  Definition reachb : @definitions.state C V -> definitions.state -> bool :=
    fun s1 s2 => forallb (fun s => is_member s (get_messages s2)) (get_messages s1).

  Parameter Rleb : R -> R -> bool. 

  Definition not_heavyb (sigma : @definitions.state C V) : bool :=
    Rleb (fault_weight_state sigma) (proj1_sig threshold)%R.

  Definition valid_clientb : option (C * V) -> @sorted_state C V message_type * option proto_message -> bool :=
    fun l sm =>
      match l with
      | None => reachb (add_message_sorted (unoption_message (snd sm)) (fst sm)) (fst sm) && not_heavyb (fst sm)
      | Some (c,v) => compareb (get_estimate (fst sm)) c 
      end.

  Lemma valid_client_correct :
    forall (l : option (C * V)) (sm : @sorted_state C V message_type * option proto_message),
      valid_clientb l sm = true <-> valid_client l sm. 
  Proof.
    intros [[c v] | ] [s [msg | ]]; split; intro H;
    unfold valid_clientb in H.
    replace msg with (make_proto_message (proj1_sig msg) (make_proto_message_prop (proj1_sig msg))).
    apply client_produce.
    assert (get_estimate (fst (s, Some msg)) = c) by admit. 
    rewrite <- H0. simpl.
  Admitted.

  Lemma valid_client_correct' :
    forall (l : option (C * V)) (sm : @sorted_state C V message_type * option proto_message),
      valid_clientb l sm = false <-> ~ valid_client l sm. 
  Proof.
    intros. apply mirror_reflect_curry.
    apply valid_client_correct.
  Qed.

  Lemma valid_decidable : forall (l : option (C * V)) som, {valid_client l som} + {~valid_client l som}. 
  Proof.
    intros. 
    case_eq (valid_clientb l som); intro H.
    - left.
      now apply valid_client_correct.
    - right.
      now apply valid_client_correct'.
  Qed.

  (* 2.3.2 Minimal full client, Client1 *)
  Instance LSM_full_client1 : LSM_sig (@message C V) :=
    { state := @sorted_state C V message_type
      ; label := option (C * V)
      ; proto_message_prop := proto_message_prop 
      ; proto_message_decidable := proto_message_decidable
      ; initial_state_prop := initial_state_prop
      ; initial_message_prop := initial_message_prop
      ; s0 := state0
      ; m0 := proto_message0
      ; l0 := None
    }.

  Instance VLSM_full_client1 : @VLSM (@message C V) LSM_full_client1 := 
    { transition := vtransition
      ; valid := valid_client
    }.

  (* Converting between full node and VLSM notions *)

  (* How to avoid these solutions to awkward namespace clashes? *) 
  Definition sorted_state_union : (@state _ LSM_full_client1) -> (@state _ LSM_full_client1) -> (@state _ LSM_full_client1) :=
    sorted_state_union. 

  (* Protocol state *)
  (* How do we state this? 
  Lemma protocol_state_equiv :
    forall (s : @state (@message C V) LSM_full_client1),
      (definitions.protocol_state C V message_type) (proj1_sig s) <->
      (@protocol_state_prop (@message C V) LSM_full_client1) s. *) 

  (* Reachability *)
  (* VLSM reachability defined in terms of protocol traces (transition and validity) *) 
  Definition vlsm_next : protocol_state -> protocol_state -> Prop :=
    fun s1 s2 => protocol_trace_prop (Finite [s1; s2]).

  Lemma next_equiv :
    forall (s1 s2 : protocol_state),
      vlsm_next s1 s2 <->
      exists (msg : @message C V), add_in_sorted_fn msg (proj1_sig (proj1_sig s1)) = proj1_sig (proj1_sig s2).
  Proof. Admitted.

  Definition vlsm_reach : protocol_state -> protocol_state -> Prop :=
    fun s1 s2 => exists (tr : protocol_trace_from (fun s => s = s1)), in_trace s2 tr.

  Lemma reach_equiv :
    forall (s1 s2 : protocol_state),
      vlsm_reach s1 s2 <->
      incl (get_messages (proj1_sig (proj1_sig s1))) (get_messages (proj1_sig (proj1_sig s2))).
  Proof. Admitted.
  
  (* VLSM state union *)
  Lemma join_protocol_state :
    forall (s1 s2 : @state _ LSM_full_client1),
      protocol_state_prop s1 ->
      protocol_state_prop s2 -> 
      not_heavy (proj1_sig (sorted_state_union s1 s2)) -> 
      protocol_state_prop (sorted_state_union s1 s2). 
  Proof. 
  Admitted.

  Program Definition protocol_state_union (s1 s2 : protocol_state) (H_weight : not_heavy (sorted_state_union (proj1_sig s1) (proj1_sig s2))) : protocol_state := exist protocol_state_prop (sorted_state_union (proj1_sig s1) (proj1_sig s2)) _.
  Next Obligation.
    destruct s1 as [s1 about_s1];
      destruct s2 as [s2 about_s2].
    now apply join_protocol_state. 
  Defined.
  
  Lemma vlsm_reach_morphism :
    forall (s1 s2 : protocol_state) (H_weight : not_heavy (proj1_sig (sorted_state_union (proj1_sig s1) (proj1_sig s2)))),
      vlsm_reach s1 (protocol_state_union s1 s2 H_weight).
  Proof. Admitted.

  (* cf. this and the other definition of reach? *) 
  
  Theorem pair_common_futures :
    forall (s1 s2 : protocol_state),
      not_heavy (proj1_sig (sorted_state_union (proj1_sig s1) (proj1_sig s2))) ->
      exists (s3 : protocol_state),
        vlsm_reach s1 s3 /\ vlsm_reach s2 s3. 
  Proof. 
    intros.
    remember (sorted_state_union (proj1_sig s1) (proj1_sig s2)) as s3.
    assert (about_s3 : protocol_state_prop s3).
    red.
  Admitted. 

  Theorem strong_nontriviality :
    forall (s1 : protocol_state),
    exists (s2 : protocol_state),
      vlsm_reach s1 s2 /\
      exists (s3 : protocol_state),
      forall (tr2 : protocol_trace_from (fun s => s = s2))
        (tr3 : protocol_trace_from (fun s => s = s3)),
        (exists (s : protocol_state),
            in_trace s tr2 /\ in_trace s tr3 -> False). 
  Proof. 
  Admitted. 
  
  (* 2.5.1 Minimal full client protocol: Client2 *) 
  Definition label2 : Type := unit.    

  Definition vtransition2 (l : unit) (sm : @sorted_state C V message_type * option proto_message) : @sorted_state C V message_type * option proto_message :=
    match l with
    | tt => match (snd sm) with
           | None => (fst sm, None)
           | Some msg => (add_message_sorted (proj1_sig msg) (fst sm), None)
           end
    end. 
  
  Inductive valid_client2 : unit -> (@sorted_state C V message_type) * option proto_message -> Prop :=
  | client2_none : forall (s : @sorted_state C V message_type), valid_client2 tt (s, None)
  | client2_receive : forall (s : @sorted_state C V message_type) (m : proto_message),
      reach (justification (proj1_sig m)) s -> not_heavy (add_in_sorted_fn (proj1_sig m) s) ->
      valid_client2 tt (add_message_sorted (proj1_sig m) s, Some (make_proto_message (proj1_sig m) (make_proto_message_prop (proj1_sig m)))).

  Instance LSM_full_client2 : LSM_sig (@message C V) :=
    { state := @sorted_state C V message_type
      ; label := label2
      ; proto_message_prop := proto_message_prop 
      ; proto_message_decidable := proto_message_decidable
      ; initial_state_prop := initial_state_prop
      ; initial_message_prop := initial_message_prop
      ; s0 := state0
      ; m0 := proto_message0
      ; l0 := tt
    }.

  Instance VLSM_full_client2  : @VLSM (@message C V) LSM_full_client2 := 
    { transition := vtransition2
      ; valid := valid_client2
    }.

  (* Minimal full validator protocol for name v: Validator(v) *)
  Definition labelv : Type := option C.

  Definition vtransitionv (v : V) (l : labelv) (sm : @sorted_state C V message_type * option proto_message) : @sorted_state C V message_type * option proto_message :=
    match l with
    | None => match (snd sm) with
             | None => sm 
             | Some msg => (add_message_sorted (proj1_sig msg) (fst sm), None)
           end
    | Some c => (add_message_sorted (c,v,proj1_sig (fst sm)) (fst sm), Some (make_proto_message (c,v,proj1_sig (fst sm)) (make_proto_message_prop (c,v,proj1_sig (fst sm)))))
    end. 
  
  Inductive valid_validator : labelv ->  @sorted_state C V message_type * option proto_message -> Prop :=
  | validator_none : forall (s : @sorted_state C V message_type), valid_validator None (s, None)
  | validator_receive : forall (s : @sorted_state C V message_type) (m : proto_message), reach (justification (proj1_sig m)) s -> valid_validator None (s, Some m)
  | validator_send : forall (c : C) (s : state) (m : option proto_message), (@estimator (@sorted_state C V message_type) C He) s c -> valid_validator (Some c) (s, m).

  Instance LSM_full_validator : LSM_sig (@message C V) :=
    { state := @sorted_state C V message_type
      ; label := labelv
      ; proto_message_prop := proto_message_prop 
      ; proto_message_decidable := proto_message_decidable
      ; initial_state_prop := initial_state_prop
      ; initial_message_prop := initial_message_prop
      ; s0 := state0
      ; m0 := proto_message0
      ; l0 := None
    }.

  Instance VLSM_full_validator (v : V) : @VLSM (@message C V) LSM_full_validator := 
    { transition := vtransitionv v
      ; valid := valid_validator
    }.

  Parameter validators : list V.
  Parameter v0 : V. 

  Lemma nat_eq_dec : EqDec nat.
  Proof.
    unfold EqDec. induction x; destruct y.
    - left. reflexivity.
    - right. intros HC; inversion HC.
    - right. intros HC; inversion HC.
    - specialize (IHx y). destruct IHx as [Heq | Hneq].
      + left. subst. reflexivity.
      + right. intros Heq. inversion Heq. contradiction.
  Qed.
  
  Lemma nat_inhabited : Logic.inhabited nat. 
  Proof. exact (inhabits 0). Qed.

  Definition IS_index : nat -> LSM_sig (@message C V) :=
    fun n =>
      match n with
      | 0 => LSM_full_client2
      | S n => LSM_full_validator
      end. 

  Definition IM_index : forall (n : nat), @VLSM (@message C V) (IS_index n).
  intros. 
  destruct n.
  exact VLSM_full_client2.
  exact (VLSM_full_validator (nth (n-1) validators v0)).
  Defined.

  Definition VLSM_full_composed :=
    @indexed_vlsm nat (@message C V) nat_eq_dec IS_index IM_index 0. 


