Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation.
Import ListNotations.  
From Casper
Require Import preamble.

(* Thursday, 31st July *)

Class PartialOrder :=
  { A : Type;
    A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True;
    R : A -> A -> Prop;
    R_refl :> Reflexive R;
    R_trans :> Transitive R;
  }. 

Definition minimal_R `{PartialOrder} : A -> A -> Prop :=
  fun a1 a2 => R a1 a2 /\
            (forall a, R a1 a /\ R a a2 -> a1 = a \/ a2 = a).

Class PartialOrderNonLC `{PartialOrder} :=
  { no_local_confluence : forall (a : A), exists (a1 a2 : A),
        minimal_R a a1 /\ minimal_R a a2 /\
        ~ exists (a' : A), R a1 a' /\ R a2 a';
  }.

Theorem non_triviality `{PartialOrderNonLC} :
  exists (P : A -> Prop) (a1 a2 : A),
    (forall (a : A), R a1 a -> P a) /\
    (forall (a : A), R a2 a -> ~ P a). 
Proof.
  destruct A_inhabited as [a0 _].
  assert (H_LC := no_local_confluence a0).
  destruct H_LC as [a1 [a2 [H_left [H_right H_no_intersect]]]].
  (* The P we want is "can be reached by a1". 
     ~ P is therefore "cannot be reached by a1". *) 
  exists (fun a => R a1 a), a1, a2.
  split. intros; assumption.
  intros. intro Hnot. apply H_no_intersect.
  exists a. split; assumption.
Qed.

Class PartialOrderNonLCish `{PartialOrder} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        R a a1 /\ R a a2 /\
        ~ exists (a' : A), R a1 a' /\ R a2 a';
  }.

Theorem non_triviality_ish `{PartialOrderNonLCish} :
  exists (P : A -> Prop) (a1 a2 : A),
    (forall (a : A), R a1 a -> P a) /\
    (forall (a : A), R a2 a -> ~ P a). 
Proof.
  assert (H_LC := no_local_confluence_ish).
  destruct H_LC as [a0 [a1 [a2 [H_left [H_right H_no_intersect]]]]].
  exists (fun a => R a1 a), a1, a2.
  split. intros; assumption.
  intros. intro Hnot. apply H_no_intersect.
  exists a. split; assumption.
Qed.

Class ReachableStates :=
  { state : Type;
    state0 : state;
    reachable : state -> state -> Prop;
    reachable_trans :> Transitive reachable;
    reachable_refl :> Reflexive reachable;
  }.

(* Definition 3.1 *) 
Definition in_future `{ReachableStates} := reachable.

(* Lemma 1 : Monotonic futures *) 
Lemma monotonic_futures `{ReachableStates} :
  forall (s1 s2 : state),
    in_future s1 s2 <->
    forall (s : state),
      in_future s2 s -> in_future s1 s. 
Proof.
  intros s1 s2; split.
  - intros H_12 s H_s.
    now apply reachable_trans with s2.
  - intros H_s. spec H_s s2.
    apply H_s. apply reachable_refl. 
Qed.

Class MashableReachableStates `{ReachableStates} :=
  { mash : state -> state -> state;
    mash_comm :> Commutative mash;
    mash_reach : forall (s1 s2 : state), reachable s1 (mash s1 s2); 
  }. 

(* Instead of explicitly mentioning validators and fault weights etc. we abstract it into a predicate to describe good states, i.e. protocol states *) 
Class GoodMashableReachableStates `{MashableReachableStates} :=
  { is_good_state : state -> Prop;
    gstate : Type := {s : state | is_good_state s};
    gstate_proj1 (gs : gstate) := proj1_sig gs;
  }.

Coercion gstate_proj1 : gstate >-> state. 

(* Theorem 1 : 2-party common futures *) 
Theorem pairwise_common_futures `{GoodMashableReachableStates} :
  forall (gs1 gs2 : gstate),
    is_good_state (mash gs1 gs2) ->
    exists (gs : gstate),
      in_future gs1 gs /\ in_future gs2 gs. 
Proof.
  intros gs1 gs2 H_good.
  exists (exist is_good_state (mash gs1 gs2) H_good).
  split; simpl.
  apply mash_reach.
  rewrite mash_comm; apply mash_reach.
Qed.

Lemma in_future_iter `{GoodMashableReachableStates}:
  forall s ls, In s ls -> in_future s (fold_right mash state0 ls). 
Proof.
  intros s ls H_in.
  induction ls as [|hd tl IHtl].
  - inversion H_in.
  - destruct H_in as [H_eq | H_neq].
    + subst.
      simpl. apply mash_reach. 
    + spec IHtl H_neq. simpl.
      eapply reachable_trans with (fold_right mash state0 tl).        assumption.
      rewrite mash_comm.
      now apply mash_reach. 
Qed.

(* Theorem 2 : n-wise common futures *) 
Theorem nwise_common_futures `{GoodMashableReachableStates} :
  forall (ls : list gstate), 
    is_good_state (fold_right mash state0 (map gstate_proj1 ls)) ->
    exists (s : gstate),
      Forall (fun st => in_future st s) (map gstate_proj1 ls). 
Proof. 
  intros ls H_weight.
  exists (exist is_good_state (fold_right mash state0 (map gstate_proj1 ls)) H_weight).
  rewrite Forall_forall. 
  intros s H_in. simpl.
  now apply in_future_iter.
Qed.

(* Definition 3.3 : Decided properties of protocol states *)
Definition decided `{GoodMashableReachableStates} : (state -> Prop) -> state -> Prop :=
  fun P s => forall s', in_future s s' -> P s'. 

(* Lemma 2 : Forward consistency *) 
Lemma forward_consistency `{GoodMashableReachableStates} :
  forall s P,
    decided P s ->
    forall s',
      in_future s s' ->
      decided P s'.
Proof.
  intros s P H_dec s' H_rel.
  unfold decided in *.
  intros s'' H_rel'.
  assert (in_future s s'') by (apply (reachable_trans s s' s''); assumption).
  spec H_dec s''; now apply H_dec. 
Qed.

Definition negate `{GoodMashableReachableStates} : (state -> Prop) -> (state -> Prop) :=
  fun P => fun s => P s -> False. 

(* Lemma 3 : Backwards consistency *)
Lemma backwards_consistency `{GoodMashableReachableStates} :
   forall s s',
      in_future s s' ->
      forall P,
        decided P s' ->
        ~ decided (negate P) s.
Proof. 
  intros s s' H_rel P H_dec Hnot.
  spec Hnot s' H_rel.
  spec H_dec s'. spec H_dec.
  apply reachable_refl. contradiction. 
Qed.

(* Theorem 3 : Two-party consensus safety *)
Theorem pairwise_consensus_safety_state `{GoodMashableReachableStates} :
  forall (s1 s2 : gstate),
    is_good_state (mash s1 s2) -> 
    forall P, 
      ~ (decided P s1 /\ decided (negate P) s2).
Proof.
  intros s1 s2 H_weight P [H_dec H_dec_not]. 
  destruct (pairwise_common_futures s1 s2 H_weight) as [s [H_r1 H_r2]].
  spec H_dec s H_r1. spec H_dec_not s H_r2. contradiction.
Qed.

(* Consistency on state properties *) 
Definition state_consistency `{GoodMashableReachableStates} (ls : list state) : Prop :=
  exists (s : gstate),
  forall (P : state -> Prop),
    Exists (fun s => decided P s) ls ->
    P s.

(* Theorem 4 : n-party consensus safety *) 
Theorem nwise_consensus_safety_state `{GoodMashableReachableStates} :
  forall (ls : list gstate),
    is_good_state (fold_right mash state0 (map gstate_proj1 ls)) ->
    state_consistency (map gstate_proj1 ls). 
Proof. 
  intros ls H_weight. 
  destruct (nwise_common_futures ls H_weight) as [s' H_mash]. 
  exists s'. intros P H_exists. 
  apply Exists_exists in H_exists.
  destruct H_exists as [s'' [H_in'' H_dec'']].
  rewrite Forall_forall in H_mash. 
  spec H_mash s'' H_in''.
  spec H_dec'' s' H_mash.
  assumption.
Qed.

Class ConsensusGoodMashableReachableStates `{GoodMashableReachableStates} :=
  { consensus_value : Type;
    about_consensus_value :> StrictlyComparable consensus_value;
    estimator : state -> consensus_value -> Prop;
    estimator_total : forall (s : state), exists (c : consensus_value), estimator s c;
  }.

(* Consistency on consensus values *) 
Definition lift `{ConsensusGoodMashableReachableStates} (P : consensus_value -> Prop) : state -> Prop :=
  fun s => forall c : consensus_value, estimator s c -> P c.

Definition consensus_value_consistency `{ConsensusGoodMashableReachableStates} (ls : list state) : Prop :=
  exists c,
    forall (P : consensus_value -> Prop),
      Exists (fun s => decided (lift P) s) ls ->
      P c. 

(* Theorem 5 : n-party consensus safety for consensus value properties *)
Theorem nwise_consensus_safety_consensus_values `{ConsensusGoodMashableReachableStates} :
  forall (ls : list gstate),
    is_good_state (fold_right mash state0 (map gstate_proj1 ls)) ->
      consensus_value_consistency (map gstate_proj1 ls). 
Proof.
  intros ls H_weight. 
  destruct (nwise_common_futures ls H_weight) as [s H_mash].
  destruct (estimator_total s) as [c about_c]. 
  exists c. intros P H_exists.
  apply Exists_exists in H_exists.
  destruct H_exists as [s' [H_in' H_dec']].
  rewrite Forall_forall in H_mash.
  spec H_mash s' H_in'.
  spec H_dec' s H_mash.
  spec H_dec' c about_c. assumption.
Qed.

(* Now it gets interesting... incorporating messages *) 
Class CBCProtocolStates `{ConsensusGoodMashableReachableStates} :=
  { validator : Type;
    about_validator :> StrictlyComparable validator;
    message : Type;
    about_message :> StrictlyComparable message;
    estimate : message -> consensus_value;
    sender : message -> validator;
    justification : message -> state;
  }.


(* Definition 4.1 : Observed validators *) 
Definition observed `{CBCProtocolStates} : message -> validator -> Prop :=
  fun m v => sender m = v. 

(* Definition 4.2 : Later *)
(** THIS cannot be defined without the notion of states as sets of messages **) 

(* States as generic sets *)
(*
Fixpoint f_iter {A B : Type} (f : B -> A -> B) (la : list A) (b : B) :=
  match la with
  | [] => b
  | hd :: tl => f_iter f tl (f b hd)
  end.

Theorem f_iter_wrap {A B : Type} : forall lm1 lm2 s0 (f : B -> A -> B),
    f_iter f (lm1 ++ lm2) s0 = f_iter f lm2 (f_iter f lm1 s0). 
Proof.
  induction lm1 as [| hd1 tl1 IHlm1].
  - easy.
  - intros lm2 s0 f. simpl. spec IHlm1 lm2 (f s0 hd1) f.
    exact IHlm1.
Qed.

Class StateProtocol :=
  { S : Type;
    S_dec : forall (s1 s2 : S), {s1 = s2} + {s1 <> s2};
    state := set S;
    state0 : state := [];
    state_union : state -> state -> state := set_union S_dec;

    message : Type;
    message_dec : forall (m1 m2 : message), {m1 = m2} + {m1 <> m2};
    send_message : state -> message -> state;

    good_message : state -> message -> Prop;
    good_message_preserved : forall s m, good_message s m ->
                                    good_message (send_message s m) m;

    prot_state : state -> Prop;
    pstate := {s : state | prot_state s};
    pstate_proj1 (ps : pstate) := proj1_sig ps;
    
  }.

Definition in_future `{StateProtocol} : state -> state -> Prop :=
  fun s1 s2 => exists lm, Forall (good_message s1) lm /\ f_iter send_message lm s1 = s2.

Theorem good_message_future_preserved `{StateProtocol} :
  forall s m, good_message s m ->
         forall lm, Forall (good_message s) lm ->
               good_message (f_iter send_message lm s) m. 
Proof. 
  intros s m H_good lm.
  induction lm as [|hd tl IHlm];
    intros H_allgood. 
  - simpl; assumption. 
  - simpl. spec IHlm.
    apply Forall_forall. intros msg H_in.
    rewrite Forall_forall in H_allgood.
    spec H_allgood msg. spec H_allgood.
    right; assumption. assumption.
    (* This is just not true *)
Abort. 

Theorem in_future_trans `{StateProtocol} :
  forall s1 s2 s3,
    in_future s1 s2 ->
    in_future s2 s3 ->
    in_future s1 s3. 
Proof.
  intros s1 s2 s3 H_12 H_23. assert (H_12_copy := H_12).
  destruct H_12 as [lm12 [H_good12 H_step12]].
  destruct H_23 as [lm23 [H_good23 H_step23]].
  exists (lm12 ++ lm23).
  split.
  - rewrite Forall_forall in *.
    intros x H_in.
    rewrite in_app_iff in H_in.
    destruct H_in as [left | right].
    spec H_good12 x left; now apply H_good12.
    (* Now we have some strange additional assumption required... *)
    spec H_good23 x right.
    unfold in_future in H_12_copy.
    now apply good_message_preservation with s2.
  - rewrite <- H_step12 in H_step23.
    now rewrite f_iter_wrap.
Qed.


(* States with decidable equality *) 
Definition state := Type.
Parameter state0 : state.
Parameter state_dec : forall (s1 s2 : state), {s1 = s2} + {s1 <> s2}. 
Parameter state_incl : state -> state -> Prop. 

Parameter fault_weight : state -> R. 
Parameter good_weight : state -> Prop.
Parameter good_weight_state0 : good_weight state0. 

Definition C := Type. 
Definition V := Type.
Parameter estimator : state -> C -> Prop.
Parameter estimator_total : forall s, exists c, estimator s c.

Parameter mash : state -> C -> V -> state -> state. 
Parameter mush : state -> state -> state.

Inductive protocol_state : state -> nat -> Prop :=
| init : protocol_state state0 0
| next : forall (s : state) (n : nat),
    protocol_state s n ->
    forall (s' : state),
      state_incl s' s ->
      forall (c : C),
        estimator c s' ->
        forall (v : V),
          good_weight (mash s c v s') ->
          protocol_state (mash s c v s') (S n). 

Definition pstate (n : nat) : Type := {s : state | protocol_state s n}. 
Definition pstate_proj1 {n : nat} (ps : pstate n) := proj1_sig ps. 
Coercion pstate_proj1 : pstate >-> state.

(* Messages *) 
Definition message := Type.
Parameter message0 : message.

(* Some guarantee for valid messages *) 
Parameter is_good_message : state -> message -> Prop. 

(* Some guarantee for good states *) 
Inductive is_good_state_indexed : state -> nat -> Prop := 
| good_state_O : is_good_state_indexed state0 0 
| good_state_S : forall s m n, is_good_state_indexed s n -> is_good_message s m -> is_good_state_indexed (mush s m) (n+1). 

Inductive is_good_state : state -> Prop :=
| good0 : is_good_state state0
| goodS : forall s m, is_good_state s -> is_good_message s m -> is_good_state (mush s m). 

Definition reachable_one (s1 s2 : state) := 
  exists (m : message), is_good_message s1 m /\ s2 = mush s1 m. 

(* It's unreasonable to define chucking in a bunch of messages at once, because they need to be checked step-wise *)

Theorem onestep_reachable_states_are_good_indexed :
  forall s n, is_good_state_indexed s n ->
       forall s', reachable_one s s' -> 
             exists m, is_good_state_indexed s' m. 
Proof.
  intros.
  destruct H0 as [msg [H_good H_eq]].
  subst.
  exists (n+1). now apply good_state_S. 
Qed.

Theorem reachable_states_are_good :
  forall s, is_good_state s ->
       forall s', reachable_one s s' -> 
             is_good_state s'. 
Proof.
  intros.
  destruct H0 as [msg [H_good H_eq]].
  subst.
  now apply goodS. 
Qed.

Definition good_path (p : nat -> state) := 
  forall n, reachable_one (p n) (p (n+1)). 

Definition in_path (s : state) (p : nat -> state) := 
  exists n, p n = s. 

Definition in_future (s1 s2 : state) := 
  exists p, good_path p /\
       exists m n, m > n /\
              p n = s1 /\
              p m = s2. 

(* It may be straightforward to define state inclusion in terms of mushing, but it's less straightforward to define state union in terms of mushing. *)

(* Perhaps we want to rely on functional choice here *)
(* The union of two states exists if there is an intersection of two good paths that include each state in its respective past *)
Definition is_union (s s1 s2 : state) :=
  exists (p1 p2 : nat -> state) (n1 n2 : nat), p1 n1 = s /\ p2 n2 = s /\
                                     exists (m1 m2 : nat),
                                       m1 < n1 /\ p1 m1 = s1 /\
                                       m2 < n2 /\ p2 m2 = s2.

Theorem exists_union : forall (s1 s2 : state),
  exists s, is_union s s1 s2. 
Proof. Admitted. 

Axiom functional_choice : forall (X : Type) (P : X -> Prop), (exists x, P x) -> {x : X | P x}. 

Program Definition union (s1 s2 : state) : state := proj1_sig (functional_choice state (fun s => is_union s s1 s2) (exists_union s1 s2)).

Theorem union_is_union :
  forall s1 s2, is_union (union s1 s2) s1 s2. 
Proof.
  intros s1 s2; unfold is_union; unfold union; simpl.
Admitted.
(* This must be provable in some generic form *) 

Definition t_state : Type := {s : state | good_weight s}.
Definition t_state_proj1  (ts : t_state) := proj1_sig ts. 
Coercion t_state_proj1 : t_state >-> state.

Theorem one : forall (s1 s2 : t_state),
    good_weight (union (proj1_sig s1) (proj1_sig s2)) ->
    exists (s : t_state), in_future s1 s /\ in_future s2 s. 
Proof.
  intros.
  assert (H_useful := union_is_union s1 s2). 
  destruct H_useful as [p1 [p2 [n1 [n2 [H_eq1 [H_eq2 [m1 [m2 H_useful]]]]]]]].
  exists (exist _ (union (proj1_sig s1) (proj1_sig s2)) H).
  split. red. exists p1. repeat split. admit.
  destruct H_useful. destruct H1. destruct H2. exists n1, m1. split. 
  assumption. split. assumption. simpl. assumption.
  simpl. split. destruct H_useful. destruct H1. destruct H2.
  assumption. simpl. symmetry. omega. H_useful. omega. impl. unfold union.  red. simpl. red. Parameter union : state -> statep -> state. 

Variables (message : Type) (state : Type).
Parameter          (state_dec : forall (x y : state), {x = y} + {x <> y}). 

Check set_add state_dec.

Definition add_message (m : state) (states : set state) :=
  set_map state_dec (set_add state_dec m) states. 
Class ZeeZee :=
  { state : Type;
    message : Type;
    f : set (set state) -> set (set message) -> set (set state) -> set (set message) := 
    
    
*)    
