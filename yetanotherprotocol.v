Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation.
Import ListNotations.  
From Casper
Require Import preamble.

(* Monday, 29th July *)

Class MessageProtocol :=
  {
    state : Type;
    state0 : state;
    message : Type;
    good_message : state -> message -> Prop;
    (* Subset relation *) 
    send_message : state -> message -> state;
    (* State union operation *)
    reachable := fun s1 s2 => exists (lm : list message),
                     fold_left send_message lm s1 = s2; 
    mash : state -> state -> state;
    mash_comm : forall s1 s2, mash s1 s2 = mash s2 s1;
    (* *)
    mash_in_future : forall s1 s2, exists lm, Forall (good_message s1) lm /\ fold_left send_message lm s1 = mash s1 s2;
    (* *) 
    good_message_preservation : forall m s1 s2, good_message s2 m ->
                                           (exists lm, Forall (good_message s1) lm /\ fold_left send_message lm s1 = s2) ->
                                           good_message s1 m;
  }.

(*
Context (MP : `{MessageProtocol}). 

Definition steppable : state -> state -> Prop :=
  fun s1 s2 => exists m, good_message s1 m /\ send_message s1 m = s2. 

Definition reachable : state -> state -> Prop :=
  fun s1 s2 => exists lm, Forall (good_message s1) lm /\ f_iter send_message lm s1 = s2. 

*)


Definition in_future `{MessageProtocol} : state -> state -> Prop :=
   fun s1 s2 => exists lm, Forall (good_message s1) lm /\ fold_left send_message lm s1 = s2. 

Theorem in_future_trans `{MessageProtocol} :
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
    now rewrite fold_left_app.
Qed.

Section Safety. 

  Context (H_M : `{MessageProtocol}). 
  Parameters (C : Type)
             (estimator : state -> C -> Prop)
             (estimator_total : forall s, exists c, estimator s c). 
  
  Parameters (good_state : state -> Prop)
             (good_state0 : good_state state0). 
  Definition t_state : Type := {s : state | good_state s}.
  Definition t_state_proj1 (ts : t_state) := proj1_sig ts. 
  Coercion t_state_proj1 : t_state >-> state.
  
  Theorem one :
    forall (s1 s2 : t_state),
      good_state (mash s1 s2) -> 
      exists (s : t_state),
        in_future s1 s /\ in_future s2 s. 
  Proof. 
    intros s1 s2 H_weight. 
    exists (exist good_state (mash s1 s2) H_weight). 
    split; simpl; try apply mash_in_future.
    rewrite mash_comm; apply mash_in_future.
  Qed.

  Lemma in_future_iter :
    forall s ls, In s ls -> in_future s (fold_right mash state0 ls). 
  Proof.
    intros s ls H_in.
    induction ls as [|hd tl IHtl].
    - inversion H_in.
    - destruct H_in as [H_eq | H_neq].
      + subst.
        simpl. apply mash_in_future. 
      + spec IHtl H_neq. simpl.
        eapply in_future_trans with (fold_right mash state0 tl). 
        assumption.
        rewrite mash_comm.
        now apply mash_in_future. 
  Qed.

  Theorem two :
    forall (ls : list t_state), 
      good_state (fold_right mash state0 (map t_state_proj1 ls)) ->
      exists (s : t_state),
        Forall (fun st => in_future st s) (map t_state_proj1 ls). 
  Proof. 
    intros ls H_weight.
    exists (exist good_state (fold_right mash state0 (map t_state_proj1 ls)) H_weight).
    rewrite Forall_forall. 
    intros s H_in. simpl.
    now apply in_future_iter.
  Qed.

  Definition decided `{MessageProtocol} : state -> (state -> Prop) -> Prop :=
    fun s P => forall s', in_future s s' -> P s'. 

  Definition negate `{MessageProtocol} : (state -> Prop) -> (state -> Prop) :=
    fun P => fun s => P s -> False. 

  Lemma forward_consistency `{MessageProtocol} :
    forall s P,
      decided s P ->
      forall s',
        in_future s s' ->
        decided s' P.
  Proof.
    intros s P H_dec s' H_rel.
    unfold decided in *.
    intros s'' H_rel'.
    assert (in_future s s'') by (apply (in_future_trans s s' s''); assumption).
    spec H_dec s''; now apply H_dec. 
  Qed.

  Lemma backward_consistency `{MessageProtocol} :
    forall s s',
      in_future s s' ->
      forall P,
        decided s' P ->
        ~ decided s (negate P).
  Proof. 
    intros s s' H_rel P H_dec Hnot.
    spec Hnot s' H_rel.
    spec H_dec s'. spec H_dec.
    unfold in_future. exists [].
    split; easy. contradiction.
  Qed.

  Theorem three `{MessageProtocol} :
    forall (s1 s2 : t_state),
      good_state (mash s1 s2) -> 
      forall P, 
        ~ (decided s1 P /\ decided s2 (negate P)).
  Proof.
    intros s1 s2 H_weight P [H_dec H_dec_not]. 
    destruct (one s1 s2 H_weight) as [s [H1 H2]].
    spec H_dec s H1. spec H_dec_not s H2. contradiction.
  Qed. 

  (* Consistency on state properties *) 
  Definition state_consistency (ls : list state) : Prop :=
    exists (s : t_state),
    forall (P : state -> Prop),
      Exists (fun s => decided s P) ls ->
      P s.

  Theorem four :
    forall (ls : list t_state),
      good_state (fold_right mash state0 (map t_state_proj1 ls)) ->
      state_consistency (map t_state_proj1 ls). 
  Proof. 
    intros ls H_weight. 
    destruct (two ls H_weight) as [s' H_mash]. 
    exists s'. intros P H_exists. 
    apply Exists_exists in H_exists.
    destruct H_exists as [s'' [H_in'' H_dec'']].
    rewrite Forall_forall in H_mash. 
    spec H_mash s'' H_in''.
    spec H_dec'' s' H_mash.
    assumption.
  Qed.

  (* Consistency on consensus values *) 
  Definition lift (P : C -> Prop) : state -> Prop :=
    fun s => forall c : C, estimator s c -> P c.

  Definition consensus_value_consistency (ls : list state) : Prop :=
    exists c,
      forall (P : C -> Prop),
        Exists (fun s => decided s (lift P)) ls ->
        P c. 

  (* Theorem 5 *)
  Theorem five :
    forall (ls : list t_state),
      good_state (fold_right mash state0 (map t_state_proj1 ls)) ->
      consensus_value_consistency (map t_state_proj1 ls). 
  Proof.
    intros ls H_weight. 
    destruct (two ls H_weight) as [s H_mash].
    destruct (estimator_total s) as [c about_c]. 
    exists c. intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s' [H_in' H_dec']].
    rewrite Forall_forall in H_mash.
    spec H_mash s' H_in'.
    spec H_dec' s H_mash.
    spec H_dec' c about_c. assumption.
  Qed.

End Safety.
