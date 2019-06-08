Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.
Require Import Casper.preamble.

(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)

(** Parameters of the protocol **)

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.hashes.

(** Messages **)

Require Import Casper.LightStates.messages.


(************)
(** States **)
(************)

Require Import Casper.LightStates.states.

Require Import Casper.LightStates.hash_state.

(***************)
(** Estimator **)
(***************)

Parameter estimator : state -> C -> Prop.

Parameter estimator_total : forall s : state, exists c : C, estimator s c.

(********************)
(* State properties *)
(********************)


Require Import Casper.LightStates.fault_weights.


(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The valid message condition **)

Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= t)%R.

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition [msg].
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_validators.
  simpl. unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. apply threshold_nonnegative.
Qed.

(** TODO? Define protocol messages; also for the full version? **)

Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state state_empty
  | protocol_state_cons : forall c v j sigma',
      protocol_state j -> (* 1 *)
      valid_estimate_condition c j ->  (* 2 *)
      In (c, v, hash_state j) sigma' ->
      protocol_state (state_remove (c, v, hash_state j) sigma')  ->
      NoDup sigma' ->
      fault_tolerance_condition sigma' ->
      protocol_state sigma'
  .

Lemma protocol_state_singleton : forall c v j,
  protocol_state j ->
  valid_estimate_condition c j ->
  protocol_state [(c, v, hash_state j)].
Proof.
  intros.
  apply protocol_state_cons with c v j; try assumption.
  - left. reflexivity.
  - simpl. rewrite eq_dec_if_true; constructor.
  - constructor; try constructor. apply in_nil.
  - apply fault_tolerance_condition_singleton.
Qed.

Lemma exist_equivocating_messages : forall nv vs,
  ~ In nv vs ->
  exists j1, exists j2, protocol_state j1 /\ protocol_state j2 /\
    (forall v,
      In v vs  ->
      exists c1, exists c2,
        valid_estimate_condition c1 j1 /\ valid_estimate_condition c2 j2 /\
        equivocating_messages (c1, v, hash_state j1) (c2, v, hash_state j2) = true
    )
  .
Proof.
  destruct (estimator_total []) as [c Hc].
  intros.
  destruct (estimator_total [(c, nv, [])]) as [c' Hc'].
  exists []. exists [(c, nv,[])]. repeat split; try constructor.
  intros.
  - apply (protocol_state_singleton c nv []) in Hc; try constructor. assumption.
  - intros. exists c. exists c'. repeat split; try assumption.
    unfold equivocating_messages. rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      apply andb_true_iff. split.
      * simpl. rewrite eq_dec_if_false; simpl; try reflexivity.
        intro. apply hash_injective in H1. inversion H1; subst. apply H. apply H0.
      * simpl. reflexivity.
    + intro. inversion H1.
Qed.


Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup sigma.
Proof.
  intros. inversion H; subst.
  - constructor.
  - assumption.
Qed.

Lemma fault_tolerance_condition_subset : forall sigma sigma',
  incl sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Lemma fault_tolerance_condition_set_eq : forall sigma sigma',
  set_eq sigma sigma' ->
  fault_tolerance_condition sigma ->
  fault_tolerance_condition sigma'.
Proof.
  intros. destruct H. apply (fault_tolerance_condition_subset _ _ H1 H0).
Qed.

Lemma set_eq_protocol_state : forall sigma,
  protocol_state sigma ->
  forall sigma',
  set_eq sigma sigma' ->
  NoDup sigma' ->
  protocol_state sigma'.
Proof.
  intros sigma H.
  induction H; intros.
  - destruct H. apply incl_empty in H1; subst. constructor.
  - clear IHprotocol_state1.
    apply (set_eq_remove message_eq_dec (c, v, hash_state j)) in H5 as Hset_eq; try assumption.
    apply IHprotocol_state2 in Hset_eq. apply (protocol_state_cons c v j); try assumption.
    + destruct H5. apply (H5 (c, v, hash_state j)). assumption.
    + apply (fault_tolerance_condition_set_eq _ _ H5 H4).
    + apply set_remove_nodup. assumption.
Qed.

Definition Reachable (sigma1 sigma2 : state) : Prop :=
  protocol_state sigma1 /\ protocol_state sigma2 /\ incl sigma1 sigma2.

Notation "sigma2 'in_Futures' sigma1" :=
  (Reachable sigma1 sigma2)
  (at level 20).

Lemma in_Futures_trans : forall sigma1 sigma2 sigma3,
  sigma1 in_Futures sigma2 ->
  sigma2 in_Futures sigma3 ->
  sigma1 in_Futures sigma3.
Proof.
  intros. destruct H as [Hps2 [Hps1 Hincl21]]. destruct H0 as [Hps3 [_ Hincl32]].
  repeat (split; try assumption). apply incl_tran with sigma2; assumption.
Qed.