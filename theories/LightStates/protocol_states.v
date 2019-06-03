Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.
(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)



(** Parameters of the protocol **)

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.threshold.
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


(** TODO? Define protocol messages; also for the full version? **)

Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state state_empty
  | protocol_state_cons : forall c v sigma sigma',
      protocol_state sigma ->
      valid_estimate_condition c sigma ->
      In (c, v, hash_state sigma) sigma' ->
      protocol_state (state_remove (c, v, hash_state sigma) sigma')  ->
      NoDup sigma' ->
      fault_tolerance_condition sigma' ->
      protocol_state sigma' 
  .

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
    apply (set_eq_remove message_eq_dec (c, v, hash_state sigma)) in H5 as Hset_eq; try assumption.
    apply IHprotocol_state2 in Hset_eq. apply (protocol_state_cons c v sigma); try assumption.
    + destruct H5. apply (H5 (c, v, hash_state sigma)). assumption.
    + apply (fault_tolerance_condition_set_eq _ _ H5 H4).
    + apply set_remove_nodup. assumption.
Qed.

Definition Reachable (sigma1 sigma2 : state) : Prop :=
  protocol_state sigma1 /\ protocol_state sigma2 /\ incl sigma1 sigma2.

Notation "sigma2 'in_Futures' sigma1" :=
  (Reachable sigma1 sigma2)
  (at level 20).
