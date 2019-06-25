Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.
Require Import Casper.preamble.

(** Parameters of the protocol **)

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.justifications.

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
  unfold equivocating_senders.
  simpl. unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. apply threshold_nonnegative.
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

Lemma exist_equivocating_messages : forall vs,
  vs <> nil ->
  exists j1, exists j2, protocol_state j1 /\ protocol_state j2 /\ ~ set_eq j1 j2 /\
    exists c1, exists c2,
      valid_estimate_condition c1 j1 /\ valid_estimate_condition c2 j2 /\
      (forall v,
        In v vs  ->
          equivocating_messages (c1, v, hash_state j1) (c2, v, hash_state j2) = true
      )
  .
Proof.
  destruct (estimator_total []) as [c Hc].
  intros.
  destruct vs; try (exfalso; apply H; reflexivity); clear H. 
  destruct (estimator_total [(c, v, [])]) as [c' Hc'].
  destruct (estimator_total [(c', v, hash_state [(c, v, [])])]) as [c'' Hc''].
  exists []. exists [(c', v, hash_state [(c, v, [])])]. repeat split; try constructor.
  - apply (protocol_state_singleton c' v [(c, v, [])]) in Hc'; try constructor; try assumption.
    apply (protocol_state_singleton c v []) in Hc; try constructor; assumption.
  - intro. destruct H. apply incl_empty in H0. inversion H0.
  - exists c. exists c''. repeat split; try assumption.
    intros. unfold equivocating_messages. rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      apply andb_true_iff. split.
      * unfold hash_state. simpl. unfold justification_add. simpl.
        unfold justification_in. unfold inb.
        rewrite eq_dec_if_false; simpl; try reflexivity.
        intro. apply hash_injective in H0. inversion H0; subst.
      * simpl. reflexivity.
    + intro. inversion H0.
Qed.

Lemma binary_justification_nodup : forall (vs : list V) (c1 c2 : C) (j1 j2 : state),
  ~ set_eq j1 j2 ->
  NoDup vs ->
  NoDup (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - simpl. apply NoDup_cons_iff in H0. destruct H0 as [Hnin Hnodup]. constructor.
    + intro H0. destruct H0.
      * apply H. inversion H0; subst; clear H0. apply hash_state_injective in H3.
        apply set_eq_comm. assumption.
      * apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
    + apply IHvs in Hnodup. apply NoDup_cons_iff; split; try assumption. intro.
      apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
      destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
Qed.

Lemma binary_justification_protocol_state : forall vs c1 j1 c2 j2,
  protocol_state j1 ->
  protocol_state j2 ->
  ~ set_eq j1 j2 ->
  valid_estimate_condition c1 j1 ->
  valid_estimate_condition c2 j2 ->
  NoDup vs ->
  fault_tolerance_condition (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) ->
  protocol_state (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)
  .
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - apply NoDup_cons_iff in H4. destruct H4 as [Hanin Hnodup].
    simpl. apply protocol_state_cons with c1 a j1; try assumption.
    + left; reflexivity.
    + simpl. rewrite eq_dec_if_true; try reflexivity.
      apply protocol_state_cons with c2 a j2; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply IHvs; try assumption.
        apply fault_tolerance_condition_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map in Hin. apply in_flat_map.
        destruct Hin as [v [Hinv Hinx]].
        exists v. split; try assumption. right. assumption.
      * apply NoDup_cons_iff. split; try apply binary_justification_nodup; try assumption.
        intro. apply Hanin.
        apply in_flat_map in H4. destruct H4 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
      * apply fault_tolerance_condition_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map.
        { destruct Hin as [Heq | Hin].
          - subst. exists a. split; try (left; reflexivity). right. left. reflexivity.
          - apply in_flat_map in Hin. destruct Hin as [v [Hinv Hin]].
            exists v. split; try assumption. right. assumption.
        }
    + apply NoDup_cons_iff. split.
      * intro.
        { destruct H4 as [Heq | Hin].
          - apply H1. inversion Heq; subst; clear Heq. apply hash_state_injective.
            rewrite H7. reflexivity.
          - apply Hanin.
            apply in_flat_map in Hin. destruct Hin as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
        }
      * apply NoDup_cons_iff.
        { split.
          - intro. apply Hanin.
            apply in_flat_map in H4. destruct H4 as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
          - apply binary_justification_nodup; assumption.
        }
Qed.

Lemma protocol_state_nodup : forall sigma,
  protocol_state sigma ->
  NoDup sigma.
Proof.
  intros. inversion H; subst.
  - constructor.
  - assumption.
Qed.

Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition sigma.
Proof.
  intros. inversion H.
  - unfold fault_tolerance_condition. unfold fault_weight_state. simpl.
    apply Rge_le. apply threshold_nonnegative.
  - assumption.
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