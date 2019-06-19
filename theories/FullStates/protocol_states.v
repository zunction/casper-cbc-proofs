Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)


(** Parameters of the protocol **)

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.threshold.


(** Messages and States **)

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.


(***************)
(** Estimator **)
(***************)

Parameter estimator : state -> C -> Prop.

Parameter estimator_total : forall s : state, exists c : C, estimator s c.

(** State membership **)
Require Import Casper.FullStates.in_state.

(** Canonical representation of states **)

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.list_to_state.


(*******************************)
(** Protocol state conditions **) 
(*******************************)


Require Import Casper.FullStates.fault_weights.


(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    syntactic_state_inclusion sigma1 sigma2.

(** The valid message condition **)
Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.


(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= t)%R.

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition (next msg Empty).
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_validators.
  simpl. unfold equivocating_message_state. simpl.
  unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. apply threshold_nonnegative.
Qed.

Lemma fault_tolerance_condition_subset : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

(** Protocol states **)
Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall c v sigma sigma',
      protocol_state sigma -> (* 1 *)
      protocol_state sigma' ->
      syntactic_state_inclusion sigma sigma' ->
      valid_estimate_condition c sigma ->
      fault_tolerance_condition (add_in_sorted_fn (c, v, sigma) sigma') ->
      protocol_state (add_in_sorted_fn (c, v, sigma) sigma')
  .

Lemma protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, sigma) sigma'); try assumption.
    apply locally_sorted_message_justification. assumption.
Qed.

Lemma protocol_state_singleton : forall c v,
  valid_estimate_condition c Empty ->
  protocol_state (next (c, v, Empty) Empty).
Proof.
  intros.
  assert (Heq : add_in_sorted_fn (c, v, Empty) Empty = (next (c, v, Empty) Empty))
  ; try reflexivity.
  rewrite <- Heq.
  apply protocol_state_next; try assumption; try apply protocol_state_empty.
  - apply incl_refl. 
  - simpl. rewrite add_is_next. apply fault_tolerance_condition_singleton.
Qed.

(* 
Lemma exist_equivocating_messages : forall vs,
  vs <> nil ->
  exists j1, exists j2, protocol_state j1 /\ protocol_state j2 /\ j1 <> j2 /\
    exists c1, exists c2,
      valid_estimate_condition c1 j1 /\ valid_estimate_condition c2 j2 /\
      (forall v,
        In v vs  ->
          equivocating_messages (c1, v, j1) (c2, v, j2) = true
      )
  .
Proof.
  destruct (estimator_total Empty) as [c Hc].
  intros.
  destruct vs; try (exfalso; apply H; reflexivity); clear H. 
  destruct (estimator_total (next (c, v, Empty) Empty)) as [c' Hc'].
  destruct (estimator_total (add_in_sorted_fn (c', v, (next (c, v, Empty) Empty)) (next (c, v, Empty) Empty))) as [c'' Hc''].
  destruct (set_eq_add_in_sorted (c', v, next (c, v, Empty) Empty) (next (c, v, Empty) Empty)).
  exists Empty. exists (add_in_sorted_fn (c', v, (next (c, v, Empty) Empty)) (next (c, v, Empty) Empty)). repeat split; try constructor
  ; try apply protocol_state_singleton; try assumption; try apply incl_refl.
  - apply fault_tolerance_condition_subset with
      (next (c', v, next (c, v, Empty) Empty) (next (c, v, Empty) Empty))
    ; try assumption.
    unfold fault_tolerance_condition. unfold fault_weight_state.
    unfold equivocating_validators. simpl.
    unfold equivocating_message_state. simpl.
    unfold equivocating_messages.
    rewrite eq_dec_if_true; try reflexivity.
    rewrite eq_dec_if_false; try (intro Contra; inversion Contra).
    rewrite eq_dec_if_true; try reflexivity.
    unfold in_state_fn. rewrite in_state_dec_if_false
    ; try (unfold in_state; simpl; intro Contra; inversion Contra)
    ; simpl
    .
    rewrite in_state_dec_if_true
    ; try (unfold in_state; simpl; left; reflexivity)
    ; simpl
    .
    rewrite eq_dec_if_false; try (intro Contra; inversion Contra).
    rewrite eq_dec_if_true; try reflexivity.
    rewrite eq_dec_if_true; try reflexivity.
    simpl.
    apply Rge_le. apply threshold_nonnegative.
  - intro Contra. symmetry in Contra.
    apply (add_in_sorted_non_empty _ _ Contra).
  - exists c. exists c''. repeat split; try assumption.
    intros. unfold equivocating_messages. rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      apply andb_true_iff. split; apply negb_true_iff
      ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity
      ; unfold in_state; try apply in_nil.
      intro.
      destruct (set_eq_add_in_sorted ((c', v, next (c, v, Empty) Empty)) (next (c, v, Empty) Empty)). 
      apply H3 in H2. simpl in H2.
      admit.
    + intro Contra. inversion Contra; subst; clear Contra. 
      destruct (message_compare (c', v, add (c'', v, Empty)to Empty) (c'', v, Empty))
      ; inversion H4.
  Admitted.

Lemma extended_protocol_state : forall vs sigma,
  protocol_state sigma ->
  exists sigma',
  protocol_state sigma' /\
  incl vs (map validator (get_messages sigma')) /\
  fault_weight_state sigma' = fault_weight_state sigma.
Proof.
  induction vs; intros.
  - exists sigma. split; try assumption. split; try reflexivity.
    intros x Hin. inversion Hin.
  - destruct (IHvs sigma H) as [sigma' [Hps [Hincl Hfw]]].
    destruct (estimator_total sigma') as [c Hc].
  Admitted.

Lemma binary_justification_protocol_state : forall vs c1 j1 c2 j2,
  protocol_state j1 ->
  protocol_state j2 ->
  j1 <> j2 ->
  valid_estimate_condition c1 j1 ->
  valid_estimate_condition c2 j2 ->
  NoDup vs ->
  fault_tolerance_condition (list_to_state (flat_map (fun v => [(c1, v, j1); (c2, v, j2)]) vs)) ->
  protocol_state (list_to_state (flat_map (fun v => [(c1, v, j1); (c2, v, j2)]) vs))
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
*)

Definition Reachable sigma1 sigma2 :=
  protocol_state sigma1 /\ protocol_state sigma2 /\ syntactic_state_inclusion sigma1 sigma2.

Notation "sigma2 'in_Futures' sigma1" :=
  (Reachable sigma1 sigma2)
  (at level 20).

Lemma in_Futures_trans : forall sigma1 sigma2 sigma3,
  sigma1 in_Futures sigma2 ->
  sigma2 in_Futures sigma3 ->
  sigma1 in_Futures sigma3.
Proof.
  intros. destruct H as [Hps2 [Hps1 Hincl21]]. destruct H0 as [Hps3 [_ Hincl32]].
  repeat (split; try assumption). apply incl_tran with (get_messages sigma2); assumption.
Qed.
