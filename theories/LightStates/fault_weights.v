Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.consensus_values.
Require Import Casper.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.sorted_lists.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.states.

Definition equivocating_messages (msg1 msg2 : message) : Prop :=
  match msg1, msg2 with
    (c1, v1, j1), (c2, v2, j2) =>
      v1 = v2 /\
      (c1 <> c2 \/ j1 <> j2) /\
      not (In (Hash (c1,v1,j1)) j2) /\
      not (In (Hash (c2,v2,j2)) j1)
  end.

Definition equivocating_messages_fn (msg1 msg2 : message) : bool :=
  match message_compare msg1 msg2 with
  | Eq => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match v_compare v1 v2 with
      | Eq => negb (hash_list_in (Hash msg1) j2) && negb (hash_list_in (Hash msg2) j1)
      | _ => false
      end
    end
  end.

Lemma equivocating_messages_function : forall msg1 msg2,
  equivocating_messages msg1 msg2 <-> equivocating_messages_fn msg1 msg2 = true.
Proof.
  intros [(c1, v1) j1] [(c2, v2) j2]; unfold equivocating_messages_fn; split; intros.
  - destruct H as [Hv [[Hc | Hj] [Hin2 Hin1]]]; subst
    ; rewrite v_compare_refl
    ; apply hash_list_compare_not_in in Hin1
    ; apply hash_list_compare_not_in in Hin2
    ; rewrite Hin1
    ; rewrite Hin2
    ; simpl
    ; rewrite v_compare_refl
    ; destruct (c_compare c1 c2) eqn:Hcc
    ; ( apply compare_lt_neq in Hcc
      || apply compare_gt_neq in Hcc
      || apply (proj1 c_compare_strict_order) in Hcc
      )
    ; try apply (proj1 c_compare_strict_order)
    ; try reflexivity.
    + exfalso. apply Hc. assumption.
    + destruct (hash_list_compare j1 j2) eqn:Hjc
      ; ( apply compare_lt_neq in Hjc
        || apply compare_gt_neq in Hjc
        || apply (proj1 hash_list_compare_strict_order) in Hjc
        )
      ; try apply (proj1 hash_list_compare_strict_order)
      ; try reflexivity
      .
      exfalso; apply Hj; apply Hjc.
  - destruct (message_compare (c1, v1, j1) (c2, v2, j2)) eqn:Hmsg
    ; destruct (v_compare v1 v2) eqn:Hv
    ; try discriminate
    ; apply (proj1 v_compare_strict_order) in Hv
    ; subst
    ; apply andb_true_iff in H
    ; destruct H as [Hj2 Hj1]
    ; apply negb_true_iff in Hj1
    ; apply negb_true_iff in Hj2
    ; apply hash_list_compare_not_in in Hj1
    ; apply hash_list_compare_not_in in Hj2
    ; split ; try reflexivity
    ; repeat (split; try assumption)
    ; clear Hj1; clear Hj2
    ; (apply compare_lt_neq in Hmsg || apply compare_gt_neq in Hmsg)
    ; try apply (proj1 message_compare_strict_order)
    ; apply message_neq in Hmsg
    ; destruct Hmsg as [Hc | [Hv | Hj]]
    ; try (left; assumption)
    ; try (right; assumption)
    ; exfalso; apply Hv; reflexivity
    .
Qed.


Definition equivocating_message_state (msg : message) : state -> Prop :=
  Exists (equivocating_messages msg).

Definition equivocating_message_state_fn (msg : message) : state -> bool :=
  existsb (equivocating_messages_fn msg).

Lemma equivocating_message_state_function : forall msg sigma,
  equivocating_message_state msg sigma
  <->
  equivocating_message_state_fn msg sigma = true
  .
Proof.
  unfold equivocating_message_state_fn. unfold equivocating_message_state.
  intros.
  rewrite existsb_exists. rewrite Exists_exists.
  split; intros; destruct H as [x [Hin H]]; exists x; split; try assumption
  ; apply equivocating_messages_function; try assumption.
Qed.

Inductive equivocating_validators : state -> list V -> Prop :=
  equivocating_validators_intro : forall sigma vs emsgs,
    filter_rel (fun msg => equivocating_message_state msg sigma) sigma emsgs ->
    fold_rel (fun msg => @add_in_sorted_list V v_lt (validator msg)) [] emsgs vs ->
    equivocating_validators sigma vs.

Definition equivocating_validators_fn (sigma : state) : list V :=
  fold_right (fun msg vs => @add_in_sorted_list_fn V v_compare (validator msg) vs) []
    (filter (fun msg => equivocating_message_state_fn msg sigma) sigma).

Definition fault_weight_state_fn (sigma : state) : R :=
  (fold_right Rplus 0%R (map weight (equivocating_validators_fn sigma))).
