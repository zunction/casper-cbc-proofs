Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.list_to_state.
Require Import Casper.FullStates.threshold.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.protocol_states.
Require Import Casper.FullStates.state_union.

Module Type Common_Futures
              (PCons : Consensus_Values) 
              (PVal : Validators)
              (PStates : States PCons PVal)
              (PMessages : Messages PCons PVal PStates)
              (PIn_State : In_State PCons PVal PStates PMessages)
              (PLocally_Sorted : Locally_Sorted PCons PVal PStates PMessages PIn_State)
              (PAdd_In_Sorted : Add_In_Sorted PCons PVal PStates PMessages PIn_State PLocally_Sorted) 
              (PLists_To_State : List_To_State PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted)
              (PFault_Weights : Fault_Weights PCons PVal PStates PMessages PIn_State PLocally_Sorted)
              (PThreshold : Threshold PCons PVal PStates PMessages PIn_State PLocally_Sorted PFault_Weights)
              (PProtocol_States : Protocol_States PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted PLists_To_State PFault_Weights PThreshold)
              (PState_Union : State_Union PCons PVal PStates PMessages PIn_State PLocally_Sorted  PAdd_In_Sorted PLists_To_State)
              .

(* import the Module parameters in order to have access to 
   its parameters without having to use the DotNotation. *)
Import PCons.
Import PVal.
Import PStates.
Import PMessages.
Import PIn_State.
Import PLocally_Sorted.
Import PAdd_In_Sorted.
Import PLists_To_State.
Import PFault_Weights.
Import PThreshold.
Import PProtocol_States.
Import PState_Union.

(** Two party common futures **)

Lemma union_protocol_2states : forall sigma1 sigma2,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  fault_tolerance_condition (state_union sigma1 sigma2) ->
  protocol_state (state_union sigma1 sigma2).
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - unfold state_union. simpl. rewrite list_to_state_sorted; try assumption.
    apply protocol_state_sorted. assumption.
  - clear IHHps2_1.
    rewrite (state_union_add_in_sorted sig1 (c, v, sigma) sigma') in *
    ; try (apply (locally_sorted_message_justification c v sigma))
    ; try (apply protocol_state_sorted; assumption)
    .
    assert (protocol_state (state_union sig1 sigma')).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with
        (add_in_sorted_fn (c, v, sigma) (state_union sig1 sigma'))
      ; try assumption.
      intros msg Hin. apply set_eq_add_in_sorted. right. assumption.
    }
    constructor; try assumption.
    + intros msg Hin. apply state_union_iff. right. apply H. assumption.
Qed.

Theorem two_party_common_futures : forall sigma1 sigma2,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  fault_tolerance_condition (state_union sigma1 sigma2) ->
  exists sigma',
  protocol_state sigma' /\
  sigma' in_Futures sigma1  /\
  sigma' in_Futures sigma2.
Proof.
  intros.
  exists (state_union sigma1 sigma2).
  split.
  - apply (union_protocol_2states _ _ H H0 H1).
  - split; constructor; try assumption ; split; try apply union_protocol_2states; try assumption; intros msg Hin; apply state_union_messages; apply set_union_intro.
    + left. assumption.
    + right. assumption.
Qed.

Lemma union_protocol_nstates : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  protocol_state (fold_right state_union Empty sigmas).
Proof.
  induction sigmas; intros.
  - simpl. constructor.
  - inversion H; subst; clear H.
    simpl in H0. 
    apply (fault_tolerance_condition_subset (fold_right state_union Empty sigmas)) in H0 as Hftc.
    + simpl. apply union_protocol_2states; try assumption. apply IHsigmas; try assumption.
    + apply state_union_incl_right.
Qed.

Theorem n_party_common_futures : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  exists sigma',
    protocol_state(sigma') /\
    Forall (fun sigma => sigma' in_Futures sigma) sigmas.
Proof.
  intros.
  exists (fold_right state_union Empty sigmas).
  apply (union_protocol_nstates sigmas) in H0; try assumption.
  split; try assumption.
  apply Forall_forall; intros.
  rewrite Forall_forall in H. apply H in H1 as Hpsx.
  constructor; try assumption. split; try assumption.
  apply state_union_incl_iterated. assumption.
Qed.

End Common_Futures.