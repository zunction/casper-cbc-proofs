Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.

Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.estimator.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.hash_function.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.hash_state.

Module Common_Futures
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PHash : Hash)
        (PHash_function : Hash_function PCons PVal PHash)
        (PEstimator : Estimator PCons PVal PVal_Weights PHash)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PHash.
Import PHash_function.
Import PEstimator.
Import PThreshold.

Module PProtocol_States := Protocol_States PCons PVal PVal_Weights 
                                           PHash PHash_function 
                                           PEstimator PThreshold.

Export PProtocol_States.


(** Two party common futures **)

Lemma union_protocol_2states : forall sigma1 sigma2,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  fault_tolerance_condition (state_union sigma1 sigma2) ->
  protocol_state (state_union sigma1 sigma2).
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - simpl. assumption.
  - clear IHHps2_1.
    assert (protocol_state (state_union sig1 (state_remove (c, v, hash_state j) sigma'))).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with (state_union sig1 sigma'); try assumption.
      intro msg; intro Hin.
      apply set_union_intro.
      unfold state_union in Hin; apply set_union_elim in Hin.
      destruct Hin; try (left; assumption).
      right. apply (set_remove_1 _ _ _ _ H4).
    }
    clear IHHps2_2.
     apply protocol_state_nodup in Hps1 as Hnodups1.
      assert (HnodupUs1s' := H1).
      apply (set_union_nodup message_eq_dec Hnodups1) in HnodupUs1s'.
      destruct (in_dec message_eq_dec (c, v, hash_state j) sig1).
    + apply set_eq_protocol_state with (state_union sig1 (state_remove (c, v, hash_state j) sigma'))
      ; try assumption.
      apply set_eq_remove_union_in; assumption.
    + apply (protocol_state_cons c v j); try assumption.
      * apply set_union_iff. right. assumption.
      * apply (set_remove_nodup message_eq_dec (c, v, hash_state j)) in HnodupUs1s' as Hnoduprem.
        apply set_eq_protocol_state with (state_union sig1 (state_remove (c, v, hash_state j) sigma'))
        ; try assumption.
        apply set_eq_remove_union_not_in; assumption.
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
  - split; constructor; try assumption; split; try apply union_protocol_2states; try assumption; intro msg; intros; apply set_union_intro.
    + left. assumption.
    + right. assumption.
Qed.

Lemma union_protocol_nstates : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  protocol_state (fold_right state_union state_empty sigmas).
Proof.
  induction sigmas; intros.
  - simpl. constructor.
  - inversion H; subst; clear H.
    simpl in H0. 
    apply (fault_tolerance_condition_subset (fold_right state_union state_empty sigmas)) in H0 as Hftc.
    + simpl. apply union_protocol_2states; try assumption. apply IHsigmas; try assumption.
    + apply set_union_incl_right.
Qed.

Theorem n_party_common_futures : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  exists sigma',
    protocol_state(sigma') /\
    Forall (fun sigma => sigma' in_Futures sigma) sigmas.
Proof.
  intros.
  exists (fold_right state_union state_empty sigmas).
  apply (union_protocol_nstates sigmas) in H0; try assumption.
  split; try assumption.
  apply Forall_forall; intros.
  rewrite Forall_forall in H. apply H in H1 as Hpsx.
  constructor; try assumption. split; try assumption.
  apply set_union_incl_iterated. assumption.
Qed.

End Common_Futures.