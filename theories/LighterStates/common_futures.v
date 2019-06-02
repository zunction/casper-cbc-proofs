Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.

Require Import Casper.ListSetExtras.

Require Import Casper.LighterStates.messages.
Require Import Casper.LighterStates.states.
Require Import Casper.LighterStates.protocol_states.

Require Import Casper.LighterStates.fault_weights.



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
    assert (protocol_state (state_union sig1 (state_remove (c, v, hash_state.hash_state sigma) sigma'))).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with (state_union sig1 sigma'); try assumption.
      intro msg; intro Hin.
      apply set_union_intro.
      unfold state_union in Hin; apply set_union_elim in Hin.
      destruct Hin; try (left; assumption).
      right. apply (set_remove_1 _ _ _ _ H4).
    }
    clear IHHps2_2.
    inversion H4; subst.
    + symmetry in H6. unfold state_union in H6.  apply set_union_empty in H6.
      destruct H6; subst. apply set_eq_protocol_state with (state_union sigma' nil).
      * simpl. apply (protocol_state_cons c v sigma); assumption.
      * apply set_union_comm.
      * apply set_union_nodup; try constructor. assumption.
    + { destruct (message_eq_dec (c0, v0, hash_state.hash_state sigma0) (c, v, hash_state.hash_state sigma)).
      - inversion e; subst; clear e.
        apply (protocol_state_cons c v sigma); try assumption.
      + apply set_union_intro. right. assumption.
      + apply set_eq_protocol_state with (state_remove (c, v, hash_state.hash_state sigma0)
          (state_union sig1
             (state_remove (c, v, hash_state.hash_state sigma) sigma'))); try assumption.
  Admitted.

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

Theorem union_protocol_nstates : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  protocol_state (fold_right state_union state_empty sigmas).
Proof.
  induction sigmas; intros.
  - simpl. constructor.
  - inversion H; subst; clear H.
    simpl in H0.
  Admitted.
(* TODO: Maybe introduce a definition for the "fun" below *)

Theorem n_party_common_futures : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union state_empty sigmas) ->
  exists sigma',
    protocol_state(sigma') /\
    Forall (fun sigma => sigma' in_Futures sigma) sigmas.  (* P(sigma) ::= sigma => sigma' *)
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
