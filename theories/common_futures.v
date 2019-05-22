Require Import Coq.Reals.Reals.

Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.state_inclusion.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.sorted_union.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.preamble.

(** work in progress **)

(** Lemmas to prove

fault_weight_message_state_sorted_subset 

sorted_union_total [in sorted_union]
sorted_union_ac [in sorted_union]
sorted_union_locally_sorted [in sorted_union]
sorted_subset_transitive [in sorted_subset]

**)


Lemma fault_weight_message_state_sorted_subset : forall msg sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma' r2 ->
  (r1 <= r2)%R.
Admitted.

Lemma fault_weight_state_sorted_subset : forall sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros. 
  generalize dependent r1. generalize dependent r2.
  induction H; intros.
  + apply fault_weight_state_empty in H0; subst.
    apply fault_weight_state_nonnegative in H1. 
    assumption.
  + destruct (fault_weight_message_state_total msg sigma) as [r1' H2].
    destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H2) in H0.
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply (fault_weight_message_state_sorted_subset _ _ _ _ _ H H2) in H3.
    (* maybe this part can be proved easier *)
    apply (Rplus_le_compat_r r1' _ _) in H0.
    rewrite Rplusminus_assoc_r in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_r in H0.
    apply (Rplus_le_compat_l (Ropp r2') _ _) in H3.
    rewrite Rplus_opp_l in H3.
    rewrite Rplusminus_assoc_r in H0.
    apply (Rplus_ge_reg_neg_r r2 (Ropp r2' + r1') r1 H3) in H0 .
    assumption.
  + destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply fault_weight_message_state_nonnegative in H3.
    assert (H4 := Rminus_lt_r r2 r2' H3).
    apply (Rle_trans _ _ _ H0 H4).
Qed.

Lemma fault_weight_state_add : forall msg sigma sigma' r1 r2,
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  apply add_in_sorted_sorted_subset in H1; try assumption.
  apply (fault_weight_state_sorted_subset sigma sigma' r1 r2 H1 H2 H3).
Qed.

Lemma fault_tolerance_condition_backwards : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  destruct (fault_weight_state_total sigma') as [r' H4].
  assert (LTw := fault_weight_state_add msg sigma sigma' r r' H H0 H1 H3 H4).
  apply H2 in H4.
  apply (Rle_trans _ _ _ LTw H4).
Qed.

(** Two party common futures **)

Theorem two_party_common_futures : forall sigma1 sigma2 sigma,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  sorted_union sigma1 sigma2 sigma ->
  fault_tolerance_condition sigma ->
  protocol_state sigma.
Proof.
  intros sig1 sig2 sig H1. generalize dependent sig. generalize dependent sig2.
  induction H1; intros sig2 sig Hsig2 HUnion HFault.
  + apply union_state_empty_left in HUnion; subst; assumption.
  + assert (H3 := protocol_state_next c v sigma sigma' sigma'' H1_ H1_0 H H0 H1 H2).
    apply protocol_state_sorted in H1_0 as LS_sigma'.
    apply protocol_state_sorted in Hsig2 as LS_sig2.
    apply protocol_state_sorted in H1_ as LS_sigma.
    apply protocol_state_sorted in H3 as LS_sigma''.
    apply (locally_sorted_msg_justification c v sigma) in LS_sigma as LS_msg.
    destruct (sorted_union_total sigma' sig2) as [sigma2' HUnion2'].
    apply (sorted_union_ac _ _ _ _ _ _ LS_sigma' LS_sig2 LS_msg H1 HUnion) in HUnion2' as Hadd2'.
    apply protocol_state_next with c v sigma sigma2'; try assumption.
    * apply IHprotocol_state2 with sig2; try assumption.
      apply (sorted_union_locally_sorted _ _ _ HUnion2' LS_sigma') in LS_sig2 as LS_sigma2'.
      apply (sorted_union_locally_sorted _ _ _ HUnion LS_sigma'') in LS_sig2 as LS_sig.
      apply (fault_tolerance_condition_backwards _ _ _ LS_sigma2' LS_sig Hadd2' HFault).
    * apply sorted_union_subset_left in HUnion2' as Hsub2'; try assumption.
      apply sorted_union_locally_sorted in HUnion2'; try assumption.
      apply (sorted_subset_transitive _ _ _ LS_sigma LS_sigma' HUnion2' H Hsub2').
Qed.
