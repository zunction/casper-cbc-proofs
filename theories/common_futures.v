Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.state_inclusion.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.sorted_union.

(** work in progress **)

(** Lemmas to prove

sorted_union_total [in sorted_union]
sorted_union_ac [in sorted_union]
fault_tolerance_condition_backwards [in common_futures]
sorted_union_locally_sorted [in sorted_union]
sorted_subset_transitive [in sorted_subset]

**)

Lemma fault_tolerance_condition_backwards: forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Admitted.

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
  + clear IHprotocol_state1.
    apply protocol_state_sorted in H1_0 as LS_sigma'.
    apply protocol_state_sorted in Hsig2 as LS_sig2.
    apply protocol_state_sorted in H1_ as LS_sigma.
    apply (locally_sorted_msg_justification c v sigma) in LS_sigma as LS_msg.
    destruct (sorted_union_total sigma' sig2) as [sigma2' HUnion2'].
    apply (sorted_union_ac _ _ _ _ _ _ LS_sigma' LS_sig2 LS_msg H1 HUnion) in HUnion2' as Hadd2'.
    apply protocol_state_next with c v sigma sigma2'; try assumption.
    * apply IHprotocol_state2 with sig2; try assumption.
      apply (fault_tolerance_condition_backwards _ _ _ Hadd2' HFault).
    * apply sorted_union_subset_left in HUnion2' as Hsub2'; try assumption.
      apply sorted_union_locally_sorted in HUnion2'; try assumption.
      apply (sorted_subset_transitive _ _ _ LS_sigma LS_sigma' HUnion2' H Hsub2').
Qed.
