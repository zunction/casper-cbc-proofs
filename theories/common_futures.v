Require Import Coq.Reals.Reals.

Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.sorted_subset. 
Require Import Casper.FullStates.sorted_union.
Require Import Casper.FullStates.fault_weights.

(** work in progress **)

(** Lemmas to prove

sorted_union_total [in sorted_union]
sorted_union_ac [in sorted_union]
sorted_union_locally_sorted [in sorted_union]
sorted_subset_transitive [in sorted_subset]

**)


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

