Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.state_inclusion.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.sorted_union.

(** work in progress **)

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

(* Previous Proof


rewrite add_is_next in *.
    inversion HUnion as 
      [ gamma U1 U2 UNext
      | gamma U1 U2 UNext
      | msg gamma1 gamma2 gamma' HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next U1 U2 UNext
      ]
    ; subst
    ; try assumption
    ; rewrite add_is_next in *
    ; apply no_confusion_next in UNext
    ; destruct UNext
    ; subst
    ; apply fault_tolerance_condition_backwards in HFault as HFault_next
    ; apply protocol_state_next_backwards_state in H2 as H2_next
    ; apply protocol_state_next_backwards_state in H1 as H1_next
    ; try apply protocol_state_next_backwards_justification in H2 as protocol_sj2
    ; try apply protocol_state_next_backwards_justification in H1 as protocol_sj1
    ; try apply protocol_state_sorted in protocol_sj1 as LS_sj1
    ; try apply protocol_state_sorted in protocol_sj2 as LS_sj2
    ; apply IHsigma1  in HUnion_next as H_sigma1 ; try assumption
    ; apply protocol_state_next with (sc) (sv) (sj) (sigma1); try assumption
    ; try (apply protocol_state_next_backwards_justification in H1 as H1_j;  assumption)
    ; try (apply protocol_state_next_backwards_justification in H2 as H2_J;  assumption)
    ; try unfold full_node_condition
    ; try assert (LS_gamma1 := protocol_state_sorted gamma1 H1_next)
    ; try assert (LS_gamma2 := protocol_state_sorted gamma2 H2_next)
    ; try assert (LS_nextgamma1 := protocol_state_sorted (next (sc, sv, sj) gamma1) H1)
    ; try assert (LS_nextgamma2 := protocol_state_sorted (next (sc, sv, sj) gamma2) H2)
    ; try assert (LS_nextmsg1gamma1 := protocol_state_sorted (next msg1 gamma1) H1)
    ; try assert (LS_nextmsg2gamma2 := protocol_state_sorted (next msg2 gamma2) H2)
    ; try apply protocol_state_next_backwards_valid_message in H1 as H1_valid
    ; try apply protocol_state_next_backwards_valid_message in H2 as H2_valid
    ; try apply protocol_state_sorted in H_sigma1
    ; try apply protocol_state_sorted in H_sigma2
    ; try assumption
    .
    (** case msg1 == msg2 **)
      * apply (sorted_union_subset_left gamma1 gamma2 sigma1 LS_gamma1 LS_gamma2) in HUnion_next.  
        apply protocol_state_next_inclusion in H1 as H1.
        apply (sorted_subset_transitive sj gamma1 sigma1 H1 HUnion_next LS_sj1 LS_gamma1 H_sigma1).
 
      * apply locally_sorted_next_message.
        apply (sorted_union_locally_sorted 
                (next (sc,sv,sj) gamma1) 
                (next (sc,sv,sj) gamma2) 
                (next (sc,sv,sj) sigma1) 
                HUnion LS_nextgamma1 LS_nextgamma2).

    (** case msg1 < msg2 **)
      * apply (sorted_union_subset_left gamma1 (next msg2 gamma2) sigma1 LS_gamma1 LS_nextmsg2gamma2) in HUnion_next.  
        apply protocol_state_next_inclusion in H1 as H1.
        apply (sorted_subset_transitive sj gamma1 sigma1 H1 HUnion_next LS_sj1 LS_gamma1 H_sigma1).

      * apply locally_sorted_next_message.
        apply (sorted_union_locally_sorted 
                (next (sc,sv,sj) gamma1) 
                (next msg2 gamma2) 
                (next (sc,sv,sj) sigma1) 
                HUnion LS_nextgamma1 LS_nextmsg2gamma2).

    (** case msg1 > msg2 **) 
      * apply (sorted_union_subset_right (next msg1 gamma1) gamma2 sigma1 LS_nextmsg1gamma1 LS_gamma2) in HUnion_next.
        apply protocol_state_next_inclusion in H2.
        apply (sorted_subset_transitive sj gamma2 sigma1 H2 HUnion_next LS_sj2 LS_gamma2 H_sigma1).

 
      * apply locally_sorted_next_message.
        apply (sorted_union_locally_sorted 
                (next msg1 gamma1) 
                (next (sc,sv,sj) gamma2) 
                (next (sc,sv,sj) sigma1) 
                HUnion LS_nextmsg1gamma1 LS_nextgamma2).
Qed.


(* 

Maybe needed for sorted_subset_transitive

Lemma sorted_subset_empty : forall sigma,
  locally_sorted sigma ->
  sigma => Empty -> 
  sigma = Empty.
Proof.
  intros.
  inversion H0
    ; subst
    ; try apply no_confusion_next_empty in H1
    ; try inversion H1
    .
  - reflexivity.
Qed.
*)

(*

Maybe needed for sorted_union_locally_sorted

Lemma sorted_union_all_messages : forall msg sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  in_state msg sigma ->
  (in_state msg sigma1 \/ in_state msg sigma2).
Admitted.
*)


*)
