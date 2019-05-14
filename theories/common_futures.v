From Casper
Require Import full_version.

(** work in progress **)

Lemma protocol_state_next_backwards_justification : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  protocol_state j.
Admitted.

Lemma union_state_empty_left : forall sigma1 sigma2,
  sorted_union Empty sigma1 sigma2 -> sigma1 = sigma2.
Proof.
  intros.
  inversion H; try (subst; reflexivity).
  - destruct msg as [(c,v) j]. unfold next in H0.
    inversion H0.
  - destruct msg1 as [(c,v) j]. unfold next in H0.
    inversion H0.
  - destruct msg1 as [(c,v) j]. unfold next in H0.
    inversion H0.
Qed.

Lemma union_state_empty_right : forall sigma1 sigma2,
  sorted_union sigma1 Empty sigma2 -> sigma1 = sigma2.
Proof.
  intros.
  inversion H; try (subst; reflexivity).
  - destruct msg as [(c,v) j]. unfold next in H0.
    inversion H0.
  - destruct msg2 as [(c,v) j]. unfold next in H0.
    inversion H0.
  - destruct msg2 as [(c,v) j]. unfold next in H0.
    inversion H0.
Qed.

Lemma next_equal : forall msg1 msg2 state1 state2,
  next msg1 state1 = next msg2 state2 ->
  (msg1 = msg2 /\ state1 = state2).
Admitted.

Lemma sorted_union_noduplicates_left: forall msg sigma1 sigma2 sigma,
  sorted_union (next msg sigma1) (next msg sigma2) (next msg sigma) ->
  sorted_union sigma1 (next msg sigma2) (next msg sigma).
Admitted.

Lemma protocol_state_next_backwards_state : forall msg sigma,
  protocol_state (next msg sigma) -> protocol_state sigma.
Admitted.


Lemma protocol_state_next_backwards_valid_message : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  valid_msg_condition c j.
Admitted.

Lemma protocol_state_next_inclusion : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  j => sigma.
Admitted.

Lemma fault_tolerance_condition_backwards: forall msg sigma,
  fault_tolerance_condition (next msg sigma) ->
  fault_tolerance_condition sigma.
Admitted.

Lemma sorted_union_subset_left : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sigma1 => sigma.
Admitted.

Lemma sorted_union_subset_right : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sigma2 => sigma.
Admitted.

Lemma sorted_subset_transitive : forall sigma1 sigma2 sigma3,
  sigma1 => sigma2 ->
  sigma2 => sigma3 ->
  sigma1 => sigma3.
Admitted. 

Lemma sorted_union_first_eq : forall msg sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sorted_union (next msg sigma1) (next msg sigma2) (next msg sigma) ->
  add_in_sorted msg sigma (next msg sigma).
Admitted.

Lemma sorted_union_first_lt : forall msg1 msg2 sigma1 sigma2 sigma,
  msg_lt msg1 msg2 ->
  sorted_union sigma1 (next msg2 sigma2) sigma ->
  sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg1 sigma) ->
  add_in_sorted msg1 sigma (next msg1 sigma).
Admitted.

Lemma sorted_union_first_gt : forall msg1 msg2 sigma1 sigma2 sigma,
  msg_lt msg2 msg1 ->
  sorted_union (next msg1 sigma1) sigma2 sigma ->
  sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg2 sigma) ->
  add_in_sorted msg2 sigma (next msg2 sigma).
Admitted.


(** TODO: try to compress the cases for the induction step **)
Theorem two_party_common_futures : forall sigma1 sigma2 sigma,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  sorted_union sigma1 sigma2 sigma ->
  fault_tolerance_condition sigma ->
  protocol_state sigma.
Proof.
  intros sigma1 sigma2 sigma H1 H2 HUnion HFault.
  generalize dependent sigma1.
  generalize dependent sigma2.
  induction sigma as [ | sc sv sj _]; try intros.
  + constructor.
  + rewrite add_is_next in *.
    inversion HUnion; subst; 
    try (assumption || 
         rewrite add_is_next in H; apply next_equal in H; destruct H; subst).
    (** case msg1 = msg2 **)
    - apply protocol_state_next_backwards_state in H2 as H2_next.
      apply protocol_state_next_backwards_state in H1 as H1_next.
      apply fault_tolerance_condition_backwards in HFault as HFault_next.
      apply IHsigma1 with (sigma4) (sigma3) in HFault_next as H_sigma1; try assumption.
      apply protocol_state_next with (sc) (sv) (sj) (sigma1); try assumption.
      * apply protocol_state_next_backwards_justification in H1. assumption.
      * unfold full_node_condition.
        apply protocol_state_next_inclusion in H1.
        apply sorted_union_subset_left in H4.
        apply (sorted_subset_transitive sj sigma3 sigma1 H1 H4).
      * apply protocol_state_next_backwards_valid_message in H1. assumption.
      * apply (sorted_union_first_eq (sc, sv, sj) sigma3 sigma4 sigma1 H4 HUnion).
    (** case msg1 < msg2 **)
    - apply protocol_state_next_backwards_state in H1 as H1_next.
      apply fault_tolerance_condition_backwards in HFault as HFault_next.
      apply IHsigma1 with (next msg2 sigma4) (sigma3) in HFault_next as H_sigma1; try assumption.
      apply protocol_state_next with (sc) (sv) (sj) (sigma1); try assumption.
      * apply protocol_state_next_backwards_justification in H1. assumption.
      * unfold full_node_condition.
        apply protocol_state_next_inclusion in H1.
        apply sorted_union_subset_left in H5.
        apply (sorted_subset_transitive sj sigma3 sigma1 H1 H5).
      * apply protocol_state_next_backwards_valid_message in H1. assumption.
      * apply (sorted_union_first_lt (sc, sv, sj) msg2 sigma3 sigma4 sigma1 H0 H5 HUnion).
     (** case msg1 > msg2 **)
    - apply protocol_state_next_backwards_state in H2 as H2_next.
      apply fault_tolerance_condition_backwards in HFault as HFault_next.
      apply IHsigma1 with (sigma4) (next msg1 sigma3) in HFault_next as H_sigma1; try assumption.
      apply protocol_state_next with (sc) (sv) (sj) (sigma1); try assumption.
      * apply protocol_state_next_backwards_justification in H2. assumption.
      * unfold full_node_condition.
        apply protocol_state_next_inclusion in H2.
        apply sorted_union_subset_right in H5.
        apply (sorted_subset_transitive sj sigma4 sigma1 H2 H5).
      * apply protocol_state_next_backwards_valid_message in H2. assumption.
      * apply (sorted_union_first_gt msg1 (sc, sv, sj) sigma3 sigma4 sigma1 H0 H5 HUnion).
Qed.

