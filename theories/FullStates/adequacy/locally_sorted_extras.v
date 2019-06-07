Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.

Lemma in_sorted_state : forall sigma,
  locally_sorted sigma ->
   forall msg,
  in_state msg sigma ->
  locally_sorted_msg msg.
Proof.
  intros sigma H. induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - apply in_singleton_state in H0; subst. apply locally_sorted_message_justification. assumption.
  - rewrite in_state_iff in H2. destruct H2; subst.
    + apply locally_sorted_message_justification. assumption.
    + apply IHlocally_sorted2 ; assumption.
Qed.
