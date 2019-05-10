From Casper
Require Import full_version.

(** work in progress **)
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

Lemma protocol_state_backwards : forall msg sigma,
  protocol_state (next msg sigma) -> protocol_state sigma.
Admitted.

Lemma protocol_state_next : forall msg sigma,
  protocol_state sigma ->
  fault_tolerance_condition (next msg sigma) ->
  protocol_state (next msg sigma).
Admitted.

Lemma fault_tolerance_condition_backwards: forall msg sigma,
  fault_tolerance_condition (next msg sigma) ->
  fault_tolerance_condition sigma.
Admitted.

Lemma next_equal : forall msg1 msg2 state1 state2,
  next msg1 state1 = next msg2 state2 ->
  (msg1 = msg2 /\ state1 = state2).
Admitted.

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
  - constructor.
  - rewrite add_is_next in *.
    apply protocol_state_next; try assumption.
    inversion HUnion; subst.
    + apply protocol_state_backwards in H2. assumption.
    + apply protocol_state_backwards in H1. assumption.
    + rewrite add_is_next in H.
      apply fault_tolerance_condition_backwards in HFault.
      apply protocol_state_backwards in H1.
      apply protocol_state_backwards in H2.
      apply (IHsigma1 HFault sigma4 H2 sigma3 H1).
      apply next_equal in H. destruct H; subst.
      assumption.
    + Admitted.
