From Casper
Require Import full_version.

(** work in progress **)

Lemma locally_sorted_next_message : forall msg sigma,
  locally_sorted (next msg sigma) ->
  add_in_sorted msg sigma (next msg sigma).
Admitted.

Lemma sorted_union_locally_sorted : forall sigma1 sigma2 sigma,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_union sigma1 sigma2 sigma ->
  locally_sorted sigma.
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

(** Protocol state properties **)

Lemma protocol_state_next_inclusion : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  j => sigma.
Admitted.

Lemma protocol_state_next_backwards_state : forall msg sigma,
  protocol_state (next msg sigma) -> 
  protocol_state sigma.
Admitted.

Lemma protocol_state_next_backwards_justification : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  protocol_state j.
Admitted.

Lemma protocol_state_next_backwards_valid_message : forall c v j sigma,
  protocol_state (next (c,v,j) sigma) ->
  valid_msg_condition c j.
Admitted.

Lemma fault_tolerance_condition_backwards: forall msg sigma,
  fault_tolerance_condition (next msg sigma) ->
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
  intros sigma1 sigma2 sigma H1 H2 HUnion HFault.
  generalize dependent sigma1.
  generalize dependent sigma2.
  induction sigma as [ | sc sv sj _]; try intros.
  + constructor.
  + rewrite add_is_next in *.
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
    ; apply next_equal in UNext
    ; destruct UNext
    ; subst
    ; apply fault_tolerance_condition_backwards in HFault as HFault_next
    ; apply protocol_state_next_backwards_state in H2 as H2_next
    ; apply protocol_state_next_backwards_state in H1 as H1_next
    ; apply IHsigma1  in HUnion_next as H_sigma1 ; try assumption
    ; apply protocol_state_next with (sc) (sv) (sj) (sigma1); try assumption
    ; try (apply protocol_state_next_backwards_justification in H1 as H1_j;  assumption)
    ; try (apply protocol_state_next_backwards_justification in H2 as H2_J;  assumption)
    ; try unfold full_node_condition
    ; try (
        apply sorted_union_subset_left in HUnion_next
      ; apply protocol_state_next_inclusion in H1 as H1
      ; apply (sorted_subset_transitive sj gamma1 sigma1 H1 HUnion_next)
      )
    ; try (
        apply sorted_union_subset_right in HUnion_next
      ; apply protocol_state_next_inclusion in H2
      ; apply (sorted_subset_transitive sj gamma2 sigma1 H2 HUnion_next)
      )
    ; try apply protocol_state_next_backwards_valid_message in H1 as H1_valid
    ; try apply protocol_state_next_backwards_valid_message in H2 as H2_valid
    ; try assumption
    ; apply locally_sorted_next_message
    ; apply protocol_state_sorted in H1
    ; apply protocol_state_sorted in H2
    . 
    (** case msg1 == msg2 **)
      * apply (sorted_union_locally_sorted 
                (next (sc,sv,sj) gamma1) 
                (next (sc,sv,sj) gamma2) 
                (next (sc,sv,sj) sigma1) 
                H1 H2 HUnion).
    (** case msg1 < msg2 **)
      * apply (sorted_union_locally_sorted 
                (next (sc,sv,sj) gamma1) 
                (next msg2 gamma2) 
                (next (sc,sv,sj) sigma1) 
                H1 H2 HUnion).
    (** case msg1 > msg2 **)
      * apply (sorted_union_locally_sorted 
                (next msg1 gamma1) 
                (next (sc,sv,sj) gamma2) 
                (next (sc,sv,sj) sigma1) 
                H1 H2 HUnion).
Qed.

