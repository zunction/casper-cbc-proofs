From Casper
Require Import full_version.

(** work in progress **)

Lemma locally_sorted_next_backwards : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted sigma.
Proof.
  intros.
  inversion H
    ; subst
    ; try rewrite add_is_next in *
    ; try apply no_confusion_next in H0
    ; try destruct H0; subst
    .
  - symmetry in H1. apply no_confusion_next_empty in H1. inversion H1.
  - constructor.
  - assumption.
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

Lemma sorted_subset_transitive : forall sigma1 sigma2 sigma3,
  sigma1 => sigma2 ->
  sigma2 => sigma3 ->
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma3 ->
  sigma1 => sigma3.
Admitted.

(*

Maybe needed for sorted_union_locally_sorted

Lemma sorted_union_all_messages : forall msg sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  in_state msg sigma ->
  (in_state msg sigma1 \/ in_state msg sigma2).
Admitted.
*)

Lemma sorted_union_locally_sorted : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma.
Proof.
  intros sigma1 sigma2 sigma HUnion.
  induction HUnion as 
      [ gamma
      | gamma
      | msg gamma1 gamma2 gamma' HUnion_next
      | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next
      | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next
      ]
  ; intros
  ; try assumption
  .
  Admitted.

Corollary sorted_subset_reflexive : forall sigma, 
  locally_sorted sigma ->
  sorted_subset sigma sigma.
Proof.
  intros.
  apply sorted_subset_inclusion; try assumption.
  apply state_inclusion_reflexive.
Qed.


Lemma sorted_union_subset_left : forall sigma1 sigma2 sigma,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_union sigma1 sigma2 sigma ->
  sigma1 => sigma.
Proof.
  intros sigma1 sigma2 sigma LocS_sigma1 LocS_sigma2 HUnion.
  induction HUnion
    ; try constructor
  .
  - apply sorted_subset_reflexive. assumption.
  - apply locally_sorted_next_backwards in LocS_sigma1.
    apply locally_sorted_next_backwards in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_next_backwards in LocS_sigma1.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_next_backwards in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
Qed.


Lemma sorted_union_subset_right : forall sigma1 sigma2 sigma,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_union sigma1 sigma2 sigma ->
  sigma2 => sigma.
Proof.
  intros sigma1 sigma2 sigma LocS_sigma1 LocS_sigma2 HUnion.
  induction HUnion
    ; try constructor
  .
  - apply sorted_subset_reflexive. assumption.
  - apply locally_sorted_next_backwards in LocS_sigma1.
    apply locally_sorted_next_backwards in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_next_backwards in LocS_sigma1.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_next_backwards in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
Qed.

(*

I don't think these are needed anymore

Lemma union_state_empty_left : forall sigma1 sigma2,
  sorted_union Empty sigma1 sigma2 -> sigma1 = sigma2.
Proof.
  intros sigma1 sigma2 HUnion.
  inversion HUnion as
     [ gamma U1 U2 UNext
      | gamma U1 U2 UNext
      | msg1 gamma1 gamma2 gamma' HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next U1 U2 UNext
      ]
  ; subst 
  ; try reflexivity 
  ; destruct msg1 as [(c,v) j]
  ; unfold next in U1
  ; inversion U1.
Qed.

Lemma union_state_empty_right : forall sigma1 sigma2,
  sorted_union sigma1 Empty sigma2 -> sigma1 = sigma2.
Proof.
  intros sigma1 sigma2 HUnion.
  inversion HUnion as
     [ gamma U1 U2 UNext
      | gamma U1 U2 UNext
      | msg2 gamma1 gamma2 gamma' HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next U1 U2 UNext
      | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next U1 U2 UNext
      ]
  ; subst 
  ; try reflexivity 
  ; destruct msg2 as [(c,v) j]
  ; unfold next in U2
  ; inversion U2.
Qed.
*)

Lemma locally_sorted_next_message : forall msg sigma,
  locally_sorted (next msg sigma) ->
  add_in_sorted msg sigma (next msg sigma).
Proof.
  intros.
  inversion H as
    [ M 
    | c v j Hj M 
    | c v j msg' gamma Hj LT LocS M 
    ]
   ; subst
   ; try ( rewrite add_is_next in *
         ; apply no_confusion_next in M
         ; destruct M; subst
         ; constructor
         ; assumption
         )
   .
  - destruct msg as [(sc, sv) sj].
    rewrite <- add_is_next in M. inversion M.
Qed.


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
