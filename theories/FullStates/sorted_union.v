Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.sorted_subset.

(******************************)
(** Union of (sorted) states **)
(******************************)

Inductive sorted_union : state -> state -> state -> Prop :=
  | Sorted_union_Empty_left : forall sigma, sorted_union Empty sigma sigma
  | Sorted_union_Empty_right : forall sigma, sorted_union sigma Empty sigma
  | Sorted_union_Next_eq : forall msg sigma1 sigma2 sigma',
      sorted_union sigma1 sigma2 sigma' ->
      sorted_union (next msg sigma1) (next msg sigma2) (next msg sigma')
  | Sorted_union_Next_lt : forall msg1 sigma1 msg2 sigma2 sigma',
      msg_lt msg1 msg2 ->
      sorted_union sigma1 (next msg2 sigma2) sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg1 sigma')
  | Sorted_union_Next_gt : forall msg1 sigma1 msg2 sigma2 sigma',
      msg_lt msg2 msg1 ->
      sorted_union (next msg1 sigma1) sigma2 sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg2 sigma')
  .

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
  - apply locally_sorted_tail in LocS_sigma1.
    apply locally_sorted_tail in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_tail in LocS_sigma1.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_tail in LocS_sigma2.
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
  - apply locally_sorted_tail in LocS_sigma1.
    apply locally_sorted_tail in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_tail in LocS_sigma1.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
  - apply locally_sorted_tail in LocS_sigma2.
    apply (IHHUnion LocS_sigma1 LocS_sigma2).
Qed.

(*

I don't think these are needed anymore
*)

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


(* (sigma1 \cup { m }) \cup sigma2 = (sigma1 \cup sigma2) \cup { m } *) 
Lemma sorted_union_ac : forall msg sigma1 sigma2 sigma1' sigma sigma',
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted_msg msg ->
  add_in_sorted msg sigma1 sigma1' ->
  sorted_union sigma1' sigma2 sigma' ->
  sorted_union sigma1 sigma2 sigma ->
  add_in_sorted msg sigma sigma'.
  Admitted.

Lemma sorted_union_total : forall sigma1 sigma2,
  exists sigma, sorted_union sigma1 sigma2 sigma.
  Admitted.
  

