Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.in_state.
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

Theorem sorted_union_in_state : forall sigma1 sigma2 sigma12,
  sorted_union sigma1 sigma2 sigma12 ->
  forall msg, in_state msg sigma12 <-> in_state msg sigma1 \/ in_state msg sigma2.
Proof.
  intros. 
  induction H as
    [ gamma
    | gamma
    | msg2 gamma1 gamma2 gamma' HUnion_next IHUnion
    | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next IHUnion
    | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next IHUnion
    ]
  ; split; intros
  ; try (inversion H; subst; clear H;
      apply no_confusion_next in H0; destruct H0; subst
      ; destruct H2
      ; subst 
      ; try (constructor; left; reflexivity))
  ; try (left; constructor; left; reflexivity)
  .
  - right. assumption.
  - destruct H.
    + exfalso. apply (in_empty_state _ H).
    + assumption.
  - left. assumption.
  - destruct H.
    + assumption.
    + exfalso. apply (in_empty_state _ H).
  - apply IHUnion in H; destruct H
    ; try (left ; constructor; right; assumption)
    ; right  ; constructor; right; assumption .
  - constructor.  rewrite IHUnion. 
    destruct H
    ; try (inversion H; subst; clear H;
      apply no_confusion_next in H0; destruct H0; subst
      ; destruct H2
      ; subst 
      ; try (left; reflexivity))
    .
    + right. left. assumption.
    + right. right. assumption.
  - apply IHUnion in H; destruct H.
    + left ; constructor; right; assumption.
    + right; assumption .
  - constructor.
    destruct H
    ; inversion H; subst; clear H
    ; apply no_confusion_next in H0; destruct H0; subst
    ; destruct H2
    ; subst 
    ; try (left; reflexivity)
    ; rewrite IHUnion
    .
    + right; left; assumption.
    + right; right; constructor; left; reflexivity.
    + right; right; constructor; right; assumption.
  - right; constructor; left; reflexivity.
  - apply IHUnion in H. destruct H.
    +  left; assumption.
    + right; constructor; right; assumption.
  - constructor. rewrite IHUnion.
    destruct H.
    + right; left; assumption.
    + inversion H; subst; clear H
      ; apply no_confusion_next in H0; destruct H0; subst
      ; destruct H2
      ; subst 
      ; try (left; reflexivity)
      .
      right. right. assumption.
Qed.

Lemma sorted_union_idempotent : forall sigma,
  sorted_union sigma sigma sigma.
Proof.
  induction sigma.
  - constructor.
  - rewrite add_is_next in *. apply Sorted_union_Next_eq. assumption.
Qed.

Lemma sorted_union_commutative : forall sigma1 sigma2 sigma3,
  sorted_union sigma1 sigma2 sigma3 -> sorted_union sigma2 sigma1 sigma3.
Proof.
  intros.
  induction H as
    [ gamma
    | gamma
    | msg2 gamma1 gamma2 gamma' HUnion_next IHUnion
    | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next IHUnion
    | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next IHUnion
    ]
  .
  - constructor.
  - constructor.
  - constructor. assumption.
  - apply Sorted_union_Next_gt; assumption.
  - apply Sorted_union_Next_lt; assumption.
Qed.

Lemma sorted_union_subset_left : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sigma1 => sigma.
Proof.
  intros sigma1 sigma2 sigma HUnion.
  induction HUnion
    ; try (constructor; assumption)
  .
  - apply sorted_subset_reflexive.
Qed.

Corollary sorted_union_subset_right : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sigma2 => sigma.
Proof.
  intros. apply sorted_union_commutative in H.
  apply sorted_union_subset_left with sigma1; assumption.
Qed.

Lemma sorted_union_empty_left : forall sigma1 sigma2,
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

Corollary sorted_union_empty_right : forall sigma1 sigma2,
  sorted_union sigma1 Empty sigma2 -> sigma1 = sigma2.
Proof.
  intros.
  apply sorted_union_commutative in H. apply sorted_union_empty_left. assumption.
Qed.

Lemma sorted_union_singleton : forall msg sigma1 sigma2,
  add_in_sorted msg sigma1 sigma2 <-> sorted_union (next msg Empty) sigma1 sigma2.
Proof.
  intros msg sigma1.
  induction sigma1.
  - intros; split; intros.
    + apply add_in_empty in H; subst. constructor.
    + inversion H as
        [ gamma U1 U2 UNext
        | gamma U1 U2 UNext
        | msg1 gamma1 gamma2 gamma' HUnion_next U1 U2 UNext
        | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next U1 U2 UNext
        | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next U1 U2 UNext
        ]
      ; subst
      ; try (apply no_confusion_next in U1; destruct U1; subst)
      ; try (exfalso; apply (no_confusion_next_empty _ _ U2))
      .
      * exfalso. symmetry in U1. apply (no_confusion_next_empty _ _ U1).
      * constructor.
  - clear IHsigma1_1. rename sigma1_1 into j.
    rename sigma1_2 into sigma1. rename IHsigma1_2 into IHsigma1. 
    rewrite add_is_next in *.
    intros; split; intros.
    + inversion H as 
        [ msga Umsg UEmpty Usingleton
        | msga sigmaA Umsg UNext UNext'
        | msga msga' sigmaA LTA Umsg UNext UNext'
        | msga msga' sigmaA sigmaA' LTA AddA' Umsg UNext UNext']
      ; clear H; subst
      ; rewrite add_is_next in *
      ; try (apply no_confusion_next in UNext; destruct UNext; subst)
      ; try (apply no_confusion_next in UNext'; destruct UNext'; subst)
      .
      * constructor. constructor.
      * constructor; try assumption. constructor.
      * constructor; try assumption. apply IHsigma1. assumption.
    + inversion H as
        [ gamma U1 U2 UNext
        | gamma U1 U2 UNext
        | msg1 gamma1 gamma2 gamma' HUnion_next U1 U2 UNext
        | msg1 gamma1 msg2 gamma2 gamma' LT HUnion_next U1 U2 UNext
        | msg1 gamma1 msg2 gamma2 gamma' GT HUnion_next U1 U2 UNext
        ]
      ; subst
      ; try rewrite add_is_next in *
      ; try (apply no_confusion_next in U1; destruct U1; subst)
      ; try (apply no_confusion_next in U2; destruct U2; subst)
      .
      * exfalso. symmetry in U1. apply (no_confusion_next_empty _ _ U1).
      * apply sorted_union_empty_left in HUnion_next; subst.
        constructor.
      * apply sorted_union_empty_left in HUnion_next; subst.
        apply add_in_Next_lt. assumption.
      * apply IHsigma1 in HUnion_next.
        apply add_in_Next_gt; assumption.
Qed.


Lemma sorted_union_assoc : forall sigma1 sigma2 sigma3 sigma12 sigma23 sigma123,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma3 ->
  sorted_union sigma1 sigma2 sigma12 ->
  sorted_union sigma12 sigma3 sigma123 ->
  sorted_union sigma2 sigma3 sigma23 ->
  sorted_union sigma1 sigma23 sigma123.
  Admitted.

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
Proof.
  induction sigma1.
  - intros. exists sigma2. constructor.
  - clear IHsigma1_1. rename sigma1_1 into j. rename sigma1_2 into sigma1. rename IHsigma1_2 into IHsigma1.
    intros. destruct sigma2; repeat rewrite add_is_next in *.
    + exists (next (c, v, j) sigma1). constructor.
    +  
  Admitted.


Lemma next_sorted_union_ind_left : forall msg1 msg2 gamma1 gamma2 gamma',
    locally_sorted (next msg1 gamma1) ->
    locally_sorted (next msg2 gamma2) ->
    msg_lt msg1 msg2 ->
    sorted_union gamma1 (next msg2 gamma2) gamma' ->
    locally_sorted gamma' ->
    locally_sorted (next msg1 gamma').
Proof.
  intros msg1 msg2 gamma1 gamma2 gamma' H H0 LT HUnion_next LSgamma'.
  apply locally_sorted_msg_characterization in H.
  destruct H as 
    [ Hcempty
    | [[cmsg0 [LScmsg0 Hcnext]]
    | [cmsg1 [cmsg2 [csigma' [Hcnext [LScnext [LScmsg1 LTc]]]]]]
    ]]; subst
  ; try (apply no_confusion_next in Hcnext; destruct Hcnext; subst)
  .
  + exfalso. apply (no_confusion_next_empty _ _ Hcempty).
  + apply sorted_union_empty_left in HUnion_next; subst. 
    apply add_in_sorted_sorted with cmsg0 (next msg2 gamma2); try assumption.
    apply add_in_Next_lt. assumption.
  + inversion HUnion_next as
      [ gamma Uempty Ugamma UNext
      | gamma Ugamma Uempty UNext
      | msg1 gamma1 gamma2n gamman' HUnion_nextn Unext1 Unext2 UNext'
      | msg1 gamma1 msg2n gamma2n gamman' LTn HUnion_nextn Unext1 Unext2 UNext'
      | msg1 gamma1 msg2n gamma2n gamman' GTn HUnion_nextn Unext1 Unext2 UNext'
      ]
    ; subst
    ; try (exfalso; symmetry in Uempty; apply (no_confusion_next_empty _ _ Uempty))
    ; apply no_confusion_next in Unext1; destruct Unext1; subst
    ; apply no_confusion_next in Unext2; destruct Unext2; subst
    ; apply locally_sorted_msg_characterization; right; right
    .
    * exists cmsg1. exists msg2. exists gamman'.
      split; try reflexivity. repeat (split; try assumption).
    * exists cmsg1. exists cmsg2. exists gamman'.
      split; try reflexivity. repeat (split; try assumption).
    * exists cmsg1. exists msg2. exists gamman'.
      split; try reflexivity. repeat (split; try assumption).
Qed.

Theorem sorted_union_locally_sorted : forall sigma1 sigma2 sigma,
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
  - apply locally_sorted_msg_characterization in H.
    destruct H as 
      [ Hcempty
      | [[cmsg0 [LScmsg0 Hcnext]]
      | [cmsg1 [cmsg2 [csigma' [Hcnext [LScnext [LScmsg1 LTc]]]]]]
      ]]; subst
    ; try (apply no_confusion_next in Hcnext; destruct Hcnext; subst)
    .
    + exfalso. apply (no_confusion_next_empty _ _ Hcempty).
    + apply sorted_union_empty_left in HUnion_next; subst. assumption.
    + apply sorted_union_commutative in HUnion_next.
      apply next_sorted_union_ind_left with cmsg2 gamma2 csigma'; try assumption.
      apply IHHUnion_next; try assumption.
      apply (locally_sorted_tail _ _ H0).
  - apply next_sorted_union_ind_left with msg2 gamma1 gamma2; try assumption.
    apply locally_sorted_tail in H.
    apply IHHUnion_next; assumption.
  - apply sorted_union_commutative in HUnion_next.
    apply next_sorted_union_ind_left with msg1 gamma2 gamma1; try assumption.
    apply locally_sorted_tail in H0.
    apply IHHUnion_next; assumption.
Qed.
