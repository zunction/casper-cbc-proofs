Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.syntactic_state_inclusion.
Require Import Casper.FullStates.syntactic_state_union.

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
      message_lt msg1 msg2 ->
      sorted_union sigma1 (next msg2 sigma2) sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg1 sigma')
  | Sorted_union_Next_gt : forall msg1 sigma1 msg2 sigma2 sigma',
      message_lt msg2 msg1 ->
      sorted_union (next msg1 sigma1) sigma2 sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg2 sigma')
  .

Lemma sorted_union_to_syntactic_state_union : forall sigma1 sigma2 sigma12,
  sorted_union sigma1 sigma2 sigma12 ->
  syntactic_state_union sigma1 sigma2 sigma12.
Proof.
  intros. unfold syntactic_state_union.
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
  sigma in_Futures sigma1.
Proof.
  intros sigma1 sigma2 sigma HUnion.
  induction HUnion
    ; try (constructor; assumption)
  .
  - apply sorted_subset_reflexive.
Qed.

Corollary sorted_union_subset_right : forall sigma1 sigma2 sigma,
  sorted_union sigma1 sigma2 sigma ->
  sigma in_Futures sigma2.
Proof.
  intros. apply sorted_union_commutative in H.
  apply sorted_union_subset_left with sigma1; assumption.
Qed.


Lemma sorted_union_subset : forall sigmas sigma,
  reduce_rel sorted_union sigmas sigma ->
  Forall (Reachable sigma) sigmas.
Proof.
  intros. destruct sigmas.
  - inversion H.
  - unfold reduce_rel in H. constructor.
    + generalize dependent sigma. induction sigmas; intros; inversion H; clear H; subst
      ; try apply sorted_subset_reflexive.
      apply IHsigmas in H2.
      apply sorted_union_subset_right in H4.
      unfold Reachable in *.
      apply (sorted_subset_transitive s fl sigma); assumption.
    + generalize dependent sigma. induction sigmas; intros; inversion H; clear H; subst; try constructor.
      * apply sorted_union_subset_left in H4. apply H4.
      * apply IHsigmas in H2.
        apply (Forall_impl (Reachable sigma)) in H2; try assumption.
        intros.
        apply sorted_union_subset_right in H4.
        unfold Reachable in *.
        apply (sorted_subset_transitive a0 fl sigma); assumption.
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

Lemma next_sorted_union_ind_left : forall msg1 msg2 gamma1 gamma2 gamma',
    locally_sorted (next msg1 gamma1) ->
    locally_sorted (next msg2 gamma2) ->
    message_lt msg1 msg2 ->
    sorted_union gamma1 (next msg2 gamma2) gamma' ->
    locally_sorted gamma' ->
    locally_sorted (next msg1 gamma').
Proof.
  intros msg1 msg2 gamma1 gamma2 gamma' H H0 LT HUnion_next LSgamma'.
  apply locally_sorted_message_characterization in H.
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
    ; apply locally_sorted_message_characterization; right; right
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
  - apply locally_sorted_message_characterization in H.
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


Theorem sorted_union_locally_sorted_iterated : forall sigma sigmas sigma',
  Forall locally_sorted (sigma :: sigmas) ->
  fold_rel sorted_union sigma sigmas sigma' ->
  locally_sorted sigma'.
Proof.
  intros.  
  generalize dependent sigma'. induction sigmas; intros; inversion H0; subst; clear H0 .
  + apply Forall_inv in H. assumption.
  + inversion H; subst. inversion H4; subst.
    apply IHsigmas in H3 as LSfa.
    * apply (sorted_union_locally_sorted a fl sigma'); try assumption.
    * constructor; assumption.
Qed.

Lemma syntactic_state_union_to_sorted_union : forall sigma1 sigma2 sigma12,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma12 ->
  syntactic_state_union sigma1 sigma2 sigma12 ->
  sorted_union sigma1 sigma2 sigma12.
Proof.
  intros sigma1 sigma2 sigma12.
  generalize dependent sigma2. generalize dependent sigma1.
  induction sigma12
  ; intros sigma1 sigma2 H H0 LS12; intros
  ; repeat rewrite add_is_next in *.
  - destruct sigma1; destruct sigma2; repeat rewrite add_is_next in *.
    + constructor.
    + exfalso. apply (in_empty_state (c, v, sigma2_1)).
      apply H1. right; constructor; left; reflexivity.
    + exfalso. apply (in_empty_state (c, v, sigma1_1)).
      apply H1. left; constructor; left; reflexivity.
    + exfalso. apply (in_empty_state (c, v, sigma1_1)).
      apply H1. left; constructor; left; reflexivity.
  - clear IHsigma12_1. rename sigma12_1 into j.
    rename sigma12_2 into sigma12. rename IHsigma12_2 into IHsigma12.
    destruct sigma1; destruct sigma2; repeat rewrite add_is_next in *.
    + exfalso. assert (Hin : in_state (c,v,j) (next (c, v, j) sigma12)).
      { constructor; left; reflexivity. }
      apply H1 in Hin.
      destruct Hin as [Hin | Hin]; apply (in_empty_state _ Hin).
    + assert (Heq : (next (c0, v0, sigma2_1) sigma2_2) = (next (c, v, j) sigma12)).
      { apply sorted_syntactic_state_inclusion_equality_predicate; try assumption.
        - intros msg Hin. apply H1. right; assumption.
        - intros msg Hin. apply H1 in Hin. destruct Hin; try assumption.
          exfalso. apply (in_empty_state _ H2).
      }
      rewrite Heq. constructor.
    + assert (Heq : (next (c0, v0, sigma1_1) sigma1_2) = (next (c, v, j) sigma12)).
      { apply sorted_syntactic_state_inclusion_equality_predicate; try assumption.
        - intros msg Hin. apply H1. left; assumption.
        - intros msg Hin. apply H1 in Hin. destruct Hin; try assumption.
          exfalso. apply (in_empty_state _ H2).
      }
      rewrite Heq. constructor.
    + apply sorted_syntactic_state_union_decomposition in H1; try assumption.
      apply locally_sorted_tail in H as LS1_2.
      apply locally_sorted_tail in H0 as LS2_2.
      apply locally_sorted_tail in LS12 as LS12'.
      destruct H1 as [[Eq1 [Eq2 HUnion]] | [[Eq1 [Lt HUnion]] | [Eq2 [Lt HUnion]]]]
      ; try (inversion Eq1; clear Eq1); try (inversion Eq2; clear Eq2); subst
      ; apply IHsigma12 in HUnion; try assumption.
      * constructor. assumption.
      * apply Sorted_union_Next_lt; assumption.
      * apply Sorted_union_Next_gt; assumption.
Qed.

Theorem sorted_union_iff_syntactic_state_union : forall sigma1 sigma2 sigma12,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma12 ->
  syntactic_state_union sigma1 sigma2 sigma12 <->
  sorted_union sigma1 sigma2 sigma12.
Proof.
  intros; split.
  - apply syntactic_state_union_to_sorted_union; assumption.
  - apply sorted_union_to_syntactic_state_union.
Qed.

Theorem sorted_union_assoc : forall sigma1 sigma2 sigma3 sigma12 sigma23 sigma123,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted sigma3 ->
  sorted_union sigma1 sigma2 sigma12 ->
  sorted_union sigma12 sigma3 sigma123 ->
  sorted_union sigma2 sigma3 sigma23 ->
  sorted_union sigma1 sigma23 sigma123.
Proof.
  intros sigma1 sigma2 sigma3 sigma12 sigma23 sigma123 LS1 LS2 LS3 Union12 Union123 Union23.
  apply (sorted_union_locally_sorted _ _ _ Union12 LS1) in LS2 as LS12.
  apply (sorted_union_locally_sorted _ _ _ Union23 LS2) in LS3 as LS23.
  apply (sorted_union_locally_sorted _ _ _ Union123 LS12) in LS3 as LS123.
  apply sorted_union_iff_syntactic_state_union; try assumption.
  apply sorted_union_iff_syntactic_state_union in Union12; try assumption.
  apply sorted_union_iff_syntactic_state_union in Union23; try assumption.
  apply sorted_union_iff_syntactic_state_union in Union123; try assumption.
  intro; split; intro.
  - apply Union123 in H. destruct H.
    + apply Union12 in H. destruct H.
      * left; assumption.
      * right. apply Union23. left. assumption.
    + right. apply Union23. right. assumption.
  - apply Union123. destruct H.
    + left. apply Union12. left. assumption.
    + apply Union23 in H. destruct H.
      * left. apply Union12. right. assumption.
      * right. assumption.
Qed.

Lemma sorted_union_total : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  exists sigma, sorted_union sigma1 sigma2 sigma.
Proof.
  induction sigma1; intros.
  - exists sigma2. constructor.
  - clear IHsigma1_1. rename sigma1_1 into j. rename sigma1_2 into sigma1. rename IHsigma1_2 into IHsigma1.
    repeat rewrite add_is_next in *.
    apply locally_sorted_tail in H as LSsigma1.
    apply locally_sorted_head in H as LSmsg.
    destruct (add_in_sorted_total (c,v,j) sigma2).
    apply add_in_sorted_sorted in H1 as LSx; try assumption.
    apply locally_sorted_next_message in H as Hadd.
    rewrite sorted_union_singleton in *.
    destruct (IHsigma1 x); try assumption.
    exists x0.
    apply sorted_union_commutative.
    apply sorted_union_commutative in H1.
    apply sorted_union_commutative in H2.
    apply (sorted_union_assoc _ (next (c, v, j) Empty) sigma1 x); try assumption.
Qed.
