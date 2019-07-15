Require Import List.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.locally_sorted.


Module Add_In_Sorted_Extras
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PEstimator : Estimator PCons PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PEstimator.

Module PLocally_Sorted := Locally_Sorted PCons PVal PVal_Weights PEstimator.
Export PLocally_Sorted.


Inductive add_in_sorted : message -> state -> state -> Prop :=
   | add_in_Empty : forall msg,
          add_in_sorted msg Empty (next msg Empty)
   | add_in_Next_eq : forall msg sigma,
          add_in_sorted msg (next msg sigma) (next msg sigma)
   | add_in_Next_lt : forall msg msg' sigma,
          message_lt msg msg' ->  
          add_in_sorted msg (next msg' sigma) (next msg (next msg' sigma))
   | add_in_Next_gt : forall msg msg' sigma sigma',
          message_lt msg' msg ->
          add_in_sorted msg sigma sigma' ->
          add_in_sorted msg (next msg' sigma) (next msg' sigma')
  .


Lemma add_in_empty : forall msg sigma,
  add_in_sorted msg Empty sigma -> sigma = (next msg Empty).
Proof.
  intros [(c, v) j] sigma AddA. 
  inversion AddA as 
    [ [(ca, va) ja] A AEmpty C
    | [(ca, va) ja] sigmaA A ANext C
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA smsg smsg' smsg1
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddA' A B C]
  ; clear AddA.
  subst. reflexivity.
Qed.


Lemma add_in_sorted_function : RelationFunction2 add_in_sorted add_in_sorted_fn.
Proof.
  intros msg sigma1 sigma2; generalize dependent sigma2.
  induction sigma1; intros; split; intros.
  - apply add_in_empty in H. subst. reflexivity.
  - simpl in H. subst. constructor.
  - inversion H; subst; repeat rewrite add_is_next in *. 
    + apply no_confusion_next in H2; destruct H2; subst; simpl.
      rewrite message_compare_reflexive. reflexivity.
    + apply no_confusion_next in H0; destruct H0; subst; simpl.
      unfold message_lt in H2. unfold compare_lt in H2. rewrite H2. reflexivity.
    + apply no_confusion_next in H0; destruct H0; subst; simpl.
      unfold message_lt in H1. unfold compare_lt in H1.
      apply message_compare_asymmetric in H1. rewrite H1.
      apply IHsigma1_2 in H3. rewrite H3. reflexivity.
  - simpl in H. destruct (message_compare msg (c, v, sigma1_1)) eqn:Hcmp; subst; repeat rewrite add_is_next.
    + apply (proj1 message_compare_strict_order) in Hcmp; subst.
      apply add_in_Next_eq.
    + apply add_in_Next_lt. assumption.
    + apply add_in_Next_gt.
      * apply message_compare_asymmetric in Hcmp. assumption.
      * apply IHsigma1_2. reflexivity.
Qed.


Lemma add_in_sorted_sorted : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  add_in_sorted msg sigma sigma' ->
  locally_sorted sigma'.
Proof.
  intros. apply add_in_sorted_function in H1; subst.
  apply add_in_sorted_sorted; assumption.
Qed.

Lemma no_confusion_add_in_sorted_empty : forall msg sigma,
  ~ add_in_sorted msg sigma Empty.
Proof.
  intros. intro.
  apply add_in_sorted_function in H.
  destruct sigma.
  - simpl in H. apply (no_confusion_next_empty _ _ H).
  - simpl in H. 
    destruct (message_compare msg (c, v, sigma1))
    ; rewrite add_is_next in *
    ; apply (no_confusion_next_empty _ _ H)
    .
Qed.

Lemma add_in_sorted_functional : forall msg sigma1 sigma2 sigma2',
  add_in_sorted msg sigma1 sigma2 ->
  add_in_sorted msg sigma1 sigma2' ->
  sigma2 = sigma2'.
Proof.
  apply relation_function2_functional with add_in_sorted_fn.
  apply add_in_sorted_function.
Qed.

Lemma add_in_sorted_total : forall msg sigma,
  exists sigma', add_in_sorted msg sigma sigma'.
Proof.
  apply relation_function2_total with add_in_sorted_fn.
  apply add_in_sorted_function.
Qed.


Lemma add_in_sorted_message_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  in_state msg sigma'.
Proof.
  intros. unfold in_state.
  induction H; rewrite get_messages_next; simpl; try (left; reflexivity).
  right. assumption.
Qed.

Lemma add_in_sorted_no_junk : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  forall msg', in_state msg' sigma' -> msg' = msg \/ in_state msg' sigma.
Proof.
  intros msg sigma sigma' H.
  induction H as
  [ [(hc, hv) hj]
  | [(hc, hv) hj] Hsigma
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma HLT
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma Hsigma' HGT HAdd H_H 
  ]; intros [(c', v') j'] HIn; rewrite in_state_iff in HIn
  ; destruct HIn as [Hin1 | Hin2]
  ; try (right; assumption)
  ; try (inversion Hin1; subst; left; reflexivity)
  .
  - right. apply in_state_iff. right. assumption.
  - right. apply in_state_iff. inversion Hin1; clear Hin1; subst. left. reflexivity.
  - apply H_H in Hin2. destruct Hin2 as [HInEq | HIn'].
    + left. assumption.
    + right. apply in_state_iff. right. assumption.
Qed.

Lemma add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
  induction sigma; intros; repeat rewrite add_is_next in *.
  - exfalso. apply (in_empty_state _ H0).
  - rewrite in_state_iff in H0. destruct H0.
    + subst. constructor.
    + apply (locally_sorted_first (c, v, sigma1)) in H0 as Hlt; try assumption.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.

Lemma locally_sorted_next_message : forall msg sigma,
  locally_sorted (next msg sigma) ->
  add_in_sorted msg sigma (next msg sigma).
Proof.
  intros.
  apply locally_sorted_message_characterization in H.
  destruct H as 
    [ Hcempty
    | [[cmsg0 [LScmsg0 Hcnext]]
    | [cmsg1 [cmsg2 [csigma' [Hcnext [LScnext [LScmsg1 LTc]]]]]]
    ]]; subst
    ; try (apply no_confusion_next in Hcnext; destruct Hcnext; subst)
    .
  - exfalso. apply (no_confusion_next_empty _ _ Hcempty).
  - constructor.
  - constructor. assumption.
Qed.

Lemma add_in_sorted_state_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros msg sigma sigma' H. unfold syntactic_state_inclusion; unfold incl.
  induction H; intros; try assumption. 
  - simpl in H. inversion H.
  - rewrite get_messages_next. simpl.  right. assumption.
  - rewrite get_messages_next in *. simpl in H1. simpl. 
    destruct H1.
    + left. assumption.
    + right. apply IHadd_in_sorted.
      assumption. 
Qed.

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

End Add_In_Sorted_Extras.
