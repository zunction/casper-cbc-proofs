Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.locally_sorted.


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

Fixpoint add_in_sorted_fn (msg: message) (sigma: state) : state :=
  match msg, sigma with
  | _, Empty => next msg Empty
  | msg, add (c, v, j) to sigma' =>
    match message_compare msg (c, v, j) with
    | Eq => sigma
    | Lt => next msg sigma
    | Gt => next (c, v, j) (add_in_sorted_fn msg sigma')
    end
  end.

Lemma set_eq_add_in_sorted : forall msg sigma,
  set_eq (get_messages (add_in_sorted_fn msg sigma)) (msg :: (get_messages sigma)).
Proof.
  induction sigma.
  - simpl. rewrite get_messages_next. simpl. split; apply incl_refl.
  - clear IHsigma1. simpl.
    destruct (message_compare msg (c, v, sigma1)) eqn:Hcmp.
    + simpl. apply (proj1 message_compare_strict_order) in Hcmp. subst.
      split; intros x H.
      * right. assumption.
      * destruct H; try assumption; subst. left. reflexivity.
    + rewrite get_messages_next. simpl. split; apply incl_refl.
    + simpl. split; intros x Hin.
      * destruct Hin; try (right; left; assumption).
        apply IHsigma2 in H. destruct H; try (left; assumption).
        right; right; assumption.
      * { destruct Hin as [Hmsg | [H1 | H2]]
        ; (left; assumption) || (right; apply IHsigma2)
        .
        - left; assumption.
        - right; assumption.
        }
Qed.

Lemma add_in_sorted_next : forall msg1 msg2 sigma,
  add_in_sorted_fn msg1 (next msg2 sigma) =
    match message_compare msg1 msg2 with
    | Eq => next msg2 sigma
    | Lt => next msg1 (next msg2 sigma)
    | Gt => next msg2 (add_in_sorted_fn msg1 sigma)
    end.
Proof.
  intros msg1 [(c, v) j] sigma. reflexivity.
Qed.

Lemma add_in_empty : forall msg sigma,
  add_in_sorted msg Empty sigma -> sigma = (next msg Empty).
Proof.
  intros [(c, v) j] sigma AddA. 
  inversion AddA as 
    [ [(ca, va) ja] A AEmpty C
    | [(ca, va) ja] sigmaA A ANext C
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA smsg smsg' smsg1
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddA' A B C]
  ; clear AddA; subst.
  - reflexivity.
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
    + apply (state_set_In _ _ _ H) in H0 as Hlt.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.

Lemma add_in_sorted_sorted : forall msg sigma sigma',
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  add_in_sorted msg sigma sigma' -> locally_sorted sigma'.
Proof.
  intros msg sigma sigma' Hsorted. 
  generalize dependent sigma'.
  generalize dependent msg.
  induction Hsorted as
  [
  | sc sv sj LSsj
  | sc sv sj [(sc', sv') sj'] ssigma LSsj _  LT LSs
  ]
  ; intros [(c, v) j] sigma' LSmsg AddA
  ; apply locally_sorted_message_justification in LSmsg as LSj
  ; inversion AddA as 
    [ [(ca, va) ja] AA AEmpty AC
    | [(ca, va) ja] sigmaA AA ANext AC
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA AA AB AC
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddB AA AB AC]
  ; clear AddA; subst
  ; try (rewrite add_is_next in *)
  ; try (apply LSorted_Singleton)
  ; try (apply LSorted_Next; try assumption; constructor)
  ; try assumption
  .
  - apply add_in_empty in AddB. subst. apply LSorted_Next; try assumption; constructor.
  - inversion AddB as 
    [ [(cb, vb) jb] BA BEmpty BC
    | [(cb, vb) jb] sigmaB BA BNext BC
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB LTB BA BB BC
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB sigmaB' LTB AddB' BA BB BC]
    ; clear AddB; subst
    ; try (apply LSorted_Next; assumption)
    .
    + repeat (apply LSorted_Next; try assumption).
    + apply LSorted_Next; try assumption.
      apply (IHLSs (c, v, j) _); try assumption.
      apply add_in_Next_gt; assumption.
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
