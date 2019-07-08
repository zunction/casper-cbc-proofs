Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.

Module Locally_Sorted
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PEstimator : Estimator PCons PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Export PEstimator.

(** (Locally) Sorted states **)
Inductive locally_sorted : state -> Prop :=
  | LSorted_Empty : locally_sorted Empty
  | LSorted_Singleton : forall c v j,
          locally_sorted j ->
          locally_sorted (next (c, v, j) Empty)
  | LSorted_Next : forall c v j msg' sigma, 
          locally_sorted j  ->
          message_lt (c, v, j) msg' -> 
          locally_sorted (next msg' sigma) -> 
          locally_sorted (next (c, v, j) (next msg' sigma))
  .

Definition locally_sorted_msg (msg : message) : Prop :=
  locally_sorted (next msg Empty).

Lemma locally_sorted_message_justification : forall c v j,
  locally_sorted_msg (c,v,j) <-> locally_sorted j.
Proof.
  intros; split; intro.
  - inversion H; subst; assumption.
  - apply LSorted_Singleton. assumption.
Qed.

Lemma locally_sorted_message_characterization : forall sigma,
  locally_sorted sigma <->
  sigma = Empty
  \/
  (exists msg, locally_sorted_msg msg /\ sigma = next msg Empty)
  \/
  (exists msg1 msg2 sigma',
    sigma = next msg1 (next msg2 sigma') 
    /\ locally_sorted (next msg2 sigma')
    /\ locally_sorted_msg msg1
    /\ message_lt msg1 msg2
  ).
Proof.
  split; intros.
  { inversion H; subst.
    - left. reflexivity.
    - right. left. exists (c,v,j).
      split; try reflexivity.
      apply locally_sorted_message_justification. assumption.
    - right. right. exists (c, v, j). exists msg'. exists sigma0.
      split; try reflexivity.
      repeat (split; try assumption).
      apply locally_sorted_message_justification. assumption.
  }
  { destruct H as [H | [H | H]]; subst; try constructor.
    - destruct H as [msg [LSmsg EQ]]; subst.
      destruct msg as [(c,v) j]. apply locally_sorted_message_justification in LSmsg.
      constructor. assumption.
    - destruct H as [msg1 [msg2 [sigma' [EQ [LS2' [LSmsg1 LT]]]]]]; subst.
      destruct msg1 as [(c1,v1) j1]. apply locally_sorted_message_justification in LSmsg1.
      constructor; assumption.
  }
Qed.

Lemma locally_sorted_next_next : forall msg1 msg2 sigma,
  locally_sorted (next msg1 (next msg2 sigma)) ->
  message_lt msg1 msg2.
Proof.
  intros. apply locally_sorted_message_characterization in H.
  destruct H as [H | [[msg [_ H]] | [msg1' [msg2' [sigma' [H [_ [_ Hlt]]]]]]]].
  - exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [_ H].
    exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [Heq H]; subst.
    apply no_confusion_next in H. destruct H as [Heq H]; subst.
    assumption.
Qed.

Lemma locally_sorted_remove_second : forall msg1 msg2 sigma,
  locally_sorted (next msg1 (next msg2 sigma)) ->
  locally_sorted (next msg1 sigma).
Proof.
  intros.
  apply locally_sorted_message_characterization in H.
  destruct H as [H | [[msg [_ H]] | [msg1' [msg2' [sigma' [Heq [H [Hj Hlt]]]]]]]].
  - exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in H. destruct H as [_ H].
    exfalso. apply (no_confusion_next_empty _ _ H).
  - apply no_confusion_next in Heq. destruct Heq as [Heq' Heq]; subst.
    apply no_confusion_next in Heq. destruct Heq as [Heq' Heq]; subst.
    apply locally_sorted_message_characterization in H.
    destruct H as [H | [[msg [_ H]] | [msg2'' [msg3 [sigma'' [Heq [H [_ Hlt2]]]]]]]].
    + exfalso. apply (no_confusion_next_empty _ _ H).
    + apply no_confusion_next in H. destruct H; subst. apply Hj.
    + apply no_confusion_next in Heq. destruct Heq; subst.
      apply (message_lt_transitive _ _ _ Hlt) in Hlt2. clear Hlt.
      destruct msg1' as [(c1', v1') j1']. destruct msg3 as [(c3, v3) j3].
      apply locally_sorted_message_justification in Hj.
      apply LSorted_Next; assumption. 
Qed.

Lemma locally_sorted_head : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted_msg msg.
Proof.
  intros [(c, v) j] sigma H. inversion H; subst; apply locally_sorted_message_justification; assumption.
Qed.

Lemma locally_sorted_tail : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted sigma.
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
  - exfalso; apply (no_confusion_next_empty _ _ Hcempty).
  - constructor.
  - assumption.
Qed.

Lemma locally_sorted_all : forall sigma,
  locally_sorted sigma ->
  Forall locally_sorted_msg (get_messages sigma).
Proof.
  intros. rewrite Forall_forall. induction H; simpl; intros msg Hin.
  - inversion Hin.
  - destruct Hin as [Hin | Hin] ; subst; try inversion Hin.
    apply locally_sorted_message_justification. assumption.
  - destruct Hin as [Heq | Hin]; subst.
    + apply locally_sorted_message_justification. assumption.
    + apply IHlocally_sorted2. assumption.
Qed.

Lemma locally_sorted_first : forall msg sigma,
  locally_sorted (next msg sigma) ->
  forall msg',
  in_state msg' sigma ->
  message_lt msg msg'.
Proof.
  intros msg sigma. generalize dependent msg. induction sigma; intros.
  - inversion H0.
  - rewrite add_is_next in *. apply locally_sorted_next_next in H as H1.
    rewrite in_state_iff in H0. destruct H0; subst.
    + assumption.
    + apply locally_sorted_remove_second in H. apply IHsigma2; assumption.
Qed.

Lemma sorted_syntactic_state_inclusion_first_equal : forall sigma sigma' msg,
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg sigma') ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros.
  intros msg' Hin.
  apply (locally_sorted_first msg) in Hin as Hlt; try assumption.
  unfold syntactic_state_inclusion in H1. 
  assert (Hin' : In msg' (get_messages (next msg sigma))).
  { rewrite get_messages_next. right. assumption. }
  apply H1 in Hin'. rewrite get_messages_next in Hin'.
  destruct Hin'; try assumption; subst.
  exfalso. apply (message_lt_irreflexive _ Hlt).
Qed.

Lemma sorted_syntactic_state_inclusion : forall sigma sigma' msg msg',
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg' sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg' sigma') ->
  (msg = msg' /\ syntactic_state_inclusion sigma sigma')
  \/
  (message_lt msg' msg /\ syntactic_state_inclusion (next msg sigma) sigma').
Proof.
  intros. unfold syntactic_state_inclusion in H1.
  assert (Hin : In msg (get_messages (next msg' sigma'))).
  { apply H1. rewrite get_messages_next. left. reflexivity. }
  rewrite get_messages_next in Hin.  simpl in Hin.
  destruct Hin.
  - left. subst. split; try reflexivity.
    apply sorted_syntactic_state_inclusion_first_equal with msg; assumption.
  - right. apply (locally_sorted_first msg') in H2 as Hlt; try assumption.
    split; try assumption.
    intros msg1 Hin1.
    apply H1 in Hin1 as H1in'.
    rewrite get_messages_next in H1in'.  simpl in H1in'.
    rewrite get_messages_next in Hin1.  simpl in Hin1.
    assert (Hlt1 : message_lt msg' msg1).
    { destruct Hin1; subst; try assumption.
      apply (locally_sorted_first msg) in H3; try assumption.
      apply message_lt_transitive with msg; assumption.
    }
    destruct H1in'; try assumption; subst.
    exfalso. apply (message_lt_irreflexive _ Hlt1).
Qed.

Lemma sorted_syntactic_state_inclusion_eq_ind : forall sigma1 sigma2 msg1 msg2,
  locally_sorted (next msg1 sigma1) ->
  locally_sorted (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg1 sigma1) (next msg2 sigma2) ->
  syntactic_state_inclusion (next msg2 sigma2) (next msg1 sigma1) ->
  msg1 = msg2 /\ syntactic_state_inclusion sigma1 sigma2 /\ syntactic_state_inclusion sigma2 sigma1.
Proof.
  intros.
  apply sorted_syntactic_state_inclusion in H1; try assumption.
  apply sorted_syntactic_state_inclusion in H2; try assumption.
  destruct H1; destruct H2; destruct H1; destruct H2; subst.
  - repeat (split; try reflexivity; try assumption).
  - exfalso. apply (message_lt_irreflexive _ H2).
  - exfalso. apply (message_lt_irreflexive _ H1).
  - exfalso. apply (message_lt_transitive _ _ _ H1) in H2. apply (message_lt_irreflexive _ H2).
Qed.

Lemma sorted_syntactic_state_inclusion_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  syntactic_state_inclusion sigma1 sigma2 ->
  syntactic_state_inclusion sigma2 sigma1 ->
  sigma1 = sigma2.
Proof.
  induction sigma1; intros; destruct sigma2; repeat rewrite add_is_next in *.
  - reflexivity.
  - unfold syntactic_state_inclusion in H2. rewrite get_messages_next in H2.
    simpl in H2. apply incl_empty in H2. discriminate.
  - unfold syntactic_state_inclusion in H1. rewrite get_messages_next in H1.
    simpl in H1. apply incl_empty in H1. discriminate.
  - apply sorted_syntactic_state_inclusion_eq_ind in H2; try assumption.
    destruct H2 as [Heq [Hin12 Hin21]].
    inversion Heq; subst; clear Heq.
    apply locally_sorted_tail in H.
    apply locally_sorted_tail in H0.
    apply IHsigma1_2 in Hin21; try assumption.
    subst.
    reflexivity.
Qed.


(*****************)
(* Add_in_sorted *)
(*****************)

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

Lemma in_state_add_in_sorted_iff : forall msg msg' sigma',
  in_state msg (add_in_sorted_fn msg' sigma') <->
  msg = msg' \/ in_state msg sigma'.
Proof.
  intros.
  destruct (set_eq_add_in_sorted msg' sigma') as [Hincl1 Hincl2].
  split; intros.
  - apply Hincl1 in H. destruct H.
    + subst. left. reflexivity.
    + right. assumption.
  - apply Hincl2. destruct H; subst.
    + left. reflexivity.
    + right. assumption.
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

Lemma add_in_sorted_non_empty : forall msg sigma,
  add_in_sorted_fn msg sigma <> Empty.
Proof.
  intros. intro Hadd.
  destruct sigma; inversion Hadd.
  - apply (no_confusion_next_empty _ _ H0).
  - destruct (message_compare msg (c, v, sigma1)); inversion H0.
    apply (no_confusion_next_empty _ _ H0).
Qed.


Lemma add_in_sorted_inv1 : forall msg msg' sigma,
  add_in_sorted_fn msg sigma = next msg' Empty -> msg = msg'.
Proof.
  intros [(c, v) j] msg' sigma AddA.
  destruct sigma.
  - simpl in AddA. rewrite add_is_next in AddA. apply no_confusion_next in AddA.
    destruct AddA. assumption.
  - simpl in AddA. destruct (message_compare (c, v, j) (c0, v0, sigma1)) eqn:Hcmp
    ; rewrite add_is_next in AddA; apply no_confusion_next in AddA; destruct AddA; subst;
    try reflexivity.
    + apply (proj1 message_compare_strict_order) in Hcmp; inversion Hcmp; subst; clear Hcmp.
      reflexivity.
    + exfalso. apply (add_in_sorted_non_empty _ _ H0).
Qed.

Lemma add_in_sorted_sorted : forall msg sigma,
  locally_sorted sigma ->
  locally_sorted_msg msg ->
  locally_sorted (add_in_sorted_fn msg sigma).
Proof.
  intros msg sigma. generalize dependent msg.
  induction sigma; intros.
  - simpl. assumption.
  - clear IHsigma1; rename sigma1 into j; rename sigma2 into sigma; rename IHsigma2 into IHsigma.
    simpl. destruct msg as [(mc, mv) mj].
    apply locally_sorted_message_justification in H0 as Hmj.
    repeat rewrite add_is_next in *.
    apply locally_sorted_tail in H as Hsigma.
    apply locally_sorted_head in H as Hcvj. apply locally_sorted_message_justification in Hcvj as Hj.
    apply (IHsigma _ Hsigma) in H0 as HLSadd.
    destruct (message_compare (mc, mv, mj) (c, v, j)) eqn:Hcmp.
    + assumption.
    + constructor; assumption.
    + apply message_compare_asymmetric in Hcmp.
      apply locally_sorted_message_characterization in HLSadd as Hadd.
      destruct Hadd as [Hadd | [Hadd | Hadd]].
      * exfalso. apply (add_in_sorted_non_empty _ _ Hadd).
      * destruct Hadd as [msg' [Hmsg' Hadd]]. rewrite Hadd.
        apply add_in_sorted_inv1 in Hadd; subst.
        constructor; assumption.
      * destruct Hadd as [msg1 [msg2 [sigma' [Hadd [HLS' [H1 Hlt12]]]]]].
        rewrite Hadd in *. constructor; try assumption.
        assert (Forall (message_lt (c, v, j)) (get_messages (add_in_sorted_fn (mc, mv, mj) sigma))).
        { apply Forall_forall. intros. apply set_eq_add_in_sorted in H2.
          destruct H2 as [Heq | Hin]; subst; try assumption.
          apply locally_sorted_first with sigma; assumption.
        }
        rewrite Hadd in H2. rewrite get_messages_next in H2. apply Forall_inv in H2. assumption.
Qed.


(*****************)
(* List_to_state *)
(*****************)

Definition list_to_state (msgs : list message) : state :=
  fold_right add_in_sorted_fn Empty msgs.

Lemma list_to_state_locally_sorted : forall msgs,
  Forall locally_sorted_msg msgs ->
  locally_sorted (list_to_state msgs).
Proof.
  induction msgs; simpl; try constructor; intros.
  apply add_in_sorted_sorted.
  - apply IHmsgs. apply Forall_forall. intros msg Hin.
    rewrite Forall_forall in H. apply H. right. assumption.
  - apply Forall_inv with msgs. assumption.
Qed.

Lemma list_to_state_iff : forall msgs : list message,
  set_eq (get_messages (list_to_state msgs)) msgs.
Proof.
  induction msgs; intros.
  - simpl. split; apply incl_refl.
  - simpl. apply set_eq_tran with (a :: (get_messages (list_to_state msgs))).
    + apply set_eq_add_in_sorted.
    + apply set_eq_cons. assumption.
Qed.

Lemma list_to_state_sorted : forall sigma,
  locally_sorted sigma ->
  list_to_state (get_messages sigma) = sigma.
Proof.
  intros. induction H; try reflexivity.
  rewrite get_messages_next. simpl. rewrite IHlocally_sorted2.
  rewrite add_in_sorted_next. rewrite H0. reflexivity.
Qed.


(*****************)
(** State Union **)
(*****************)

Definition state_union (sigma1 sigma2 : state) : state :=
  (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))).

Lemma state_union_messages : forall sigma1 sigma2,
  set_eq (get_messages (state_union sigma1 sigma2)) (messages_union (get_messages sigma1) (get_messages sigma2)).
Proof.
  intros.
  apply list_to_state_iff.
Qed.


Lemma state_union_incl_right : forall sigma1 sigma2,
  syntactic_state_inclusion sigma2 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages. apply set_union_incl_right. assumption.
Qed.

Lemma state_union_incl_left : forall sigma1 sigma2,
  syntactic_state_inclusion sigma1 (state_union sigma1 sigma2).
Proof.
  intros. intros msg Hin. apply state_union_messages. apply set_union_incl_left. assumption.
Qed.

Lemma state_union_iff : forall msg sigma1 sigma2,
  in_state msg (state_union sigma1 sigma2) <-> in_state msg sigma1 \/ in_state msg sigma2.
Proof.
  intros; unfold state_union; unfold in_state; split; intros.
  - apply state_union_messages in H. unfold messages_union in H. rewrite set_union_iff in H. assumption.
  - apply state_union_messages. unfold messages_union. rewrite set_union_iff. assumption.
Qed.

Lemma state_union_incl_iterated : forall sigmas sigma,
  In sigma sigmas ->
  syntactic_state_inclusion sigma (fold_right state_union Empty sigmas).
Proof.
  induction sigmas; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. apply state_union_incl_left.
    + apply IHsigmas in H. apply incl_tran with (get_messages (fold_right state_union Empty sigmas)); try assumption.
      apply state_union_incl_right.
Qed.

Lemma state_union_sorted : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted (state_union sigma1 sigma2).
Proof.
  intros.
  apply locally_sorted_all in H as Hall1. rewrite Forall_forall in Hall1.
  apply locally_sorted_all in H0 as Hall2. rewrite Forall_forall in Hall2.
  apply list_to_state_locally_sorted. apply Forall_forall. intros msg Hin.
  unfold messages_union in Hin.
  rewrite set_union_iff in Hin. destruct Hin.
  - apply Hall1. assumption.
  - apply Hall2. assumption.
Qed.

Lemma state_union_add_in_sorted : forall sigma1 msg2 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  locally_sorted_msg msg2 ->
  state_union sigma1 (add_in_sorted_fn msg2 sigma2) = add_in_sorted_fn msg2 (state_union sigma1 sigma2).
Proof.
  intros.
  apply sorted_syntactic_state_inclusion_equality_predicate.
  - apply state_union_sorted; try assumption. 
    apply add_in_sorted_sorted; assumption.
  - apply add_in_sorted_sorted; try assumption.
    apply state_union_sorted; assumption.
  - intros msg Hin. 
    apply state_union_iff in Hin.
    apply set_eq_add_in_sorted.
    destruct Hin as [Hin | Hin].
    + right. apply state_union_iff. left; assumption.
    + apply set_eq_add_in_sorted in Hin. destruct Hin as [Heq | Hin]; subst.
      * left; reflexivity.
      * right.  apply state_union_iff. right; assumption.
  - intros msg Hin.
    apply set_eq_add_in_sorted in Hin.
    apply state_union_iff.
    destruct Hin as [Heq | Hin]; subst.
    + right. apply set_eq_add_in_sorted. left; reflexivity.
    + apply state_union_iff in Hin.
      destruct Hin.
      * left; assumption.
      * right. apply set_eq_add_in_sorted. 
      right; assumption.
Qed.
End Locally_Sorted.