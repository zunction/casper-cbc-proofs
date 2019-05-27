Require Import Casper.preamble.

Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.in_state.

Definition syntactic_state_union (sigma1 : state) (sigma2 : state) (sigma12 : state) : Prop :=
  forall msg, in_state msg sigma12 <-> in_state msg sigma1 \/ in_state msg sigma2 .

Theorem syntactic_state_union_commutative : Commutative syntactic_state_union.
Proof.
  unfold Commutative; intros. intro. split; intros.
  - apply H in H0. destruct H0.
    + right; assumption.
    + left; assumption.
  - apply H. destruct H0.
    + right; assumption.
    + left; assumption.
Qed.

Theorem add_in_sorted_state_union : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  syntactic_state_union (next msg Empty) sigma sigma'.
Proof.
  intros msg sigma sigma' H. unfold syntactic_state_union.
  induction H; intros; split; intros
  .
  - left; assumption.
  - destruct H; try assumption. exfalso. apply (in_empty_state msg0 H).
  - right; assumption.
  - destruct H; try assumption. 
    apply in_singleton_state in H; subst.
    constructor; left; reflexivity.
  - inversion H0; subst; clear H0.
    apply no_confusion_next in H1; destruct H1; subst.
    destruct H3; subst.
    + left. constructor. left. reflexivity.
    + right. assumption.
  - constructor. destruct H0.
    + apply in_singleton_state in H0; subst. left; reflexivity.
    + right. assumption.
  - inversion H1; subst; clear H1.
    apply no_confusion_next in H2; destruct H2; subst.
    destruct H4; subst.
    + right. constructor. left. reflexivity.
    + apply IHadd_in_sorted in H1. 
      destruct H1. 
      * left; assumption.
      * right; constructor; right; assumption.
  - constructor. rewrite IHadd_in_sorted.
    destruct H1.
    + right; left; assumption.
    + inversion H1; subst; clear H1.
      apply no_confusion_next in H2; destruct H2; subst.
      destruct H4; subst.
      * left; reflexivity.
      * right; right; assumption.  
Qed.

Lemma sorted_syntactic_state_union_decomposition_step : forall sigma1 msg2 sigma2 msg12 sigma12,
  locally_sorted (next msg12 sigma1) ->
  locally_sorted (next msg2 sigma2) ->
  locally_sorted (next msg12 sigma12) ->
  syntactic_state_union (next msg12 sigma1) (next msg2 sigma2) (next msg12 sigma12) ->
  in_state msg2 sigma12 ->
  msg_lt msg12 msg2 /\ syntactic_state_union sigma1 (next msg2 sigma2) sigma12.
Proof.
  intros.
  rename H3 into H4.
  apply (state_set_In _ _ _ H1) in H4 as Hlt122.
  split; try assumption.
  split; intros.
  + apply (state_set_In _ _ _ H1) in H3 as Hlt12. 
    assert (Hin : in_state msg (next msg12 sigma12)).
    { constructor; right; assumption. }
    apply H2 in Hin.
    destruct Hin as [Hin | Hin]
    ; inversion Hin; subst
    ; apply no_confusion_next in H5; destruct H5; subst
    ; destruct H7; subst
    .
    * exfalso; apply (msg_lt_irreflexive _ Hlt12).
    * left; assumption.
    * right; constructor; left; reflexivity.
    * right; constructor; right; assumption.
  + assert (Hin : in_state msg (next msg12 sigma12)).
    { apply H2. destruct H3.
      - left; constructor; right; assumption.
      - right; assumption.
    }
    inversion Hin; subst; clear Hin.
    inversion H5; subst; clear H5.
    apply no_confusion_next in H8; destruct H8; subst.
    destruct H7; try assumption; subst.
    exfalso. destruct H3.
    * apply (state_set_In _ _ _ H) in H3. apply (msg_lt_irreflexive _ H3).
    * inversion H3; subst; clear H3.
      apply no_confusion_next in H5; destruct H5; subst.
      destruct H7; subst; apply msg_lt_irreflexive with msg2; try assumption.
      apply (state_set_In _ _ _ H0) in H3. 
      apply (msg_lt_transitive _ _ _ H3 Hlt122).
Qed.

Lemma sorted_syntactic_state_union_decomposition : forall msg1 sigma1 msg2 sigma2 msg12 sigma12,
  locally_sorted (next msg1 sigma1) ->
  locally_sorted (next msg2 sigma2) ->
  locally_sorted (next msg12 sigma12) ->
  syntactic_state_union (next msg1 sigma1) (next msg2 sigma2) (next msg12 sigma12) ->
  msg12 = msg1 /\ msg12 = msg2 /\  syntactic_state_union sigma1 sigma2 sigma12
  \/
  msg12 = msg1 /\ msg_lt msg12 msg2 /\  syntactic_state_union sigma1 (next msg2 sigma2) sigma12
  \/
  msg12 = msg2 /\ msg_lt msg12 msg1 /\  syntactic_state_union (next msg1 sigma1) sigma2 sigma12
  .
Proof.
  intros.
  assert (Hin1 : in_state msg1 (next msg12 sigma12)).
  { apply H2. left. constructor. left. reflexivity. }
  inversion Hin1; subst; clear Hin1.
  apply no_confusion_next in H3; destruct H3; subst.
  assert (Hin2 : in_state msg2 (next msg12 sigma12)).
  { apply H2. right. constructor. left. reflexivity. }
  inversion Hin2; subst; clear Hin2.
  apply no_confusion_next in H3; destruct H3; subst.
  destruct H5; destruct H6; subst.
  - left. repeat (split; try reflexivity); intros.
    + apply (state_set_In _ _ _ H1) in H3 as Hlt.
      assert (Hin : in_state msg (next msg12 sigma12)).
      { constructor. right. assumption. }
      apply H2 in Hin.
      destruct Hin 
      ; inversion H4; subst; clear H4
      ; apply no_confusion_next in H5; destruct H5; subst
      ; destruct H7; subst
      ; try (exfalso; apply (msg_lt_irreflexive _ Hlt))
      .
      * left; assumption.
      * right; assumption.
    + assert (Hin : in_state msg (next msg12 sigma12)).
      { apply H2. destruct H3.
        - left; constructor; right; assumption.
        - right; constructor; right; assumption.
      }
      inversion Hin; subst; clear Hin.
      inversion H4; subst; clear H4.
      apply no_confusion_next in H7; destruct H7; subst.
      destruct H6; try assumption; subst.
      exfalso. destruct H3.
      * apply (state_set_In _ _ _ H) in H3. apply (msg_lt_irreflexive _ H3).
      * apply (state_set_In _ _ _ H0) in H3. apply (msg_lt_irreflexive _ H3).
  - right. left. split; try reflexivity. 
    apply sorted_syntactic_state_union_decomposition_step; assumption.
  - right. right.  split; try reflexivity.
    apply syntactic_state_union_commutative in H2.
    apply (sorted_syntactic_state_union_decomposition_step _ _ _ _ _ H0 H H1 H2) in H3.
    destruct H3.
    apply syntactic_state_union_commutative in H4.
    split; assumption.
  - apply (state_set_In _ _ _ H1) in H3.  apply (state_set_In _ _ _ H1) in H4.
    exfalso.
    assert (Hin : in_state msg12 (next msg12 sigma12)).
    { constructor. left. reflexivity. }
    apply H2 in Hin.
    destruct Hin as [Hin | Hin]
    ; inversion Hin as [a b c d e f]; subst; clear Hin
    ; apply no_confusion_next in f; destruct f; subst
    ; destruct d; subst
    .
    + apply (msg_lt_irreflexive _ H3).
    + apply (state_set_In _ _ _ H) in H5. apply (msg_lt_irreflexive msg1).
      apply (msg_lt_transitive _ _ _ H5 H3).
    + apply (msg_lt_irreflexive _ H4).
    + apply (state_set_In _ _ _ H0) in H5. apply (msg_lt_irreflexive msg2).
      apply (msg_lt_transitive _ _ _ H5 H4).
Qed.