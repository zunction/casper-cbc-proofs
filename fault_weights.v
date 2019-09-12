Require Import Bool Reals List ListSet.
Import ListNotations.
From Casper 
Require Import preamble ListExtras ListSetExtras locally_sorted.

(** Abstract consensus values **)
Parameters (C : Type)
           (C_inhabited : exists (c : C), True)
           (C_compare : C -> C -> comparison)
           (C_compare_strictorder : CompareStrictOrder C_compare). 

Instance C_type : StrictlyComparable C :=
  { inhabited := C_inhabited; 
    compare := C_compare;
    compare_strictorder := C_compare_strictorder; }. 

(** Abstract validators **) 
Parameters (V : Type)
           (V_inhabited : exists (v : V), True)
           (V_compare : V -> V -> comparison)
           (V_compare_strictorder : CompareStrictOrder V_compare). 

Instance V_type : StrictlyComparable V :=
  { inhabited := V_inhabited;
    compare := V_compare;
    compare_strictorder := V_compare_strictorder; }.  

(** Parameter weight **)
Parameter weight_full : V -> {r : R | (r > 0)%R}.
Definition sum_weight_senders (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight_full v) + r)%R) 0%R l. 

(** Parameter threshold **)
Parameters (t_full : {r | (r >= 0)%R})
           (suff_val_full : exists (vs : list V), NoDup vs /\
                                             (sum_weight_senders vs > proj1_sig t_full)%R).

Definition full_state : Type := state C V.

Definition full_message : Type := message C V.

Definition full_in_state_fn := in_state_fn C V C_type V_type message_compare about_message.

Definition equivocating_messages (msg1 msg2 : full_message) : bool :=
  match compare_eq_dec msg1 msg2 with
  | left _ => false
  | _ => match msg1, msg2 with (c1, v1, j1), (c2, v2, j2) =>
      match compare_eq_dec v1 v2 with
      | left _ => negb (full_in_state_fn msg1 j2) && negb (full_in_state_fn msg2 j1)
      | right _ => false
      end
    end
  end.

Lemma equivocating_messages_comm : forall msg1 msg2,
  equivocating_messages msg1 msg2 = equivocating_messages msg2 msg1.
Proof.
  intros [(c1, v1) sigma1] [(c2, v2) sigma2].
  unfold equivocating_messages.
  destruct (message_eq_dec (c1, v1, sigma1) (c2, v2, sigma2))
  ; try (rewrite eq_dec_if_true; try reflexivity; symmetry; assumption).
  rewrite (eq_dec_if_false message_eq_dec)
  ; try (intro; apply n; symmetry; assumption).
  destruct (v_eq_dec v1 v2)
  ; try (rewrite eq_dec_if_false; try reflexivity; intro; apply n0; symmetry; assumption).
  subst.
  rewrite eq_dec_if_true; try reflexivity.
  rewrite andb_comm. reflexivity.
Qed.

Lemma non_equivocating_messages_extend : forall msg sigma1 c v,
  In msg (get_messages sigma1) ->
  equivocating_messages msg (c, v, sigma1) = false.
Proof.
  intros [(c0, v0) sigma']; intros.
  unfold equivocating_messages.
  destruct (message_eq_dec (c0, v0, sigma') (c, v, sigma1)); try reflexivity.
  destruct (v_eq_dec v0 v); try reflexivity.
  assert (Hin : in_state_fn (c0, v0, sigma') sigma1 = true).
  { unfold in_state_fn. rewrite in_state_dec_if_true; try reflexivity. assumption. }
  rewrite Hin. simpl. reflexivity.
Qed.

Lemma non_equivocating_messages_sender : forall msg1 msg2,
  sender msg1 <> sender msg2 ->
  equivocating_messages msg1 msg2 = false.
Proof.
  intros [(c1, v1) j1] [(c2, v2) j2] Hneq. simpl in Hneq.
  unfold equivocating_messages.
  rewrite eq_dec_if_false.
  - rewrite eq_dec_if_false; try reflexivity. assumption.
  - intro Heq. inversion Heq; subst; clear Heq. apply Hneq. reflexivity.
Qed.

Lemma equivocating_messages_sender : forall msg1 msg2,
  equivocating_messages msg1 msg2 = true ->
  sender msg1 = sender msg2.
Proof.
  unfold equivocating_messages.
  intros [(c1, v1) j1] [(c2, v2) j2] Hequiv.
  simpl. destruct (message_eq_dec (c1, v1, j1) (c2, v2, j2)).
  - inversion Hequiv.
  - destruct (v_eq_dec v1 v2); try assumption. inversion Hequiv.
Qed.

(******************************)
(* equivocating_message_state *)
(******************************)

Definition equivocating_message_state (msg : message) (sigma : state) : bool :=
  existsb (equivocating_messages msg) (get_messages sigma).

Lemma equivocating_message_state_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  forall msg,
  equivocating_message_state msg sigma = true -> equivocating_message_state msg sigma' = true.
Proof.
  unfold equivocating_message_state. 
  intros. rewrite existsb_exists in *. destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma non_equivocating_extend : forall sigma sigma' c v,
  syntactic_state_inclusion sigma sigma' ->
  equivocating_message_state (c, v, sigma') sigma = false.
Proof.
  unfold equivocating_message_state.
  induction sigma; intros.
  - reflexivity.
  - simpl. rewrite IHsigma2.
    + rewrite equivocating_messages_comm.
      rewrite non_equivocating_messages_extend; try reflexivity.
      apply H. left. reflexivity.
    + intros x Hin. apply H. right. assumption.
Qed.

Lemma equivocating_message_state_notIn : forall msg sigma,
  ~In (sender msg) (set_map v_eq_dec sender (get_messages sigma)) ->
  equivocating_message_state msg sigma = false.
Proof.
  intros [(c, v) j] sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  unfold equivocating_message_state. apply existsb_forall.
  intros [(cx, vx) jx] Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists (cx, vx, jx). split; try assumption. reflexivity.
Qed.

Definition equivocating_senders (sigma : state) : set V :=
  set_map v_eq_dec sender
    (filter (fun msg => equivocating_message_state msg sigma)
      (get_messages sigma)).

Lemma equivocating_senders_nodup : forall sigma,
  NoDup (equivocating_senders sigma).
Proof.
  intros. apply set_map_nodup.
Qed.

Lemma equivocating_senders_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_message_state msg sigma) (get_messages sigma')).
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro. apply equivocating_message_state_incl. assumption.
Qed.

Lemma equivocating_senders_extend : forall sigma c v,
  equivocating_senders (add (c, v, sigma) to sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  assert (Heq :
    (filter (fun msg : message => equivocating_message_state msg (add (c, v, sigma)to sigma))
      (get_messages (add (c, v, sigma)to sigma))) = 
    (filter (fun msg : message => equivocating_message_state msg sigma)
      (get_messages sigma))); try (rewrite Heq; reflexivity).
    simpl.
  assert
    (Hequiv : equivocating_message_state (c, v, sigma) (add (c, v, sigma)to sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros. rewrite equivocating_messages_comm.
    destruct H as [Heq | Hin].
    - subst. unfold equivocating_messages.
      rewrite eq_dec_if_true; reflexivity.
    - apply non_equivocating_messages_extend. assumption.
  }
  apply filter_eq_fn. intros. unfold equivocating_message_state. split; intros
  ; apply existsb_exists in H0; apply existsb_exists
  ; destruct H0 as [msg [Hin Hmsg]]; exists msg; split; try assumption.
  - simpl in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    exfalso. subst.
    apply (non_equivocating_messages_extend _ _ c v) in H.
    rewrite Hmsg in H. inversion H.
  - right. assumption.
Qed.

Lemma equivocating_senders_single : forall sigma c v j,
  ~In v (set_map v_eq_dec sender (get_messages sigma)) ->
  set_eq (equivocating_senders (add_in_sorted_fn (c, v, j) sigma)) (equivocating_senders sigma).
Proof.
  intros.
  unfold equivocating_senders. intros.
  split; intros v' Hin
  ; apply set_map_exists; apply set_map_exists in Hin
  ; destruct Hin as [[(cx, vx) jx] [Hin Heq]]
  ; simpl in Heq; subst
  ; exists (cx, v', jx)
  ; simpl; split; try reflexivity
  ; apply filter_In; apply filter_In in Hin
  ; destruct Hin as [Hin HEquiv]
  ; unfold equivocating_message_state in HEquiv
  ; apply existsb_exists in HEquiv
  ; destruct HEquiv as [[(cy, vy) jy] [Hiny HEquiv]]
  .
  - apply in_state_add_in_sorted_iff in Hiny. apply in_state_add_in_sorted_iff in Hin.
    destruct Hin.
    + exfalso. inversion H0; subst; clear H0.
      assert (Hnequiv : equivocating_messages (c, v, j) (cy, vy, jy) = false)
      ;try (rewrite Hnequiv  in HEquiv; inversion HEquiv); clear HEquiv.
      destruct Hiny.
      * rewrite H0. unfold equivocating_messages. rewrite eq_dec_if_true; reflexivity.
      * apply non_equivocating_messages_sender. simpl. intro; subst. apply H.
        apply set_map_exists. exists (cy, vy, jy). split; try reflexivity; assumption.
    + split; try assumption. unfold equivocating_message_state.
      apply existsb_exists. exists (cy, vy, jy).
      destruct Hiny.
      * exfalso. inversion H1; subst; clear H1. apply H.
        apply set_map_exists. exists (cx, v', jx). split; try assumption. simpl.
        apply equivocating_messages_sender in HEquiv. simpl in HEquiv. assumption.
      * split; assumption.
  -  split.
    + apply in_state_add_in_sorted_iff. right. assumption.
    + unfold equivocating_message_state. apply existsb_exists.
      exists (cy, vy, jy). split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.

Definition sum_weights : set V -> R := fold_right (fun v r => (weight v + r)%R) 0%R.

Definition fault_weight_state (sigma : state) : R := sum_weights (equivocating_senders sigma).


Lemma sum_weights_in : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (weight v + sum_weights (set_remove v_eq_dec v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (eq_dec_left v_eq_dec v). rewrite H. reflexivity.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (v_eq_dec v a); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (weight v) (weight a)). rewrite Rplus_assoc. 
    apply Rplus_eq_compat_l. apply IHvs; assumption.
Qed.

Lemma sum_weights_incl : forall vs vs',
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  intros vs vs'. generalize dependent vs.
  induction vs'; intros.
  - apply incl_empty in H1; subst. apply Rle_refl.
  - inversion H0; subst; clear H0.
    destruct (in_dec v_eq_dec a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup v_eq_dec a). assumption.
      * assumption.
      * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
        destruct Hrem as [Hin Hxa].
        apply H1 in Hin. destruct Hin; try assumption.
        exfalso; subst. apply Hxa. reflexivity.
      * assumption.
    + simpl. apply Rle_trans with (sum_weights vs').
      * apply IHvs'; try assumption.
        intros x Hin. apply H1 in Hin as Hin'. destruct Hin'; try assumption.
        exfalso; subst. apply n. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. apply weight_positive.
Qed.

Lemma fault_weight_state_incl : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

(** Proof obligations from CBC_protocol **)
Lemma equivocation_weight_compat : forall (s1 s2 : sorted_state), (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R. 
Proof. 
  intros s1 s2.
  assert (H_useful := fault_weight_state_incl s1 (state_union s1 s2)).
  spec H_useful.
  red. unfold state_union.
  assert (H_useful' := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_useful' as [_ useful]. intros x H_in.
  spec useful x. spec useful. unfold messages_union.
  rewrite in_app_iff. tauto.
  assumption.
  replace (state_union s2 s1) with (state_union s1 s2) by apply state_union_comm.
  assumption. 
Qed.


End Fault_Weights.
