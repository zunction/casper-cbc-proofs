Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts Classical Sorting.
Import ListNotations.    
From Casper  
Require Import preamble ListExtras ListSetExtras sorted_lists protocol RealsExtras .


Variables (C V : Type).
Variables (about_C : `{StrictlyComparable C})
          (about_V : `{StrictlyComparable V}). 

Parameter two_senders : exists (v1 v2 : V), v1 <> v2.

Definition pos_R := {r : R | (r > 0)%R}.

Parameter weight : V -> pos_R.

Definition sum_weights (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l. 


Parameters (t_full : {r | (r >= 0)%R})
           (suff_val_full : exists vs, NoDup vs /\ (sum_weights vs > (proj1_sig t_full))%R).



Lemma distinct_sender_total : forall v1 : V, exists v2 : V, v1 <> v2.
Proof.
  intros.
  destruct two_senders  as [v1' [v2' Hneq]].
  destruct (compare_eq_dec v1 v1') eqn:Heq.
  - subst. exists v2'. assumption.
  - exists v1'. assumption.
Qed.

Definition get_distinct_sender (v : V) :=
  proj1_sig (choice V (fun v' => v <> v') (distinct_sender_total v)).

Definition get_distinct_sender_correct (v : V) :=
  proj2_sig (choice V (fun v' => v <> v') (distinct_sender_total v)).

Lemma get_distinct_sender_correct' :
  forall v, get_distinct_sender v <> v. 
Proof.
  intros. unfold get_distinct_sender.
  assert (H_useful := get_distinct_sender_correct v).
  simpl in *.
  intro H_absurd.
  apply H_useful; symmetry; assumption.
Qed.

Definition weight_proj1_sig (w : pos_R) : R := proj1_sig w.

Coercion weight_proj1_sig : pos_R >-> R.


Lemma sum_weights_in : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove compare_eq_dec v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (eq_dec_left compare_eq_dec v). rewrite H. reflexivity.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (compare_eq_dec v a); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc. 
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
    destruct (in_dec compare_eq_dec a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup compare_eq_dec a). assumption.
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
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. destruct weight. simpl. auto. 
Qed.

Lemma sum_weights_app : forall vs vs',
  sum_weights (vs ++ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  induction vs; intros; simpl.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite IHvs. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma pivotal_validator_extension : forall vsfix vss,
  NoDup vsfix ->
  (* and whose added weight does not pass the threshold *)
  (sum_weights vsfix <= proj1_sig t_full)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights (vss ++ vsfix) > proj1_sig t_full)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights (vs ++ vsfix) > proj1_sig t_full)%R /\
  exists v,
    In v vs /\
    (sum_weights ((set_remove compare_eq_dec v vs) ++ vsfix) <= proj1_sig t_full)%R.
Proof.
  destruct t_full as [t about_t]; simpl in *.
  intro.  induction vss; intros.
  - simpl in H2. exfalso. apply (Rge_gt_trans t) in H2; try (apply Rle_ge; assumption).
    apply Rgt_not_eq in H2. apply H2. reflexivity.
  - simpl in H2. destruct (Rtotal_le_gt (sum_weights (vss ++ vsfix)) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply append_nodup_left in H1. assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + simpl in H1. apply NoDup_cons_iff in H1. destruct H1 as [Hnin Hvss]. apply IHvss in H3; try assumption.
      destruct H3 as [vs [Hvs [Hincl Hex]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.


(* From threshold.v *)
Lemma validators_pivotal_ind : forall vss,
  NoDup vss ->
  (sum_weights vss > proj1_sig t_full)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights vs > proj1_sig t_full)%R /\
  exists v,
    In v vs /\
    (sum_weights (set_remove compare_eq_dec v vs) <= proj1_sig t_full)%R.
Proof.
  intros.
  rewrite <- (app_nil_r vss) in H.   rewrite <- (app_nil_r vss) in H0.
  apply (pivotal_validator_extension [] vss) in H0; try assumption.
  - destruct H0 as [vs [NoDupvs [Inclvs [Gt [v [Inv Lt]]]]]].
    rewrite app_nil_r in Lt. rewrite app_nil_r in Gt.
    exists vs. repeat (split; try assumption).
    exists v. repeat (split; try assumption).
  - constructor.
  - destruct t_full as [t about_t]; simpl in *.
    apply Rge_le; assumption.
Qed.

Lemma sufficient_validators_pivotal :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > proj1_sig t_full)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove compare_eq_dec v vs) <= proj1_sig t_full)%R.
Proof.
  destruct suff_val_full as [vs [Hvs Hweight]].
  apply (validators_pivotal_ind vs Hvs) in Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  destruct t_full as [t about_t]; simpl in *.
  exists vs'. repeat (split; try assumption).
Qed.

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= proj1_sig t_full)%R /\
      (sum_weights vs > proj1_sig t_full - (proj1_sig (weight v)))%R.

Lemma exists_pivotal_validator : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists v.
  subst. exists (set_remove compare_eq_dec v vs). repeat split.
  - apply set_remove_nodup. assumption.
  - intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
  - assumption.
  - rewrite (sum_weights_in v) in Hgt; try assumption.
    rewrite Rplus_comm in Hgt.
    apply (Rplus_gt_compat_r (- (proj1_sig (weight v))%R)) in Hgt.
    rewrite Rplus_assoc in Hgt.
    rewrite Rplus_opp_r in Hgt.
    rewrite Rplus_0_r in Hgt.
    assumption.
Qed.
