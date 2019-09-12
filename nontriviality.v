Require Import Bool Reals List ListSet.
Import ListNotations.
From Casper
Require Import preamble ListSetExtras protocol_eq fullnode_eq.

Section Protocol. 
  Variables (C V : Type). 
  Context (about_C : `{StrictlyComparable C})
          (about_V : `{StrictlyComparable V}).

  Definition state := state C V. 

  Definition non_trivial_state (p : state -> Prop) :=
  (exists sigma1, prot_state sigma1 /\ decided sigma1 p)
  /\
  (exists sigma2, prot_state sigma2 /\ decided sigma2 (predicate_not p)).

Definition potentially_pivotal (v : validators) : Prop :=
    exists (vs : list validators),
      NoDup vs /\
      ~In v vs /\
      (sum_weight_state vs <= t)%R /\
      (sum_weights vs > t - weight v)%R.

Definition at_least_two_validators : Prop :=
  forall v1 : validators, exists v2 : validators, v1 <> v2.

Lemma sufficient_validators_pivotal_ind : forall vss,
  NoDup vss ->
  (sum_weights vss > t)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights vs > t)%R /\
  exists v,
    In v vs /\
    (sum_weights (set_remove v_eq_dec v vs) <= t)%R.
Proof.
  induction vss; intros.
  simpl in H0.
  - exfalso. apply (Rge_gt_trans t) in H0; try apply threshold_nonnegative.
    apply Rgt_not_eq in H0. apply H0. reflexivity.
  - simpl in H0. destruct (Rtotal_le_gt (sum_weights vss) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + apply NoDup_cons_iff in H. destruct H as [Hnin Hvss]. apply IHvss in H1; try assumption.
      destruct H1 as [vs [Hvs [Hincl H]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.

Lemma sufficient_validators_pivotal :
  exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > t)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove v_eq_dec v vs) <= t)%R.
Proof.
  destruct sufficient_validators_condition as [vs [Hvs Hweight]].
  apply (sufficient_validators_pivotal_ind vs Hvs) in  Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  exists vs'. repeat (split; try assumption).
Qed.

Lemma exists_pivotal_message : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists v.
  subst. exists (set_remove v_eq_dec v vs). repeat split.
  - apply set_remove_nodup. assumption.
  - intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
  - assumption.
  - rewrite (sum_weights_in v) in Hgt; try assumption.
    rewrite Rplus_comm in Hgt.
    apply (Rplus_gt_compat_r (- weight v)%R) in Hgt.
    rewrite Rplus_assoc in Hgt.
    rewrite Rplus_opp_r in Hgt.
    rewrite Rplus_0_r in Hgt.
    assumption.
Qed.

Definition valid_protocol_state (sigma : state) (csigma cempty : consensus_values) (vs : list validators) : state :=
  fold_right
    (fun v sigma' =>
      add_in_sorted_fn (csigma, v, sigma) (add_in_sorted_fn (cempty, v, Empty) sigma'))
    sigma
    vs.

Lemma in_valid_protocol_state : forall msg sigma csigma cempty vs,
  in_state msg (valid_protocol_state sigma csigma cempty vs) ->
  in_state msg sigma \/
  exists v, In v vs /\ (msg = (csigma, v, sigma) \/ (msg = (cempty, v, Empty))).
Proof.
  intros. induction vs.
  - simpl in H. left. assumption.
  - simpl in H. rewrite in_state_add_in_sorted_iff in H. rewrite in_state_add_in_sorted_iff in H.
    destruct H as [Heq | [Heq | Hin]];
    try (right; exists a; split; try (left; reflexivity); (left; assumption) || (right; assumption)).
    apply IHvs in Hin. destruct Hin; try (left; assumption). right.
    destruct H as [v [Hin H]].
    exists v. split; try assumption. right; assumption.
Qed.

Lemma in_valid_protocol_state_rev_sigma : forall sigma csigma cempty vs,
  syntactic_state_inclusion sigma (valid_protocol_state sigma csigma cempty vs).
Proof.
  intros. intros msg Hin.
  induction vs.
  - assumption.
  - simpl. apply in_state_add_in_sorted_iff. right.
    apply in_state_add_in_sorted_iff. right.
    assumption.
Qed.

Lemma in_valid_protocol_state_rev_csigma : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (csigma, v, sigma) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Lemma in_valid_protocol_state_rev_cempty : forall sigma csigma cempty vs,
  forall v,
  In v vs ->
  in_state (cempty, v, Empty) (valid_protocol_state sigma csigma cempty vs).
Proof.
  induction vs; intros.
  - inversion H.
  - destruct H as [Heq | Hin].
    + subst. simpl. apply in_state_add_in_sorted_iff. right.
       apply in_state_add_in_sorted_iff. left. reflexivity.
    + simpl. apply in_state_add_in_sorted_iff. right. 
      apply in_state_add_in_sorted_iff. right.  apply IHvs. assumption.
Qed.

Lemma valid_protocol_state_equivocating_senders :
  forall cempty,
  estimator Empty cempty ->
  forall v vs,
  ~ In v vs ->
  forall csigma,
  estimator (next (cempty, v, Empty) Empty) csigma ->
  set_eq (equivocating_senders (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty vs)) vs.
Proof.
  intros.
  remember (next (cempty, v, Empty) Empty) as sigma.
  remember (valid_protocol_state sigma csigma cempty vs) as sigma2.
  unfold equivocating_senders. split; intros; intros x Hin.
  - apply (set_map_exists v_eq_dec sender)  in Hin.
    destruct Hin as [[(cx, vx) jx] [Hin Hsend]].
    simpl in Hsend. rewrite <- Hsend.
    apply filter_In in Hin. destruct Hin as [Hin Hequiv].
    apply existsb_exists in Hequiv.
    destruct Hequiv as [[(cy, vy) jy] [Hiny Hequiv]].
    rewrite Heqsigma2 in Hin.
    apply in_valid_protocol_state in Hin.
    destruct Hin as [Hin | [vv [Hin [Heq | Heq]]]]; try (inversion Heq; subst; assumption).
    exfalso. unfold equivocating_messages in Hequiv.
    rewrite Heqsigma in Hin. apply in_singleton_state in Hin.
    rewrite Heqsigma2 in Hiny.
    apply in_valid_protocol_state in Hiny.
    destruct Hiny as [Hiny | [vv [Hiny [Heq | Heq]]]].
    + rewrite Heqsigma in Hiny. apply in_singleton_state in Hiny.
      rewrite Hin in Hequiv. rewrite Hiny in Hequiv.
      rewrite eq_dec_if_true in Hequiv; try reflexivity.
      inversion Hequiv.
    + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
      rewrite eq_dec_if_false in Hequiv.
      * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
        intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
        apply H0. assumption.
      * intro. inversion H2; subst; clear H2. apply H0. assumption.
    + rewrite Hin in Hequiv. rewrite Heq in Hequiv.
      rewrite eq_dec_if_false in Hequiv.
      * rewrite eq_dec_if_false in Hequiv; try inversion Hequiv.
        intro; subst. inversion Hin; subst; clear Hin. inversion Heq; subst; clear Heq.
        apply H0. assumption.
      * intro. inversion H2; subst; clear H2. apply H0. assumption.
  - apply (set_map_exists v_eq_dec sender).
    exists (cempty, x, Empty). simpl. split; try reflexivity.
    apply filter_In. split.
    + rewrite Heqsigma2. apply in_valid_protocol_state_rev_cempty. assumption.
    + apply existsb_exists. exists (csigma, x, sigma). split.
      * rewrite Heqsigma2. apply in_valid_protocol_state_rev_csigma. assumption.
      * unfold equivocating_messages.
        { rewrite eq_dec_if_false.
          - rewrite eq_dec_if_true; try reflexivity. apply andb_true_iff. split.
            + apply negb_true_iff. unfold in_state_fn. 
              rewrite in_state_dec_if_false; try reflexivity.
              rewrite Heqsigma. intro. apply in_singleton_state in H2.
              apply H0. inversion H2; subst; clear H2. assumption.
            + apply negb_true_iff. unfold in_state_fn. 
              rewrite in_state_dec_if_false; try reflexivity.
              apply in_empty_state.
          - intro. inversion H2; subst. inversion H5.
        }
Qed.

Lemma valid_protocol_state_ps :
  forall cempty,
  estimator Empty cempty ->
  forall vs,
  NoDup vs ->
  (sum_weights vs <= t)%R ->
  forall v,
  ~ In v vs ->
  forall csigma,
  estimator (next (cempty, v, Empty) Empty) csigma ->
  protocol_state (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty vs).
Proof.
  intros. induction vs.
  - simpl. apply protocol_state_singleton. assumption.
  - simpl. constructor.
    + apply protocol_state_singleton. assumption.
    + constructor.
      * constructor.
      * { apply IHvs.
        - apply NoDup_cons_iff in H0. destruct H0. assumption.
        - simpl in H1. apply Rle_trans with (weight a + sum_weights vs)%R; try assumption.
          rewrite <- (Rplus_0_l (sum_weights vs))  at 1.
          apply Rplus_le_compat_r.
          apply Rge_le. left. apply weight_positive.
        - intro.  apply H2. right. assumption.
        }
      * intro. simpl. intro. inversion H4.
      * assumption.
      * unfold fault_tolerance_condition. unfold fault_weight_state.
        apply Rle_trans with (sum_weights (a :: vs)); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        rewrite add_is_next.
        remember (next (cempty, v, Empty) Empty) as sigma.
        remember (valid_protocol_state sigma csigma cempty vs) as sigma2.
        { apply incl_tran with (equivocating_senders sigma2).
        - apply set_eq_proj1. apply equivocating_senders_single.
          intro. apply set_map_exists in H4.
          destruct H4 as [[(cx, vx) jx] [Hin Heq]].
          simpl in Heq. rewrite Heq in Hin. clear Heq.
          rewrite Heqsigma2 in Hin. apply in_valid_protocol_state in Hin.
          destruct Hin.
          + rewrite Heqsigma in H4. apply in_singleton_state in H4.
            apply H2. inversion H4. left; reflexivity.
          + destruct H4 as [vv [Hin Heq]]. apply NoDup_cons_iff in H0.
            destruct H0 as [Hnin Hnodup]. apply Hnin.
            destruct Heq as [Heq | Heq]; inversion Heq; subst; assumption.
        - apply incl_tran with vs.
          + apply set_eq_proj1. subst.
            apply valid_protocol_state_equivocating_senders; try assumption.
            intro. apply H2. right. assumption.
          + intros x Hin. right. assumption.
        }
    + intros msg Hin. simpl in Hin.
      destruct Hin as [Heq | Hcontra]; try inversion Hcontra; subst.
      apply in_state_add_in_sorted_iff. right.
      rewrite add_is_next.
      apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
    + assumption.
    + unfold fault_tolerance_condition. unfold fault_weight_state.
      apply Rle_trans with (sum_weights (a :: vs)); try assumption.
      apply sum_weights_incl; try assumption; try apply set_map_nodup.
      apply incl_tran with (equivocating_senders (valid_protocol_state (next (cempty, v, Empty) Empty) csigma cempty (a :: vs)))
      ; try  apply incl_refl.
      apply set_eq_proj1.
      apply valid_protocol_state_equivocating_senders; try assumption.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  at_least_two_validators ->
  exists p, non_trivial_state p.
Proof.
  intro H2v.
  destruct exists_pivotal_message as [v Hpivotal].
  destruct (estimator_total Empty) as [c Hc].
  destruct Hpivotal as [vs [Hnodup [Hnin [Hlt Hgt]]]].
  destruct vs as [ | v' vs].
  - exists (in_state (c,v,Empty)).
    split.
    + exists (next (c,v,Empty) Empty); split; try apply protocol_state_singleton; try assumption.
      intros sigma H. destruct H as [HLS1 [HLS2 H]]. apply H. simpl. left. reflexivity.
    + destruct (H2v v) as [v' Hv'].
      remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0).
      { subst. apply protocol_state_singleton. assumption. }
      destruct (estimator_total sigma0) as [c0 Hc0].
      exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      intro.
      apply protocol_state_fault_tolerance in Hps' as Hft'.
      unfold fault_tolerance_condition in Hft'.
      assert (Hnft' : (fault_weight_state sigma' > t)%R).
      { apply Rlt_le_trans with (fault_weight_state (add (c, v, Empty) to (add (c0, v, sigma0) to Empty))).
        - unfold fault_weight_state. unfold equivocating_senders. simpl.
          assert ( Hequiv : equivocating_message_state (c, v, Empty)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c0, v, sigma0). 
            split.
            - right. left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv.
          assert ( Hequiv0 : equivocating_message_state (c0, v, sigma0)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c, v, Empty). 
            split.
            - left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv0. simpl. rewrite eq_dec_if_true; try reflexivity.
          simpl. simpl in Hgt. unfold Rminus in Hgt.
          apply (Rplus_gt_compat_r (weight v)) in Hgt. rewrite Rplus_assoc in Hgt.
          rewrite Rplus_0_r. rewrite Rplus_0_l in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt.
          apply Rgt_lt. assumption.
        - apply fault_weight_state_incl. unfold syntactic_state_inclusion. simpl.
          intros x Hin. destruct Hin as [Hin | [Hin | Hcontra]]; try inversion Hcontra; subst
          ; try assumption.
          apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
      }
      unfold Rgt in Hnft'. apply (Rlt_irrefl t).
      apply Rlt_le_trans with (fault_weight_state sigma'); assumption.
  - remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
    assert (Hps0 : protocol_state sigma0).
    { subst. apply protocol_state_singleton. assumption. }
    destruct (estimator_total sigma0) as [c0 Hc0].
    exists (in_state (c0,v,sigma0)).
    split.
    + exists (add_in_sorted_fn (c0, v, sigma0) sigma0).
      split; try (apply extend_protocol_state; assumption).
      intros sigma' H'. destruct H' as [_ [Hps' Hincl]].
      apply Hincl. apply in_state_add_in_sorted_iff. left. reflexivity.
    + remember (add_in_sorted_fn (c, v, Empty) Empty) as sigma.
      simpl in Heqsigma. rewrite add_is_next in Heqsigma.
      destruct (estimator_total sigma) as [csigma Hcsigma].
      remember (valid_protocol_state sigma csigma c (v' :: vs)) as sigma2.
      assert (Hequiv2 : set_eq (equivocating_senders sigma2) (v' :: vs)). 
      { rewrite Heqsigma2. rewrite Heqsigma in *.
        apply valid_protocol_state_equivocating_senders; assumption.
      }
      exists sigma2. split.
      * subst. apply valid_protocol_state_ps; assumption.
      * unfold decided_state. intros sigma' Hfutures.
        unfold predicate_not. intro Hin.
        destruct Hfutures as [Hps2 [Hps' Hincl]].
        apply protocol_state_fault_tolerance in Hps'.
        { apply (fault_tolerance_condition_subset (add (c0, v, sigma0) to sigma2)) in Hps'.
        - unfold fault_tolerance_condition in Hps'.
          apply Rlt_irrefl with t.
          apply Rlt_le_trans with (fault_weight_state (add (c0, v, sigma0)to sigma2)); try assumption.
          unfold fault_weight_state.
          unfold Rminus in Hgt. apply (Rplus_gt_compat_r (weight v)) in Hgt.
          rewrite Rplus_assoc in Hgt. rewrite Rplus_opp_l, Rplus_0_r in Hgt.
          apply Rgt_lt. apply Rge_gt_trans with (sum_weights (v' :: vs) + weight v)%R; try assumption.
          rewrite Rplus_comm.
          assert (Hsum : (weight v + sum_weights (v' :: vs))%R = sum_weights (v :: v' :: vs))
          ; try reflexivity; try rewrite Hsum.
          apply Rle_ge. apply sum_weights_incl; try apply set_map_nodup; try (constructor; assumption).
          intros vv Hvin. unfold equivocating_senders.
          apply set_map_exists.
          exists (c, vv, Empty).
          split; try reflexivity.
          apply filter_In.
          split; destruct Hvin as [Heq | Hvin]; subst; apply existsb_exists || right.
          + apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
          + apply in_valid_protocol_state_rev_cempty; assumption.
          + exists (c0, vv, add_in_sorted_fn (c, v', Empty) Empty).
            split ; try (left; reflexivity).
            simpl. unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
            ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * rewrite add_is_next in H. apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. left. reflexivity.
            * inversion H.
            * intro. inversion H.
          + exists (csigma, vv, (next (c, v, Empty) Empty)). split
            ; try (right; apply in_valid_protocol_state_rev_csigma; assumption).
            unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
            ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. assumption.
            * inversion H.
            * intro. inversion H.
        - intros msg Hmin.
          destruct Hmin as [Heq | Hmin].
          * subst. assumption.
          * apply Hincl. assumption.
   }
Qed.

End Non_triviality_Properties_Protocol_States.
