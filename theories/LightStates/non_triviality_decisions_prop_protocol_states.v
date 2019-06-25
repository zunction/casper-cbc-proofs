Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.messages.
Require Import Casper.LightStates.fault_weights.
Require Import Casper.LightStates.threshold.
Require Import Casper.LightStates.states.
Require Import Casper.LightStates.hash_state.
Require Import Casper.LightStates.protocol_states.
Require Import Casper.LightStates.consistent_decisions_prop_protocol_states.

Definition non_trivial (p : state -> Prop) :=
  (exists sigma1, protocol_state sigma1 /\ decided_state p sigma1)
  /\
  (exists sigma2, protocol_state sigma2 /\ decided_state (predicate_not p) sigma2).

Definition potentially_pivotal (v : V) : Prop :=
    exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= t)%R /\
      (sum_weights vs > t - weight v)%R
      .

Lemma exists_pivotal_validator : exists v, potentially_pivotal v.
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

Theorem non_triviality_decisions_on_properties_of_protocol_states :
  exists p, non_trivial p.
Proof.
  destruct exists_pivotal_validator as [v [vs [Hnodup [Hvnin [Hlte Hgt]]]]].
  destruct (exist_equivocating_messages (v :: vs))
    as [j1 [j2 [Hj1ps [Hj2ps [Hneq12 [c1 [c2 [Hval1 [Hval2 Heqv]]]]]]]]]
  ; try (intro H; inversion H).
  exists (In (c1,v,hash_state j1)).
  split.
  - exists [(c1,v, hash_state j1)].
    split. 
    + apply (protocol_state_singleton c1 v) in Hval1; try assumption.
    + intros sigma H.
      destruct H as [_ [_ Hincl]]. apply Hincl. left. reflexivity.
  - exists ((c2, v, hash_state j2) :: flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
    split.
    + apply protocol_state_cons with c2 v j2; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply binary_justification_protocol_state; try assumption.
        unfold fault_tolerance_condition.
        apply Rle_trans with (sum_weights (set_map v_eq_dec sender (flat_map (fun v0 : V => [(c1, v0, hash_state j1); (c2, v0, hash_state j2)]) vs)))
        ; try apply fault_weight_max.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        intros x Hin.
        apply set_map_exists in Hin.
        destruct Hin as [[(mc, mv) mj] [Hin Hveq]]. simpl in Hveq. subst.
        apply in_flat_map in Hin.
        destruct Hin as [mv [Hinv Hinm]].
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * constructor; try (apply binary_justification_nodup; assumption).
        rewrite in_flat_map. intro.
        destruct H as [v'' [Hinv Hinm]].
        apply Hvnin.
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * unfold fault_tolerance_condition.
        unfold fault_weight_state.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        unfold equivocating_senders.
        intros v0 Hinv0.
        apply set_map_exists in Hinv0.
        destruct Hinv0 as [[(c0, v0') j0] [Hin Heq]].
        simpl in Heq; subst.
        apply filter_In in Hin.
        destruct Hin as [Hin Hequiv].
        destruct Hin as [Heq | Hin]
        ; try (
          apply in_flat_map in Hin
          ; destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
          ; inversion Hin; subst; clear Hin; assumption
        ).
        inversion Heq; subst; clear Heq. simpl in Hequiv.
        unfold equivocating_messages in Hequiv.
        rewrite eq_dec_if_true in Hequiv; try reflexivity.
        simpl in Hequiv.
        apply existsb_exists in Hequiv.
        destruct Hequiv as [[(mc, mv) mj] [Hin Hequiv]].
        apply in_flat_map in Hin.
        unfold equivocating_messages in Hequiv.
        destruct ( message_eq_dec (c0, v0, hash_state j2) (mc, mv, mj))
        ; try discriminate.
        destruct (v_eq_dec v0 mv); try discriminate; subst.
        destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
          ; inversion Hin; subst; clear Hin; assumption.
    + intros sigma Hincl. intro Hin.
      destruct Hincl as [Hps [Hpssigma Hinc]].
      apply protocol_state_fault_tolerance in Hpssigma.
      apply (fault_tolerance_condition_subset ((c1, v, hash_state j1) :: ((c2, v, hash_state j2) :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs))) in Hpssigma.
      * unfold fault_tolerance_condition in Hpssigma. unfold fault_weight_state in Hpssigma.
        assert (Heq : ((c1, v, hash_state j1)
             :: (c2, v, hash_state j2)
                :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)
               = flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (v :: vs))
        ; try reflexivity.
        rewrite Heq in Hpssigma.
        apply (Rplus_gt_compat_r (weight v)) in Hgt. unfold Rminus in Hgt.
        rewrite Rplus_assoc in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt. apply Rgt_lt in Hgt.
        apply (Rle_lt_trans _ _ _ Hpssigma) in Hgt.
        { apply (Rle_lt_trans (sum_weights (v :: vs))) in Hgt.
          - rewrite Rplus_comm in Hgt. simpl in Hgt. apply Rlt_irrefl with (weight v + sum_weights vs)%R.
            assumption.
          - apply sum_weights_incl.
            + constructor; assumption.
            + apply set_map_nodup.
            + intros v0 Hin0. unfold equivocating_senders.
              apply set_map_exists. exists (c1, v0, hash_state j1).
              split; try reflexivity.
              apply filter_In.
              split.
              * apply in_flat_map.
                exists v0. split; try assumption.
                left; reflexivity.
              * apply existsb_exists. exists (c2, v0, hash_state j2).
                split; try (apply Heqv; assumption).
                apply in_flat_map.
                exists v0. split; try assumption. right; left; reflexivity.
      }
    * intros msg Hinm. 
      destruct Hinm as [Heq | Hinm]; subst; try assumption.
      apply Hinc. assumption.
Qed.
