Require Import Casper.full_states.
Require Import Casper.full_messages.
Require Import Casper.FullStates.add_in_sorted.

(** (Locally) Sorted states **)
Inductive locally_sorted : state -> Prop :=
  | LSorted_Empty : locally_sorted Empty
  | LSorted_Singleton : forall c v j,
          locally_sorted j ->
          locally_sorted (next (c, v, j) Empty)
  | LSorted_Next : forall c v j msg' sigma, 
          locally_sorted j  ->
          msg_lt (c, v, j) msg' -> 
          locally_sorted (next msg' sigma) -> 
          locally_sorted (next (c, v, j) (next msg' sigma))
  .

Lemma locally_sorted_head : forall c v j sigma,
  locally_sorted (next (c,v,j) sigma) ->
  locally_sorted j.
Proof.
  intros. inversion H; subst; assumption.
Qed.

Lemma locally_sorted_tail : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted sigma.
Proof.
  intros.
  inversion H; subst; clear H
  ; try (rewrite add_is_next in *; apply no_confusion_next in H0; destruct H0; subst)
  .
  - exfalso. symmetry in H1. apply (no_confusion_next_empty _ _ H1) . 
  - constructor.
  - assumption. 
Qed.


Theorem add_in_sorted_sorted : forall c v j sigma sigma',
  locally_sorted sigma ->
  locally_sorted j ->
  add_in_sorted (c, v, j) sigma sigma' -> locally_sorted sigma'.
Proof.
  intros c v j sigma sigma' Hsorted. 
  generalize dependent sigma'.
  generalize dependent j. generalize dependent v. generalize dependent c.
  induction Hsorted as
  [
  | sc sv sj LSsj
  | sc sv sj [(sc', sv') sj'] ssigma LSsj _  LT LSs
  ]
  ; intros c v j sigma' LSj AddA
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
  - apply add_in_empty in AddB. subst. apply LSorted_Next; try assumption; constructor. assumption.
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
      apply (IHLSs c v j _); try assumption.
      apply add_in_Next_gt; assumption.
Qed.
