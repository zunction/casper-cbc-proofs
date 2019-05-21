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


Definition locally_sorted_msg (msg : message) : Prop :=
  locally_sorted (next msg Empty).

Lemma locally_sorted_msg_justification : forall c v j,
  locally_sorted_msg (c,v,j) <-> locally_sorted j.
Proof.
  intros; split; intro.
  - inversion H; subst; assumption.
  - apply LSorted_Singleton. assumption.
Qed.

Lemma locally_sorted_head : forall msg sigma,
  locally_sorted (next msg sigma) ->
  locally_sorted_msg msg.
Proof.
  intros [(c, v) j] sigma H. inversion H; subst; apply locally_sorted_msg_justification; assumption.
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


Theorem add_in_sorted_sorted : forall msg sigma sigma',
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
  ; apply locally_sorted_msg_justification in LSmsg as LSj
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
  inversion H as
    [ M 
    | c v j Hj M 
    | c v j msg' gamma Hj LT LocS M 
    ]
   ; subst
   ; try ( rewrite add_is_next in *
         ; apply no_confusion_next in M
         ; destruct M; subst
         ; constructor
         ; assumption
         )
   .
  - destruct msg as [(sc, sv) sj].
    rewrite <- add_is_next in M. inversion M.
Qed.


