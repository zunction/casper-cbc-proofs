Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.

Inductive add_in_sorted : message -> state -> state -> Prop :=
   | add_in_Empty : forall msg,
          add_in_sorted msg Empty (next msg Empty)
   | add_in_Next_eq : forall msg sigma,
          add_in_sorted msg (next msg sigma) (next msg sigma)
   | add_in_Next_lt : forall msg msg' sigma,
          msg_lt msg msg' ->  
          add_in_sorted msg (next msg' sigma) (next msg (next msg' sigma))
   | add_in_Next_gt : forall msg msg' sigma sigma',
          msg_lt msg' msg ->
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
  ; clear AddA; subst.
  - reflexivity.
Qed.

Lemma no_confusion_add_in_sorted_empty : forall msg sigma,
  ~ add_in_sorted msg sigma Empty.
Proof.
  unfold not. intros msg sigma Hadd.
  inversion Hadd as
    [ msg1 A B C 
    | msg1 sig1 A B C
    | msg1 sig1 sig2 H1 A B C
    | msg1 sig1 sig2 H1 H2 A B D C
    ]
  ; subst
  ; apply no_confusion_next_empty in C
  ; assumption.
Qed.

Theorem add_in_sorted_functional : forall msg sigma1 sigma2 sigma2',
  add_in_sorted msg sigma1 sigma2 ->
  add_in_sorted msg sigma1 sigma2' ->
  sigma2 = sigma2'.
Proof.
  intros. generalize dependent msg. generalize dependent sigma2. generalize dependent sigma2'.
  induction sigma1 as [ | c1 v1 j1 _ ] ; intros sigma2' sigma2 [(c, v) j] AddA AddB.
  - inversion AddA as 
    [ [(ca, va) ja] A AEmpty C
    | [(ca, va) ja] sigmaA A ANext C
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA smsg smsg' smsg1
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddA' A B C]
    ; clear AddA; subst.
    inversion AddB as 
    [ [(cb, vb) jb] A BEmpty C
    | [(cb, vb) jb] sigmaB A BNext C
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB LTB A B C
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB sigmaB' LTB AddB' A B C]
    ; clear AddB; subst.
    reflexivity.
  - inversion AddA as 
    [ [(ca, va) ja] AA AEmpty AC
    | [(ca, va) ja] sigmaA AA ANext AC
    | [(ca, va) ja] [(ca', va') ja'] sigmaA LTA AA AB AC
    | [(ca, va) ja] [(ca', va') ja'] sigmaA sigmaA' LTA AddA' AA AB AC]
    ; inversion AddB as 
    [ [(cb, vb) jb] BA BEmpty BC
    | [(cb, vb) jb] sigmaB BA BNext BC
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB LTB BA BB BC
    | [(cb, vb) jb] [(cb', vb') jb'] sigmaB sigmaB' LTB AddB' BA BB BC]
    ;  clear AddA; clear AddB; subst
    ; try reflexivity
    ; try (apply (msg_lt_transitive _ _ _ LTA) in LTB)
    ; try (destruct (msg_lt_irreflexive _ LTB))
    ; try (destruct (msg_lt_irreflexive _ LTA)).
    apply (IHsigma1_1 _ _ _ AddA') in AddB'; subst.
    reflexivity.
Qed.

Theorem add_in_sorted_total : forall msg sigma,
  exists sigma', add_in_sorted msg sigma sigma'.
Proof.
  intros. generalize dependent msg.
  induction sigma as [ | sc sv sj _ ] 
  ; intros [(c, v) j]
  ; try (rewrite add_is_next in *).
  - exists (next (c,v,j) Empty). apply add_in_Empty.
  - destruct (msg_lt_total_order (c,v,j) (sc,sv,sj)) as [Heq | [LT | GT]].
    + inversion Heq; subst. exists (next (sc,sv,sj) sigma1).
      apply add_in_Next_eq.
    + exists (next (c,v,j) (next (sc, sv, sj) sigma1)).
      apply add_in_Next_lt. apply LT.
    + destruct (IHsigma1 (c, v, j)) as [sigma1' Hsigma1'].
      exists (next (sc, sv, sj) sigma1').
      apply add_in_Next_gt; assumption.
Qed.
