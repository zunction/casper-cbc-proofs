Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

From Casper
Require Import preamble.
From Casper
Require Import sorted_lists.


(**
  TODO: Prove that all Inductive defining functions yield total functions.
  This is important, as if the functions are not total we might have empty
  hypothesis.
**)


(** Parameters of the protocol **)

(***************************************)
(** Non-empty set of consensus values **)
(***************************************)

Variable C : Set .

Axiom C_non_empty : exists c : C, True.

(** Less than order on consensus values **)

Variable c_lt : C -> C -> Prop.

Axiom c_lt_strict_order: StrictOrder c_lt.

(** C totally ordered **)

Axiom c_lt_total_order: TotalOrder c_lt.

Corollary C_eq_dec : forall x y : C, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with c_lt.
  - apply c_lt_strict_order.
  - apply c_lt_total_order.
Qed.

(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Variable V : Set .

Axiom V_non_empty : exists v : V, True.

(** Less than order on validator names **)

Variable v_lt : V -> V -> Prop.

Axiom v_lt_strict_order: StrictOrder v_lt.

(** V totally ordered **)

Axiom v_lt_total_order: TotalOrder v_lt.

Corollary V_eq_dec : forall x y : V, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with v_lt.
  - apply v_lt_strict_order.
  - apply v_lt_total_order.
Qed.

(***********************)
(** Validator weights **)
(***********************)

Variable weight : V -> R.

Axiom weight_positive : forall v : V, (weight v > 0)%R.


(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Variable t : R.

Axiom threshold_nonnegative : (t >= 0)%R .

(** TODO: Strictly smaller than the total validator weigths **)


(************)
(** States **)
(************)

Inductive state : Set :=
  | Empty : state
  | Next : C ->  V -> state -> state -> state.


Notation "'add' ( c , v , msg ) 'to' sigma" :=
  (Next c v msg sigma)
  (at level 20).

(***************)
(** Estimator **)
(***************)

Variable epsilon : state -> C -> Prop.

Axiom epsilon_total : forall s : state, exists c : C, epsilon s c.


(********************)
(* State properties *)
(********************)

Inductive state_lt : state -> state -> Prop :=
  | state_lt_Empty : forall c v j sigma, 
      state_lt Empty (add (c,v,j) to sigma)
  | state_lt_C : forall c1 c2 v1 v2 j1 j2 sigma1 sigma2,
      c_lt c1 c2 ->
      state_lt (add (c1,v1,j1) to sigma1) (add (c2,v2,j2) to sigma2)
  | state_lt_V : forall c v1 v2 j1 j2 sigma1 sigma2,
      v_lt v1 v2 -> 
      state_lt (add (c,v1,j1) to sigma1) (add (c,v2,j2) to sigma2)
  | state_lt_M : forall c v j1 j2 sigma1 sigma2,
      state_lt j1 j2 ->
      state_lt (add (c,v,j1) to sigma1) (add (c,v,j2) to sigma2)
  | state_lt_Next : forall c v j sigma1 sigma2,
      state_lt sigma1 sigma2 ->
      state_lt (add (c,v,j) to sigma1) (add (c,v,j) to sigma2)
  .

Lemma state_lt_irreflexive : Irreflexive state_lt.
Proof.
 assert (SOc : StrictOrder c_lt); try apply c_lt_strict_order.
 assert (SOv : StrictOrder v_lt); try apply v_lt_strict_order. 
 assert (EE : not(state_lt Empty Empty)); try (unfold not; intros; inversion H).
 unfold Irreflexive. unfold Reflexive. induction x.
    + apply EE.
    + unfold complement. intros. inversion H; subst.
      * destruct SOc. 
        apply StrictOrder_Irreflexive in H1. inversion H1.
      * destruct SOv. 
        apply StrictOrder_Irreflexive in H1. inversion H1.
      * apply IHx1 in H1. inversion H1.
      * apply IHx2 in H1. inversion H1.
Qed.

Lemma state_lt_transitive: Transitive state_lt.
Proof.
  assert (SOc : StrictOrder c_lt); try apply c_lt_strict_order.
  assert (SOv : StrictOrder v_lt); try apply v_lt_strict_order.
  destruct SOc as [_ Soc]. 
  destruct SOv as [_ Sov]. 
  unfold Transitive in *.
  intros. generalize dependent x. induction H0.
  - intros. inversion H.
  - intros. inversion H0; subst; try (apply state_lt_C; assumption).
    + constructor.
    + apply state_lt_C; try assumption. apply (Soc _ _ _ H3 H). 
  - intros. inversion H0; subst; try (apply state_lt_V; assumption).
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. apply (Sov _ _ _ H3 H).
  - intros; subst. inversion H; subst.
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. assumption.
    + apply state_lt_M. apply IHstate_lt. assumption.
    + apply state_lt_M. assumption. 
  - intros; subst. inversion H; subst.
    + constructor.
    + apply state_lt_C. assumption.
    + apply state_lt_V. assumption.
    + apply state_lt_M. assumption.
    + apply state_lt_Next. apply IHstate_lt. assumption.
Qed.

Lemma state_lt_strict_order : StrictOrder state_lt.
Proof.
  constructor.
  - apply state_lt_irreflexive.
  - apply state_lt_transitive.
Qed.

Theorem state_lt_total_order : TotalOrder state_lt.
Proof.
  unfold TotalOrder.
  intros. generalize dependent c2.
  induction c1.
  - induction c2.
    + left. reflexivity.
    + right. left. apply state_lt_Empty.
  - induction c2.
    + right. right. apply state_lt_Empty.
    + destruct (c_lt_total_order c c0); subst.
      * destruct (v_lt_total_order v v0); subst.
        { destruct (IHc1_1 c2_1); subst.
            { destruct (IHc1_2 c2_2); subst.
                { left. reflexivity. }
                { destruct H. 
                    { right. left. apply state_lt_Next. assumption. }
                    { right. right. apply state_lt_Next. assumption. }
                 }
             }
            {  destruct H. 
              { right. left. apply state_lt_M. assumption. }
              { right. right. apply state_lt_M. assumption. }
            }
        }
        { destruct H.
          { right. left. apply state_lt_V.  assumption. }
          { right. right. apply state_lt_V. assumption. }
        } 
     * destruct H.
        { right. left. apply state_lt_C.
          {assumption. }
        }
        { right. right. apply state_lt_C. 
          {assumption. }
        }
Qed.

Corollary state_eq_dec : forall x y : state, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with state_lt.
  - apply state_lt_strict_order.
  - apply state_lt_total_order.
Qed.

(**************)
(** Messages **)
(**************)

Definition message := (C * V * state)%type.

Definition next (msg : message) (sigma : state) : state :=
  match msg with
  | (c, v, j) => add (c, v, j) to sigma
  end.

Lemma add_is_next : forall c v j sigma,
  add (c, v, j)to sigma = next (c, v, j) sigma.
Proof.
  intros. unfold next. reflexivity.
Qed.

Lemma no_confusion_next : forall msg1 msg2 sigma1 sigma2,
  next msg1 sigma1 = next msg2 sigma2 ->
  msg1 = msg2 /\ sigma1 = sigma2.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  inversion H; subst; clear H.
  split; reflexivity.
Qed.

Lemma no_confusion_next_empty : forall msg sigma,
  next msg sigma <> Empty.
Proof.
  intros. intro. destruct msg as [(c, v) j]. inversion H.
Qed.

Definition msg_lt (msg1 msg2 : message) : Prop :=
  state_lt (next msg1 Empty) (next msg2 Empty).

Corollary msg_lt_irreflexive : Irreflexive msg_lt.
Proof.
  unfold Irreflexive. unfold Reflexive.
  destruct x as [(c, v) j].
  unfold complement. intros.
  unfold msg_lt in H. unfold next in H.
  apply state_lt_irreflexive in H. inversion H.
Qed.

Corollary msg_lt_transitive: Transitive msg_lt.
Proof.
  unfold Transitive.
  destruct x as [(c1, v1) j1].
  destruct y as [(c2, v2) j2].
  destruct z as [(c3, v3) j3].
  unfold msg_lt. unfold next.
  intros.
  apply state_lt_transitive with (add (c2, v2, j2)to Empty); assumption.
Qed.

Lemma msg_lt_strict_order : StrictOrder msg_lt.
Proof.
  constructor.
  - apply msg_lt_irreflexive.
  - apply msg_lt_transitive.
Qed.

Corollary msg_lt_total_order: TotalOrder msg_lt.
Proof.
  unfold TotalOrder. 
  unfold msg_lt.
  destruct c1 as [(c1, v1) j1].
  destruct c2 as [(c2, v2) j2].
  unfold next.
  destruct (c_lt_total_order c1 c2); subst.
  + destruct (v_lt_total_order v1 v2); subst.
    * destruct (state_lt_total_order j1 j2); subst.
      { left. reflexivity. }
      { destruct H.
          { right. left. apply state_lt_M; try reflexivity || assumption. }
          { right. right. apply state_lt_M; try reflexivity || assumption. }
      }
    * destruct H.
      { right. left. apply state_lt_V; try reflexivity || assumption. }
      { right. right. apply state_lt_V; try reflexivity || assumption. }
  + destruct H.
    * right. left. apply state_lt_C; try assumption.
    * right. right. apply state_lt_C; try assumption.
Qed.

Corollary message_eq_dec : forall x y : message, x = y \/ x <> y.
Proof.
  apply strict_total_order_eq_dec with msg_lt.
  - apply msg_lt_strict_order.
  - apply msg_lt_total_order.
Qed.



(****************************************)
(** Canonical representation of states **)
(****************************************)

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

(** Sorted states **)
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

(** State equality **)

(** Syntactic membership predicate **)
Inductive in_state : message -> state -> Prop :=
  | InState : forall msg' msg sigma, 
          msg' = msg \/ in_state msg' sigma -> 
          in_state msg' (next msg sigma)
  .

Lemma in_empty_state : forall msg,
  ~ in_state msg Empty.
Proof.
  intros. intro. inversion H; subst.
  apply no_confusion_next_empty in H0; inversion H0.
Qed.

Theorem in_state_dec : forall msg sigma, 
  in_state msg sigma \/ ~ in_state msg sigma.
Proof.
  induction sigma.
  - right. apply in_empty_state.
  - rewrite add_is_next in *.
    clear IHsigma1.
    destruct (message_eq_dec msg (c,v,sigma1)).
    + left. constructor. left. assumption.
    + destruct IHsigma2.
      * left. constructor. right. assumption.
      * right. intro. inversion H1; subst; clear H1.
        rewrite add_is_next in *.
        apply no_confusion_next in H2; destruct H2; subst.
        destruct H4; try apply (H H1); apply (H0 H1).
Qed.

Definition syntactic_state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  forall msg, in_state msg sigma1 -> in_state msg sigma2.

Lemma in_singleton_state : forall msg msg',
  in_state msg (next msg' Empty) -> msg = msg'.
Proof.
  intros.
  inversion H; subst; clear H.
  apply no_confusion_next in H0; destruct H0; subst.
  destruct H2; try assumption.
  exfalso. apply (in_empty_state _ H).
Qed.

Lemma in_sorted_state : forall sigma,
  locally_sorted sigma ->
   forall c v j,
  in_state (c, v, j) sigma ->
  locally_sorted j.
Proof.
  intros sigma H. induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - apply in_singleton_state in H0. inversion H0; subst; clear H0. assumption.
  - inversion H2; subst; clear H2. rewrite add_is_next in H3.
    apply no_confusion_next in H3; destruct H3; subst.
    destruct H5.
    + inversion H2; subst; assumption.
    + apply IHlocally_sorted2 with c0 v0; assumption.
Qed.

Theorem add_in_sorted_state_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros msg sigma sigma' H. unfold syntactic_state_inclusion.
  induction H; intros; try assumption. 
  - exfalso. apply (in_empty_state msg0 H).
  - constructor. right. assumption.
  - inversion H1; subst; clear H1.
    apply no_confusion_next in H2; destruct H2; subst.
    destruct H4; subst.
    + constructor. left. reflexivity.
    + constructor. right. apply IHadd_in_sorted.
      assumption. 
Qed.

Theorem add_in_sorted_msg_preservation : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  in_state msg sigma'.
Proof.
  intros.
  induction H; try (constructor; left; reflexivity).
  constructor. right. assumption.
Qed.

Theorem add_in_sorted_no_junk : forall msg sigma sigma',
  add_in_sorted msg sigma sigma' ->
  forall msg', in_state msg' sigma' -> msg' = msg \/ in_state msg' sigma.
Proof.
  intros msg sigma sigma' H.
  induction H as
  [ [(hc, hv) hj]
  | [(hc, hv) hj] Hsigma
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma HLT
  | [(hc, hv) hj] [(hc', hv') hj'] Hsigma Hsigma' HGT HAdd H_H 
  ]; intros [(c', v') j'] HIn
  ; inversion HIn as [[(inc, inv) inj] [(inc', inv') inj'] insigma [HInEq | HIn'] X Y ]
    ; clear HIn; subst
  ; try (right; assumption)
  ; try (left; assumption)
  . 
  - right. constructor. right. assumption.
  - inversion HInEq; clear HInEq; subst. right. constructor. left. reflexivity.
  - apply H_H in HIn'. destruct HIn' as [HInEq | HIn'].
    + left. assumption.
    + right. constructor. right. assumption.
Qed.

Lemma state_set_In : forall msg1 msg2 sigma,
  locally_sorted (next msg2 sigma) ->
  in_state msg1 sigma ->
  msg_lt msg2 msg1.
Proof.
  intros. generalize dependent msg1. generalize dependent msg2. induction sigma; intros.
  - apply in_empty_state in H0; inversion H0.
  - rewrite add_is_next in *. inversion H0; clear H0; subst. 
    rewrite add_is_next in *. apply no_confusion_next in H1. destruct H1; subst.
     destruct msg2 as [(c2, v2) j2]. inversion H; subst; clear H.
    rewrite add_is_next in *.  apply no_confusion_next in H5. destruct H5; subst.
    destruct H3; subst; try assumption.
    apply (msg_lt_transitive (c2, v2, j2) (c, v, sigma1) msg1 H6).
    apply IHsigma2; assumption.
Qed.

Lemma sorted_syntactic_state_inclusion_first_equal : forall sigma sigma' msg,
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg sigma') ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros.
  intros msg' Hin.
  apply (state_set_In _ _ _ H) in Hin as Hlt.
  assert (Hin' : in_state msg' (next msg sigma)).
  { constructor. right. assumption. }
  apply H1 in Hin'. inversion Hin'; subst; clear Hin'.
  apply no_confusion_next in H2; destruct H2; subst.
  destruct H4; try assumption.
  subst. exfalso. apply (msg_lt_irreflexive _ Hlt).
Qed.

Lemma sorted_syntactic_state_inclusion : forall sigma sigma' msg msg',
  locally_sorted (next msg sigma) ->
  locally_sorted (next msg' sigma') ->
  syntactic_state_inclusion (next msg sigma) (next msg' sigma') ->
  (msg = msg' /\ syntactic_state_inclusion sigma sigma')
  \/
  (msg_lt msg' msg /\ syntactic_state_inclusion (next msg sigma) sigma').
Proof.
  intros.
  assert (Hin : in_state msg (next msg' sigma')).
  { apply H1. constructor. left. reflexivity. }
  inversion Hin; subst; clear Hin.
  apply no_confusion_next in H2; destruct H2; subst.
  destruct H4.
  - left. subst. split; try reflexivity.
    apply sorted_syntactic_state_inclusion_first_equal with msg'; assumption.
  - right. apply (state_set_In _ _ _ H0) in H2.
    split; try assumption.
    intros msg1 Hin1.
    inversion Hin1; subst.
    apply no_confusion_next in H3; destruct H3; subst.
    destruct H5; subst.
    + apply H1 in Hin1.
      inversion Hin1; subst.
      apply no_confusion_next in H3; destruct H3; subst.
      destruct H5; subst; try assumption.
      exfalso. apply (msg_lt_irreflexive _ H2).
    + apply (state_set_In _ _ _ H) in H3.
      apply H1 in Hin1.
      inversion Hin1; subst.
      apply no_confusion_next in H4; destruct H4; subst.
      destruct H6; subst; try assumption.
      exfalso. apply (msg_lt_transitive _ _ _ H2) in H3.
      apply (msg_lt_irreflexive _ H3).
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
  - exfalso. apply (msg_lt_irreflexive _ H2).
  - exfalso. apply (msg_lt_irreflexive _ H1).
  - exfalso. apply (msg_lt_transitive _ _ _ H1) in H2. apply (msg_lt_irreflexive _ H2).
Qed.

Theorem sorted_syntactic_state_inclusion_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  syntactic_state_inclusion sigma1 sigma2 ->
  syntactic_state_inclusion sigma2 sigma1 ->
  sigma1 = sigma2.
Proof.
  induction sigma1; intros; destruct sigma2; repeat rewrite add_is_next in *.
  - reflexivity.
  - assert (Hin : in_state (c,v, sigma2_1) Empty).
    { apply H2. constructor. left. reflexivity. }
    inversion Hin; subst; clear Hin. exfalso. apply (no_confusion_next_empty _ _ H3).
  - assert (Hin : in_state (c,v, sigma1_1) Empty).
    { apply H1. constructor. left. reflexivity. }
    inversion Hin; subst; clear Hin. exfalso. apply (no_confusion_next_empty _ _ H3).
  - apply sorted_syntactic_state_inclusion_eq_ind in H2; try assumption.
    destruct H2 as [Heq [Hin12 Hin21]].
    inversion Heq; subst; clear Heq.
    apply locally_sorted_tail in H.
    apply locally_sorted_tail in H0.
    apply IHsigma1_2 in Hin21; try assumption.
    subst.
    reflexivity.
Qed.


(** (Insertion) sorting function **)

Inductive sort : state -> state -> Prop :=
  | Sort_empty : sort Empty Empty
  | Sort_next : forall c v j js sigma sigmas sigma',
    sort j js ->
    sort sigma sigmas ->
    add_in_sorted (c,v,js) sigmas sigma' ->
    sort (next (c,v,j) sigma) sigma'.

Theorem sort_is_sorted : forall sigma sigmas,
  sort sigma sigmas -> locally_sorted sigmas.
Proof.
  intros.
  induction H; try constructor.
  apply add_in_sorted_sorted with c v js sigmas; assumption.
Qed.

Theorem sort_sorted_idem : forall sigma,
  locally_sorted sigma -> sort sigma sigma.
Proof.
  intros. induction H.
  - constructor.
  - apply Sort_next with j Empty; try assumption; constructor.
  - apply Sort_next with j (next msg' sigma); try assumption.
    apply add_in_Next_lt; assumption.
Qed.

Theorem sort_total : forall sigma, exists sigmas, sort sigma sigmas.
Proof.
  induction sigma.
  - exists Empty. constructor.
  - rename sigma1 into j. rename sigma2 into sigma.
    destruct IHsigma1 as [js Hjs].
    destruct IHsigma2 as [sigmas Hsigmas].
    destruct (add_in_sorted_total (c, v, js) sigmas) as [sigma' Hsigma'].
    exists sigma'. rewrite add_is_next .
    apply Sort_next with js sigmas; assumption.
Qed.

Theorem sort_functional : forall sigma sigmas1 sigmas2,
  sort sigma sigmas1 ->
  sort sigma sigmas2 ->
  sigmas1 = sigmas2.
Proof.
  induction sigma; intros; try rewrite add_is_next in *
  ; inversion H0; subst; clear H0
  ; inversion H; subst; clear H
  .
  - reflexivity.
  - apply (IHsigma1 _ _ H6) in H5; subst; clear H6.
    apply (IHsigma2 _ _ H7) in H9; subst; clear H7.
    apply (add_in_sorted_functional _ _ _ _ H8) in H10; subst .
    reflexivity.
Qed.

Lemma sort_empty : forall sigma,
  sort sigma Empty -> sigma = Empty.
Proof.
  intros. inversion H; subst; clear H; try reflexivity.
  exfalso.
  inversion H2.
  apply (no_confusion_next_empty msg' sigma' H).
Qed.

Definition msg_sort (msg : message) (msgs : message) : Prop :=
  sort (next msg Empty) (next msgs Empty).

Lemma msg_sort_construct : forall c v j js,
  sort j js -> msg_sort (c, v, j) (c, v, js).
Proof.
  intros.
  unfold msg_sort. apply Sort_next with js Empty; try assumption; constructor.
Qed.

Lemma msg_sort_destruct : forall msg msgs,
  msg_sort msg msgs ->
  exists c v j js, msg = (c,v,j) /\ msgs = (c,v,js) /\ sort j js.
Proof.
  intros.
  inversion H; subst; clear H.
  - exfalso. symmetry in H1. apply (no_confusion_next_empty _ _ H1).
  - rewrite add_is_next in *.
    apply no_confusion_next in H0; destruct H0; subst.
    inversion H2; subst; clear H2.
    apply add_in_empty in H3.
    apply no_confusion_next in H3; destruct H3; subst. clear H0.
    exists c. exists v. exists j. exists js.
    repeat split; try reflexivity.
    assumption.
Qed.

Definition in_state_sorted (msg : message) (sigmas : state) : Prop :=
  exists msgs,  msg_sort msg msgs /\ in_state msgs sigmas .

Theorem in_sorted_state_all : forall sigma sigmas,
  sort sigma sigmas ->
  forall msg, in_state msg sigma -> in_state_sorted msg sigmas.
Proof.
  intros sigma sigmas H. unfold in_state_sorted. induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - inversion H2; subst; clear H2.
    rewrite add_is_next in H3.
    apply no_confusion_next in H3; destruct H3; subst.
    destruct H5; subst.
    + exists (c,v,js). split; try assumption.
      * apply msg_sort_construct; assumption.
      * apply add_in_sorted_msg_preservation with sigmas; assumption.
    + apply IHsort2 in H2.
      destruct H2 as [msgs [Hmsgs Hin]].
      exists msgs. split; try assumption.
      apply (add_in_sorted_state_preservation _ _ _ H1 msgs Hin).
Qed.

Theorem in_sort_state : forall sigma sigmas,
  sort sigma sigmas ->
  forall msgs,
  in_state msgs sigmas ->
  exists msg, msg_sort msg msgs /\ in_state msg sigma.
Proof.
  intros sigma sigmas H.
  induction H; intros.
  - exfalso. apply (in_empty_state _ H).
  - apply (add_in_sorted_no_junk _ _ _ H1) in H2.
    destruct H2; subst.
    + exists (c, v, j). split.
      * apply msg_sort_construct; assumption.
      * constructor. left. reflexivity.
    + apply IHsort2 in H2.
      destruct H2 as [js' [Hjs' Hin]].
      exists js'. split; try assumption.
      constructor. right. assumption.
Qed.


(** State equality (as sets) **)


Inductive state_eq : state -> state -> Prop :=
  | State_eq : forall sigma1 sigma2,
      (exists sigmas, sort sigma1 sigmas /\ sort sigma2 sigmas) ->
      state_eq sigma1 sigma2.

Theorem sorted_state_eq_equality_predicate : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  state_eq sigma1 sigma2 ->
  sigma1 = sigma2.
Proof.
  intros. inversion H1; subst; clear H1.
  apply sort_sorted_idem in H. apply sort_sorted_idem in H0.
  destruct H2 as [sigmas [Hsigma1s Hsigma2s]].
  apply (sort_functional _ _ _ H) in Hsigma1s; clear H; subst.
  apply (sort_functional _ _ _ H0) in Hsigma2s; clear H0; subst.
  reflexivity.
Qed.

Theorem state_eq_reflexive : Reflexive state_eq.
Proof.
  unfold Reflexive. induction x.
  - constructor. exists Empty. split; constructor.
  - constructor.
    inversion IHx2; subst; clear IHx2.
    destruct H as [x2s [Hx2s _]].
    inversion IHx1; subst; clear IHx1.
    destruct H as [x1s [Hx1s _]].
    destruct (add_in_sorted_total (c, v, x1s) x2s) as [sigmas Hsigmas].
    exists sigmas.
    assert (forall A : Prop, A -> (A /\ A)); try (intros; split; assumption).
    apply H. rewrite add_is_next.
    apply Sort_next with x1s x2s; assumption.
Qed.

Theorem state_eq_symmetric : Symmetric state_eq.
Proof.
  unfold Symmetric.
  intros. destruct H. destruct H as [sigmas [H1 H2]].
  constructor. exists sigmas. split; assumption.
Qed.

Lemma state_eq_empty : forall sigma,
  state_eq sigma Empty -> sigma = Empty.
Proof.
  intros.
  inversion H; subst; clear H.
  destruct H0 as [zs [Hzs1 Hzs2]].
  inversion Hzs2; subst; clear Hzs2.
  apply sort_empty. assumption.
Qed.

Lemma empty_eq_state : forall sigma,
  state_eq Empty sigma -> sigma = Empty.
Proof.
  intros. apply state_eq_empty. apply state_eq_symmetric. assumption.
Qed.

Theorem state_eq_transitive : Transitive state_eq.
Proof.
  unfold Transitive.
  intros.
  constructor.
  inversion H; subst; clear H.
  destruct H1 as [xys [Hxs Hys]].
  inversion H0; subst; clear H0.
  destruct H as [yzs [Hys' Hzs]].
  apply (sort_functional _ _ _ Hys) in Hys'; subst; clear Hys.
  exists yzs. split; assumption.
Qed.


Lemma sort_state_eq : forall sigma sigmas,
  sort sigma sigmas -> state_eq sigma sigmas.
Proof.
  intros. constructor.
  exists sigmas.
  split; try assumption.
  apply sort_sorted_idem.
  apply sort_is_sorted with sigma.
  assumption.
Qed.

Definition msg_eq (msg1 : message) (msg2 : message) : Prop :=
  state_eq (next msg1 Empty) (next msg2 Empty).

Lemma msg_sort_eq : forall msg1 msg2 msgs,
  msg_sort msg1 msgs -> msg_sort msg2 msgs -> msg_eq msg1 msg2.
Proof.
  unfold msg_sort. unfold msg_eq. intros.
  constructor. exists (next msgs Empty).
  split; assumption.
Qed.

Lemma msg_eq_reflexive : Reflexive msg_eq.
Proof.
  unfold Reflexive. unfold msg_eq. intro. apply state_eq_reflexive.
Qed.

Lemma msg_eq_transitive : Transitive msg_eq.
Proof.
  unfold Transitive.
  unfold msg_eq. intros msg1 msg2 msg3. apply state_eq_transitive.
Qed.

Lemma msg_eq_construct : forall msg1 msg2,
  msg_eq msg1 msg2
  -> exists c v j1 j2, msg1 = (c, v, j1)/\ msg2 = (c, v, j2) /\ state_eq j1 j2.
Proof.
  intros. inversion H; subst; clear H.
  destruct H0 as [msgs [H1s H2s]].
  inversion H1s; subst; clear H1s; try (exfalso; symmetry in H0; apply (no_confusion_next_empty _ _ H0)).
  rename H0 into Hjs.
  inversion H2s; subst; clear H2s; try (exfalso; symmetry in H3; apply (no_confusion_next_empty _ _ H3)).
  rewrite add_is_next in *.
  apply no_confusion_next in H; destruct H; subst.
  apply no_confusion_next in H0; destruct H0; subst.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  apply add_in_empty in H2; subst.
  apply add_in_empty in H5.
  apply no_confusion_next in H5. destruct H5 as [H5 _]. inversion H5; subst; clear H5.
  exists c0. exists v0. exists j. exists j0. repeat (split; try reflexivity).
  exists js0. split;assumption.
Qed.

(*******************************)
(** Semantic state membership **)
(*******************************)

Definition in_state_eq (msg : message) (sigma' : state) : Prop :=
  exists msg', in_state msg' sigma' /\ msg_eq msg msg'.

Lemma in_state_eq_empty : forall msg, ~ in_state_eq msg Empty.
Proof.
  intro. intro. inversion H; subst; clear H. destruct H0.
  apply (in_empty_state _ H).
Qed.

Lemma in_state_eq_next : forall msg msg' sigma',
  in_state_eq msg (next msg' sigma') ->
  msg_eq msg msg' \/ in_state_eq msg sigma'.
Proof.
  unfold in_state_eq.
  intros. destruct H as [msg'' [Hin Heq]].
  inversion Hin;  subst; clear Hin.
  apply no_confusion_next in H; destruct H; subst.
  destruct H1; subst.
  - left; assumption.
  - right.  exists msg''. split; assumption.
Qed.

Definition state_inclusion (sigma1 : state) (sigma2 : state) : Prop :=
  forall msg, in_state_eq msg sigma1 -> in_state_eq msg sigma2.


Lemma state_inclusion_empty : forall sigma, state_inclusion Empty sigma.
Proof.
  intros. unfold state_inclusion. intros. exfalso; apply (in_state_eq_empty _ H).
Qed.

Lemma state_inclusion_next_l : forall msg sigma sigma',
  state_inclusion sigma sigma' ->
  state_inclusion (next msg sigma) (next msg sigma').
Proof.
  unfold state_inclusion.
  intros. apply in_state_eq_next in H0.
  unfold in_state_eq.
  destruct H0.
  - exists msg. split; try assumption.
    constructor. left. reflexivity.
  - apply H in H0. destruct H0 as [msg0' [Hin Heq]].
    exists msg0'. split; try assumption.
    constructor. right. assumption.
Qed.

Lemma state_inclusion_next_r : forall msg sigma sigma',
  state_inclusion sigma sigma' ->
  state_inclusion sigma (next msg sigma').
Proof.
  unfold state_inclusion. intros.
  apply H in H0. destruct H0 as [msg0' [Hin Heq]].
    exists msg0'. split; try assumption.
    constructor. right. assumption.
Qed.


Theorem state_inclusion_reflexive : Reflexive state_inclusion.
Proof.
  intros sigma msg H. assumption.
Qed.

Theorem state_inclusion_transitive : Transitive state_inclusion.
Proof.
  intros sigma1 sigma2 sigma3 H12 H23 msg Hin.
  apply H12 in Hin. apply (H23 _ Hin).
Qed.

Theorem state_eq_inclusion : forall sigma1 sigma2,
  state_eq sigma1 sigma2 ->
  state_inclusion sigma1 sigma2.
Proof.
  unfold state_inclusion.
  intros. inversion H; subst; clear H.
  destruct H1 as [sigmas [Hsigma1s Hsigma2s]].
  inversion H0; subst; clear H0. destruct H.
  apply (in_sorted_state_all _ _ Hsigma1s) in H.
  destruct H as [xs [Hxs Hin]].
  unfold in_state_eq.
  apply (in_sort_state _ _ Hsigma2s) in Hin.
  destruct Hin as [x' [Hx's Hin]]. 
  exists x'. split; try assumption.
  apply (msg_sort_eq _ _ _ Hxs) in Hx's.
  apply (msg_eq_transitive msg x x'); assumption.
Qed.

Theorem set_in_state_sorted : forall c v j sigma,
  locally_sorted sigma ->
  locally_sorted j ->
  in_state_eq (c,v,j) sigma <-> in_state (c, v, j) sigma.
Proof.
  intros. split; intros.
  {
  inversion H1; subst; clear H1. destruct H2.
  apply msg_eq_construct in H2.
  destruct H2 as [c0 [v0 [j1 [j2 [EQ1 [EQ2 SEQ]]]]]]; inversion EQ1; subst; clear EQ1.
  apply in_sorted_state in H1 as Hj2s; try assumption.
  inversion SEQ; subst; clear SEQ.
  destruct H2 as [js [Hj1s Hj2s']].
  apply sort_sorted_idem in H0.
  apply sort_sorted_idem in Hj2s.
  apply (sort_functional _ _ _ H0) in Hj1s; subst; clear H0.
  apply (sort_functional _ _ _ Hj2s) in Hj2s'; subst; clear Hj2s.
  assumption.
  }
  {
    exists (c, v, j). split; try assumption.
    apply msg_eq_reflexive.
  }
Qed.

Theorem sorted_state_inclusion : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  state_inclusion sigma1 sigma2 <-> syntactic_state_inclusion sigma1 sigma2.
Proof.
  intros.
  split; intros.
  { intros msg Hin.
    destruct msg as [(c, v) j].
    apply in_sorted_state in Hin as Hjs; try assumption.
    apply (set_in_state_sorted _ _ _ _ H Hjs) in Hin.
    apply H1 in Hin.
    apply (set_in_state_sorted _ _ _ _ H0 Hjs) in Hin.
    assumption.
  }
  {
    intros msg Hin. inversion Hin; subst; clear Hin. destruct H2.
    apply H1 in H2. unfold in_state_eq. exists x. split; assumption.
  }
Qed.

Inductive sorted_subset : state -> state -> Prop :=
  | SubSet_Empty: forall sigma,
          sorted_subset Empty sigma
  | SubSet_Next_l: forall msg sigma sigma',
          sorted_subset sigma sigma' ->
          sorted_subset (next msg sigma) (next msg sigma')
  | SubSet_Next_r: forall msg sigma sigma',
          sorted_subset sigma sigma' ->
          sorted_subset sigma (next msg sigma')
  .

Notation "sigma1 '=>' sigma2" :=
  (sorted_subset sigma1 sigma2)
  (at level 20).


Lemma sorted_subset_syntactic_inclusion : forall sigma sigma',
  sorted_subset sigma sigma' ->
  syntactic_state_inclusion sigma sigma'.
Proof.
  intros sigma sigma' H. induction H; intros.
  - intros msg H. exfalso. apply (in_empty_state _ H).
  - intros msg' H0. inversion H0; subst; clear H0. 
    apply no_confusion_next in H1; destruct H1; subst.
    destruct H3; subst.
    + constructor. left. reflexivity.
    + constructor. right. apply IHsorted_subset. assumption.
  - constructor. right.  apply IHsorted_subset. assumption.
Qed.


Lemma syntactic_inclusion_sorted_subset : forall sigma sigma',
  locally_sorted sigma ->
  locally_sorted sigma' ->
  syntactic_state_inclusion sigma sigma' ->
  sorted_subset sigma sigma'.
Proof.
  intros sigma sigma'.
  generalize dependent sigma.
  induction sigma'; intros.
  - destruct sigma.
    + constructor.
    + rewrite add_is_next in *. assert (H2 : in_state (c, v, sigma1) Empty).
      { apply H1. constructor. left. reflexivity. }
      exfalso. apply (in_empty_state _ H2).
  - clear IHsigma'1. rewrite add_is_next in *.
    apply locally_sorted_tail in H0 as LSsigma'2.
    destruct sigma.
    + constructor.
    + rewrite add_is_next in *.
      apply sorted_syntactic_state_inclusion in H1; try assumption.
      destruct H1; destruct H1; apply locally_sorted_tail in H0.
      * inversion H1; subst; clear H1.
        apply SubSet_Next_l.
        apply locally_sorted_tail in H.
        apply IHsigma'2; assumption.
      * apply SubSet_Next_r.
        apply IHsigma'2; assumption.
Qed.

Corollary sorted_subset_inclusion : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_subset sigma1 sigma2 <-> state_inclusion sigma1 sigma2.
Proof.
  intros; split; intro.
  - apply sorted_state_inclusion; try assumption.
    apply sorted_subset_syntactic_inclusion. assumption.
  - apply syntactic_inclusion_sorted_subset; try assumption.
    apply sorted_state_inclusion; assumption.
Qed.

Theorem inclusion_state_eq : forall sigma1 sigma2,
  state_inclusion sigma1 sigma2 ->
  state_inclusion sigma2 sigma1 ->
  state_eq sigma1 sigma2.
Proof.
  intros.
  destruct (sort_total sigma1) as [sigma1s Hsort1].
  destruct (sort_total sigma2) as [sigma2s Hsort2].
  apply sort_is_sorted in Hsort1 as Hsigma1s.
  apply sort_is_sorted in Hsort2 as Hsigma2s.
  apply sort_state_eq in Hsort1.
  apply sort_state_eq in Hsort2.
  apply state_eq_inclusion in Hsort1 as Hinsigma1s.
  apply state_eq_symmetric in Hsort1.
  apply state_eq_inclusion in Hsort1 as Hinsigma1s'.

  apply state_eq_inclusion in Hsort2 as Hinsigma2s.
  apply state_eq_symmetric in Hsort2.
  apply state_eq_inclusion in Hsort2 as Hinsigma2s'.

  apply (state_inclusion_transitive _ _ _ H) in Hinsigma2s.
  apply (state_inclusion_transitive _ _ _ Hinsigma1s') in Hinsigma2s.
  apply (state_inclusion_transitive _ _ _ H0) in Hinsigma1s.
  apply (state_inclusion_transitive _ _ _ Hinsigma2s') in Hinsigma1s.
  clear H. clear H0. clear Hinsigma1s'. clear Hinsigma2s'.
  
  apply sorted_subset_inclusion in Hinsigma1s; try assumption.
  apply sorted_subset_inclusion in Hinsigma2s; try assumption.

  apply sorted_subset_syntactic_inclusion in Hinsigma1s.
  apply sorted_subset_syntactic_inclusion in Hinsigma2s.

  apply sorted_syntactic_state_inclusion_equality_predicate in Hinsigma2s
  ; try assumption.
  subst.
  apply state_eq_symmetric in Hsort1.
  apply (state_eq_transitive _ _ _ Hsort1 Hsort2).
Qed.


Theorem add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
  induction sigma; intros; repeat rewrite add_is_next in *.
  - exfalso. apply (in_empty_state _ H0).
  - inversion H0; subst; clear H0.
    rewrite add_is_next in *.
    apply no_confusion_next in H1; destruct H1; subst.
    destruct H3.
    + subst. constructor.
    + apply (state_set_In _ _ _ H) in H0 as Hlt.
      apply locally_sorted_tail in H.
      apply IHsigma2 in H0; try assumption.
      constructor; assumption.
Qed.

(******************************)
(** Union of (sorted) states **)
(******************************)

Inductive sorted_union : state -> state -> state -> Prop :=
  | Sorted_union_Empty_left : forall sigma, sorted_union Empty sigma sigma
  | Sorted_union_Empty_right : forall sigma, sorted_union sigma Empty sigma
  | Sorted_union_Next_eq : forall msg sigma1 sigma2 sigma',
      sorted_union sigma1 sigma2 sigma' ->
      sorted_union (next msg sigma1) (next msg sigma2) (next msg sigma')
  | Sorted_union_Next_lt : forall msg1 sigma1 msg2 sigma2 sigma',
      msg_lt msg1 msg2 ->
      sorted_union sigma1 (next msg2 sigma2) sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg1 sigma')
  | Sorted_union_Next_gt : forall msg1 sigma1 msg2 sigma2 sigma',
      msg_lt msg2 msg1 ->
      sorted_union (next msg1 sigma1) sigma2 sigma' ->
      sorted_union (next msg1 sigma1) (next msg2 sigma2) (next msg2 sigma')
  .

(** TODO: Properties **)


(****************************)
(** Fault Weight of States **)
(****************************)

(**
Note that this includes equivocation fault weight, as we defaulted 
the weight of non-equivocating messages to 0
**)

Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 j1 j2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,j1) (c2,v2,j2) 0
  | fault_weight_c_msg: forall c v j,
      fault_weight_msg (c,v,j) (c,v,j) 0
  | fault_weight_msg1: forall c1 c2 v j1 j2,
      in_state (c1,v,j1) j2 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_msg2: forall c1 c2 v j1 j2,
      in_state (c2,v,j2) j1 ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) 0
  | fault_weight_next: forall c1 c2 v j1 j2,
      c1 <> c2 \/ j1 <> j2 ->
      not (in_state (c1,v,j1) j2) ->
      not (in_state (c2,v,j2) j1) ->
      fault_weight_msg (c1,v,j1) (c2,v,j2) (weight v)
  .

Theorem fault_weight_msg_functional : forall msg1 msg2 r1 r2,
  fault_weight_msg msg1 msg2 r1 ->
  fault_weight_msg msg1 msg2 r2 ->
  r1 = r2.
Proof.
  intros. inversion H; subst; clear H; inversion H0; subst; clear H0
  ; try reflexivity
  ; try contradiction.
  - destruct H6; contradiction.
  - destruct H1; contradiction.
Qed.

Theorem fault_weight_msg_total : forall msg1 msg2,
  exists r, fault_weight_msg msg1 msg2 r.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  destruct (V_eq_dec v1 v2).
  - destruct (C_eq_dec c1 c2).
    + destruct (state_eq_dec j1 j2); subst.
      * exists 0%R. apply fault_weight_c_msg.
      * destruct (in_state_dec (c2, v2, j1) j2).
        { exists 0%R. apply fault_weight_msg1. assumption. }
        destruct (in_state_dec (c2, v2, j2) j1).
        { exists 0%R. apply fault_weight_msg2. assumption. }
        exists (weight v2).
        apply fault_weight_next; try assumption.
        right. assumption.
    + subst.
      destruct (in_state_dec (c1, v2, j1) j2).
      { exists 0%R. apply fault_weight_msg1. assumption. }
      destruct (in_state_dec (c2, v2, j2) j1).
      { exists 0%R. apply fault_weight_msg2. assumption. }
      exists (weight v2).
      apply fault_weight_next; try assumption.
      left. assumption.
  - exists 0%R. apply fault_weight_v_diff. assumption.
Qed.

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_Empty: forall msg,
      fault_weight_message_state msg Empty 0
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (next msg2 sigma) (r1 + r2)%R
.

Theorem fault_weight_message_state_functional : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_message_state_total : forall msg sigma,
  exists r, fault_weight_message_state msg sigma r.
Admitted.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_Empty: 
      fault_weight_state Empty 0
  | fault_weight_state_Next: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (next msg sigma) (r1 + r2)%R
.


Theorem fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2.
Admitted.

Theorem fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
Admitted.

(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    sorted_subset sigma1 sigma2.

(** The valid message condition **)
Definition valid_msg_condition (c : C) (sigma : state) : Prop :=
    epsilon sigma c.


(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  forall r,
  fault_weight_state sigma r ->
  (r <= t)%R.

Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall c v sigma sigma' sigma'',
      protocol_state sigma ->
      protocol_state sigma' ->
      full_node_condition sigma sigma' ->
      valid_msg_condition c sigma ->
      add_in_sorted (c, v, sigma) sigma' sigma'' ->
      fault_tolerance_condition sigma'' ->
      protocol_state sigma''
  .

Theorem protocol_state_sorted : forall state,
  protocol_state state -> locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted c v sigma sigma'); try assumption.
Qed.















