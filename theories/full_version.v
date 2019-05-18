Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

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

Axiom c_lt_storder: StrictOrder c_lt.

(** C totally ordered **)

Axiom C_totally_ordered: TotalOrder c_lt.


(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Variable V : Set .

Axiom V_non_empty : exists v : V, True.

(** Less than order on validator names **)

Variable v_lt : V -> V -> Prop.

Axiom v_lt_storder: StrictOrder v_lt.

(** V totally ordered **)

Axiom V_totally_ordered: TotalOrder v_lt.


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
 assert (SOc : StrictOrder c_lt); try apply c_lt_storder.
 assert (SOv : StrictOrder v_lt); try apply v_lt_storder. 
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
  assert (SOc : StrictOrder c_lt); try apply c_lt_storder.
  assert (SOv : StrictOrder v_lt); try apply v_lt_storder.
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

Lemma state_lt_storder : StrictOrder state_lt.
Proof.
  constructor.
  - apply state_lt_irreflexive.
  - apply state_lt_transitive.
Qed.

Theorem state_lt_total : TotalOrder state_lt.
Proof.
  unfold TotalOrder.
  intros. generalize dependent c2.
  induction c1.
  - induction c2.
    + left. reflexivity.
    + right. left. apply state_lt_Empty.
  - induction c2.
    + right. right. apply state_lt_Empty.
    + destruct (C_totally_ordered c c0); subst.
      * destruct (V_totally_ordered v v0); subst.
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

Lemma msg_lt_storder : StrictOrder msg_lt.
Proof.
  constructor.
  - apply msg_lt_irreflexive.
  - apply msg_lt_transitive.
Qed.

Corollary msg_lt_total: TotalOrder msg_lt.
Proof.
  unfold TotalOrder. 
  unfold msg_lt.
  destruct c1 as [(c1, v1) j1].
  destruct c2 as [(c2, v2) j2].
  unfold next.
  destruct (C_totally_ordered c1 c2); subst.
  + destruct (V_totally_ordered v1 v2); subst.
    * destruct (state_lt_total j1 j2); subst.
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
  - destruct (msg_lt_total (c,v,j) (sc,sv,sj)) as [Heq | [LT | GT]].
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

Lemma in_empty_state : forall msg, ~ in_state msg Empty.
Proof.
  intros. intro. inversion H; subst.
  apply no_confusion_next_empty in H0; inversion H0.
Qed.

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
  forall msg', in_state msg' sigma -> in_state msg' sigma'.
Proof.
  intros msg sigma sigma' H.
  induction H; intros; try assumption. 
  - exfalso. apply (in_empty_state msg' H).
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

(** Work in progress **)

(** State equality (as sets) **)


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

(**** TODO(traian): continue from here **)

Theorem set_in_state_sorted : forall c v j sigma,
  locally_sorted sigma ->
  locally_sorted j ->
  in_state_eq (c,v,j) sigma -> in_state (c, v, j) sigma.
Proof.
  intros.
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

Theorem sorted_subset_inclusion : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  sorted_subset sigma1 sigma2 <-> state_inclusion sigma1 sigma2.
Proof.
  intros. split; intros; generalize dependent H0; generalize dependent H. 
  - induction H1; intros.
    + apply state_inclusion_empty.
    + apply state_inclusion_next_l.
      apply locally_sorted_tail in H0. 
      apply locally_sorted_tail in H. 
      apply IHsorted_subset; assumption.
    +  apply state_inclusion_next_r.
      apply locally_sorted_tail in H0. 
      apply IHsorted_subset; assumption.
  - unfold state_inclusion in H1.
    intro. induction H ; intros.
    + constructor.
    + assert (Hin : in_state_eq (c, v, j) sigma2).
      { apply H1. unfold in_state_eq. exists (c, v, j).
        split; try (apply msg_eq_reflexive).
        constructor. left. reflexivity.
      }
      apply set_in_state_sorted in Hin; try assumption.
Admitted.

Theorem sorted_subset_elements: forall msg sigma1 sigma2, 
    locally_sorted(sigma1) -> 
    locally_sorted(sigma2) ->
    sorted_subset sigma1 sigma2 -> 
    in_state msg sigma1 -> 
    in_state msg sigma2.
Proof.
  Admitted.

Theorem inclusion_state_eq : forall sigma1 sigma2,
  state_inclusion sigma1 sigma2 ->
  state_inclusion sigma2 sigma1 ->
  state_eq sigma1 sigma2.
Proof.
  intros.
Admitted.


Theorem add_sorted : forall sigma msg, 
  locally_sorted sigma -> 
  in_state msg sigma -> 
  add_in_sorted msg sigma sigma.
Proof.
(*
  intros sigma msg is_sorted is_in_state.
  induction is_sorted as [| msg' | msg''].
  - inversion is_in_state.
  - destruct (msg_compare msg msg') eqn:mc; try (simpl in is_in_state; rewrite mc in is_in_state; inversion is_in_state).
    { simpl. rewrite mc. reflexivity. }
  - destruct (msg_compare msg msg'') eqn:mc''.
    + rewrite <- (IHis_sorted (in_state_decompose_LT _ _ _ is_in_state mc0)) at 2.
      apply  in mc0.
    + 
apply in_state_decompose in is_in_state.
    +
    destruct is_in_state as [is_in_state_first | is_in_state_not_first].
    + unfold add. rewrite is_in_state_first. reflexivity.
    + apply IHis_sorted in is_in_state_not_first.
      simpl in is_in_state_not_first.
      simpl. rewrite is_in_state_not_first.
*)
  Admitted.

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
Admitted.

Theorem fault_weight_msg_total : forall msg1 msg2,
  exists r, fault_weight_msg msg1 msg2 r.
Admitted.

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




(**  **)

(* NOT needed anymore

Inductive messages : state -> list message -> Prop :=
  | msg_Empty : messages Empty nil
  | msg_Next : forall msg sigma l,
      messages sigma l ->
      messages (next msg sigma) (msg :: l)
  .

Inductive fault_weight_msgs : list message -> R -> Prop :=
  | fault_weight_msgs_nil: fault_weight_msgs nil 0
  | fault_weight_msgs_elem: forall c v msg,
      fault_weight_msgs ((c,v,msg) :: nil) (weight v)
  | fault_weight_msgs_next: forall msg1 msg2 msgs r1 r2,
       fault_weight_msg msg1 msg2 r1 ->
       fault_weight_msgs msgs r2 ->
      (fault_weight_msgs (msg1 :: msg2 :: msgs)) (r1 + r2)%R
  .


Inductive state_eq : state -> state -> Prop :=
  | state_eq_Empty : state_eq Empty Empty 
  | state_eq_Next : forall c v j1 j2 sigma1 sigma2,
      state_eq j1 j2 ->
      state_eq sigma1 sigma2 ->
      state_eq (add (c,v,j1) to sigma1) (add (c,v,j2) to sigma2)
  .

Theorem state_eq_reflexive:
  forall sigma, state_eq sigma sigma.
Proof.
  induction sigma.
  - constructor.
  - constructor; (try assumption; reflexivity).
Qed.

Theorem state_equality_predicate:
  forall sigma1 sigma2, sigma1 = sigma2 <-> state_eq sigma1 sigma2.
Proof.
  split.
  - intros. subst. apply state_eq_reflexive.
  - intros. induction H.
    + reflexivity.
    + subst. reflexivity.
Qed.

Definition msg_eq (msg1 msg2 : message) : Prop :=
  state_eq (next msg1 Empty) (next msg2 Empty).

Corollary msg_equality_predicate:
  forall msg1 msg2, msg1 = msg2 <-> msg_eq msg1 msg2.
Proof.
  destruct msg1 as [(c1,v1) j1].
  destruct msg2 as [(c2,v2) j2].
  unfold msg_eq. unfold next.
  split; intros.
  - inversion H; subst. apply state_equality_predicate. reflexivity.
  - apply state_equality_predicate in H. inversion H; subst. reflexivity.
Qed.

Lemma state_set_eq_first_equal : forall c1 v1 j1 c2 v2 j2 sigma1 sigma2,
  (state_set_eq j1 j2 -> j1 = j2 ) ->
  locally_sorted (next (c1, v1, j1) sigma1) ->
  locally_sorted (next (c2, v2, j2) sigma2) ->
  state_set_eq (next (c1, v1, j1) sigma1) (next (c2, v2, j2) sigma2) ->
  (c1, v1, j1) = (c2, v2, j2) /\ state_set_eq sigma1 sigma2.
Proof.
  intros. destruct H2.  split.
  - assert (H21 := H2 (c1,v1,j1)).
Admitted.

Theorem state_set_eq_equality : forall sigma1 sigma2,
  locally_sorted sigma1 ->
  locally_sorted sigma2 ->
  state_set_eq sigma1 sigma2 <-> sigma1 = sigma2.
Proof.
  intros.
  split.
  - generalize dependent sigma2.
    induction H as
    [
    | c v j LSj
    | c v j [(c', v') j'] sigma1 LSj HLSj  LT LS1
    ]
    ; intros sigma2 LS2; destruct sigma2
    .
    + intros. reflexivity.
    + intros. rewrite add_is_next in *.
      exfalso. apply (not_empty_state_set_eq_next _ _ H).
    + intros.
      exfalso. apply (not_next_state_set_eq_empty _ _ H).
    + intros. rewrite add_is_next in *.
      inversion LS2; subst; assert (LS1 : locally_sorted (next (c, v, j) Empty));
      try ( constructor; assumption). 
      * apply (state_set_eq_first_equal _ _ _ _ _ _ _ _ (IHLSj _ H1) LS1 LS2) in H.
        destruct H. inversion H; subst. reflexivity.
      * apply (state_set_eq_first_equal _ _ _ _ _ _ _ _ (IHLSj _ H3) LS1 LS2) in H.
        destruct H. exfalso. apply (not_empty_state_set_eq_next _ _ H0).
    + intros. exfalso. apply (not_next_state_set_eq_empty _ _ H).
    + intros. rewrite add_is_next in *.
      inversion LS2; subst.
      * exfalso. apply (not_next_state_set_eq_empty (c', v', j') sigma1).
      apply proj2 with (A := (c, v, j) = (c0, v0, sigma2_1)).
      apply state_set_eq_first_equal; try assumption.
      { apply HLSj. assumption. }
      { apply LSorted_Next; assumption. }
      * assert (HSplit :  (c, v, j) = (c0, v0, sigma2_1) /\ state_set_eq (next (c', v', j') sigma1) (next msg' sigma)).
        { apply state_set_eq_first_equal; try assumption.
          - apply HLSj; assumption.
          -  apply LSorted_Next; assumption.
        }
        destruct HSplit as [HSplit1 HSplit2].
        inversion_clear HSplit1; subst.
        apply (IHLS1 _ H6) in HSplit2. rewrite HSplit2. reflexivity.
  - intro; subst. apply state_set_eq_reflexive.
Qed.

(** work in progress (syntactic inclusion) **)

Definition state_incl (sigma sigma' : state) : Prop :=
  forall msg, in_state msg sigma -> in_state msg sigma'.

Theorem state_incl_reflexive : forall sigma, state_incl sigma sigma.
Proof.
  - intro; intro; intros; assumption.
Qed.

Lemma not_next_state_incl_empty : forall msg sigma,
  ~ state_incl (next msg sigma) Empty.
Proof.
  intros. intro. 
  assert (H1 := H msg).
  assert (H2 : in_state msg (next msg sigma)).
  { constructor. left. reflexivity. }
  apply H1 in H2. inversion H2; subst.
  destruct msg0 as [(c0, v0) j0]. inversion H0.
Qed.

Definition state_set_eq (sigma sigma' : state) : Prop :=
  state_incl sigma sigma' /\ state_incl sigma' sigma.

Corollary not_next_state_set_eq_empty : forall msg sigma,
  ~ state_set_eq (next msg sigma) Empty.
Proof.
  intros. intro. destruct H. apply (not_next_state_incl_empty _ _ H).
Qed.

Corollary not_empty_state_set_eq_next : forall msg sigma,
  ~ state_set_eq Empty (next msg sigma).
Proof.
  intros. intro. destruct H. apply (not_next_state_incl_empty _ _ H0).
Qed.

Corollary state_set_eq_reflexive : forall sigma, state_set_eq sigma sigma.
Proof.
  intros. split; apply state_incl_reflexive.
Qed.
(** end of work in progress **)
*)


















