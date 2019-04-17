Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.
Import ListNotations.

Class TotalOrder {A} (lt : relation A) : Prop :=
   totality : forall c1 c2, c1 = c2 \/ lt c1 c2 \/ lt c2 c1.


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

Axiom weight_positive : forall v : V, (weight v >= 0)%R.


(************************************************************)
(** Fault tolerance threshold (a non-negative real number) **)
(************************************************************)

Variable t : R.

Axiom threshold_positive : (t >= 0)%R .

(** TODO: Strictly smaller than the total validator weigths **)
(** TODO: Do we really need this assumption? **)


(*******************)
(** Hash universe **)
(*******************)

Variable hash : Set .

(** Less than order on hashes **)

Variable hash_lt : hash -> hash -> Prop.

Axiom hash_lt_storder: StrictOrder hash_lt.

(** V totally ordered **)

Axiom hash_totally_ordered: TotalOrder hash_lt.


(** Sorted Lists **)


Inductive list_lex {A} {lt : relation A} : list A -> list A -> Prop :=
  | list_lex_empty : forall h l,
      list_lex nil (cons h l)
  | list_lex_head : forall h1 h2 l1 l2,
      lt h1 h2 -> list_lex (cons h1 l1) (cons h2 l2)
  | list_lex_tail : forall h l1 l2,
      list_lex l1 l2 -> list_lex (cons h l1) (cons h l2)
  .

Lemma list_lex_storder : forall A lt,
  StrictOrder lt -> StrictOrder (@list_lex A lt).
Proof.
  intros. destruct H. constructor.
  - unfold Irreflexive in *. unfold Reflexive in *. intros. intro.
    induction x; inversion H; subst.
    + apply (StrictOrder_Irreflexive a H1).
    + apply IHx. assumption.
  - unfold Transitive in *. intros. generalize dependent x. induction H0.
    + intros. inversion H.
    + intros. inversion H0; subst.
      * constructor.
      * apply (StrictOrder_Transitive _ _ _ H3) in H.
        apply list_lex_head. assumption.
      * apply list_lex_head. assumption.
    + intros. inversion H; subst.
      * constructor.
      * apply list_lex_head. assumption.
      * apply list_lex_tail. apply (IHlist_lex _ H3).
Qed.

Lemma list_lex_total : forall A lt,
  TotalOrder lt -> TotalOrder (@list_lex A lt).
Proof.
  intros. unfold TotalOrder in *. intros.
  generalize dependent c2. induction c1; destruct c2.
  - left. reflexivity.
  - right; left. constructor.
  - right; right. constructor.
  - destruct (H a a0) as [H1 | [H2 |H3]].
    + subst. destruct (IHc1 c2) as [IH1 | [ IH2 | IH3]].
      * subst. left. reflexivity.
      * right; left. apply list_lex_tail. assumption.
      * right; right. apply list_lex_tail. assumption.
    + right; left. apply list_lex_head. assumption.
    + right; right. apply list_lex_head. assumption.
Qed.


Inductive add_in_sorted {A} {lt : relation A} : A -> list A -> list A -> Prop :=
   | add_in_nil : forall msg,
          add_in_sorted msg nil (msg :: nil)
   | add_in_cons_eq : forall msg sigma,
          add_in_sorted msg (msg :: sigma) (msg :: sigma)
   | add_in_cons_lt : forall msg msg' sigma,
          lt msg msg' ->  
          add_in_sorted msg (msg' :: sigma) (msg :: msg' :: sigma)
   | add_in_Next_gt : forall msg msg' sigma sigma',
          lt msg' msg ->
          add_in_sorted msg sigma sigma' ->
          add_in_sorted msg (msg' :: sigma) (msg' :: sigma')
  .


Lemma add_in_sorted_first {A} {lt : relation A} : forall msg a b sigma sigma',
    StrictOrder lt ->
    LocallySorted lt (a :: sigma) ->
    lt a msg ->
    @add_in_sorted A lt msg (a :: sigma) (a :: b :: sigma') -> 
    lt a b.
Proof.
  intros. 
  destruct H as [HI HT].
  unfold Transitive in HT.
  unfold Irreflexive in HI. unfold Reflexive in HI. unfold complement in HI.
  inversion H2; subst; try (apply HI in H1; inversion H1).
  inversion H7; subst; try assumption.
  inversion H0; subst. assumption.
Qed.

Theorem add_in_sorted_sorted {A} (lt : relation A) : forall msg sigma sigma',
    StrictOrder lt ->
    LocallySorted lt sigma ->
    @add_in_sorted A lt msg sigma sigma' -> 
    LocallySorted lt sigma'.
Proof.
  intros msg sigma sigma' SO Hsorted. 
  assert (SO' := SO).
  destruct SO as [HI _].
  unfold Irreflexive in HI. unfold Reflexive in HI. unfold complement in HI.
  generalize dependent msg.
  generalize dependent sigma'. induction Hsorted.
  - intros. inversion H; subst. constructor.
  - intros. inversion H; subst.
    + constructor.
    + constructor; try assumption; try constructor.
    + inversion H5; subst. constructor; try assumption; try constructor.
  - intros. inversion H0; subst.
    + constructor; try assumption.
    + constructor;  try assumption. constructor;  try assumption.
    + apply IHHsorted in H6. inversion H6; subst.
      * constructor.
      * inversion H0; subst ; try (apply HI in H4; inversion H4).
        inversion H8; subst; try constructor; try assumption.
      * assert (LocallySorted lt (a :: b :: l)); try (constructor; assumption).
        apply (add_in_sorted_first _ _ _ _ _ SO' H3 H4) in H0.
        constructor; assumption. 
Qed.

(** Sorted lists as sets **)
Definition set_eq {A} (s1 s2 : list A) := incl s1 s2 /\ incl s2 s1.

Theorem set_equality_predicate {A}  (lt : relation A) : forall s1 s2,
  StrictOrder lt ->
  LocallySorted lt s1 ->
  LocallySorted lt s2 ->
  set_eq s1 s2 <-> s1 = s2.
Proof.
  intros. split.
  - intro. destruct H2. unfold incl in *. generalize dependent s2. induction H0; intros; destruct s2.
    +  reflexivity.
    + exfalso. apply (H3 a). constructor. reflexivity.
    + exfalso. apply (H2 a). constructor. reflexivity.
    + assert (a = a0 -> s2 = [] -> [a] = a0 :: s2). 
      { intros. subst. reflexivity. }
      apply H0.
      * destruct (H3 a0); try (constructor; reflexivity); try assumption. 
        inversion H4.
Admitted. 


(** Hash sets **)
Definition hash_lex := @list_lex hash hash_lt. 

(** Messages **)

Definition message : Set := C * V * list hash.

Definition message_lt (m1 : message) (m2 : message) : Prop :=
  match m1,m2 with
    (c1,v1,hs1),(c2,v2,hs2) =>
      c_lt c1 c2 \/ (c1 = c2 /\ (v_lt v1 v2 \/ (v1 = v2 /\ hash_lex hs1 hs2))) 
  end.

Lemma message_lt_storder : StrictOrder message_lt.
Proof.
  assert (SOc : StrictOrder c_lt); try apply c_lt_storder.
  assert (SOv : StrictOrder v_lt); try apply v_lt_storder.
  assert (SOh : StrictOrder hash_lt); try apply hash_lt_storder.
  assert (SOhs : StrictOrder hash_lex); try apply (list_lex_storder hash hash_lt SOh).
  constructor.
  - unfold Irreflexive. unfold Reflexive. destruct x as [(c, v) h]. intro.
    destruct H.
    + destruct SOc. unfold Irreflexive in *. unfold Reflexive in *.
      apply (StrictOrder_Irreflexive c H).
    + destruct H. destruct H0.
      * destruct SOv. unfold Irreflexive in *. unfold Reflexive in *.
      apply (StrictOrder_Irreflexive v H0).
      * destruct H0.
        destruct SOhs. unfold Irreflexive in *. unfold Reflexive in *.
        apply (StrictOrder_Irreflexive h H1).
  - unfold Transitive.
    destruct SOc as [_ Soc].
    destruct SOv as [_ Sov].
    destruct SOhs as [_ Sohs].
    destruct x as [(cx, vx) hx].
    destruct y as [(cy, vy) hy].
    destruct z as [(cz, vz) hz].
    simpl. intros Hxy Hyz. 
    destruct Hxy as [Hxyc | [Hxyc [Hxyv | [Hxyv Hxyh]]]]; destruct Hyz as [Hyzc | [Hyzc [Hyzv | [Hyzv Hyzh]]]]
     ; subst
     ; try (left; assumption)
     ; try (right; split; auto; left; assumption).
    + left. apply (Soc _ _ _ Hxyc Hyzc).
    + right; split; auto; left. apply (Sov _ _ _ Hxyv Hyzv).
    + right; split; auto; right; split; auto.
       apply (Sohs _ _ _ Hxyh Hyzh).
Qed.

(************)
(** States **)
(************)

Definition state : Set := list message.
Definition state_lt := @list_lex message message_lt.

(***************)
(** Estimator **)
(***************)

Variable epsilon : state -> C -> Prop.

Axiom epsilon_total : forall s : state, exists c : C, epsilon s c.


(********************)
(* State properties *)
(********************)

Print LocallySorted.

Definition state_sorted : state -> Prop := LocallySorted message_lt.


(**  Light model stops here. Rework things below (full model) **)

Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 msg1 msg2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,msg1) (c2,v2,msg2) 0
  | fault_weight_c_msg: forall c v msg,
      fault_weight_msg (c,v,msg) (c,v,msg) 0
  | fault_weight_msg1: forall c1 c2 v msg1 msg2,
      in_state (c1,v,msg1) msg2 ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) 0
  | fault_weight_msg2: forall c1 c2 v msg1 msg2,
      in_state (c2,v,msg2) msg1 ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) 0
  | fault_weight_next: forall c1 c2 v msg1 msg2,
      c1 <> c2 ->
      msg1 <> msg2 ->
      not (in_state (c1,v,msg1) msg2) ->
      not (in_state (c2,v,msg2) msg2) ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) (weight v)
  .

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_Empty: forall msg,
      fault_weight_message_state msg Empty 0
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (next msg2 sigma) (r1 + r2)%R
.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_Empty: 
      fault_weight_state Empty 0
  | fault_weight_state_Next: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (next msg sigma) (r1 + r2)%R
.



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
  protocol_state state -> sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c,v,sigma) sigma').
    + assumption.
    + assumption.
Qed.

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




*)


















