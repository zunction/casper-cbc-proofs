Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.

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

(** Hash sets **)
Definition hash_lex := @list_lex hash hash_lt. 
Definition add_in_hash_set := @add_in_sorted hash hash_lt.

(** Messages **)

Definition message : Set := C * V * list hash.

Variable Hash : message -> hash.

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


Inductive Hstate : state -> list hash -> Prop :=
  | Hstate_nil :  Hstate [] []
  | Hstate_cons : forall msg sigma hs hs',
       Hstate sigma hs ->
       add_in_hash_set (Hash msg) hs hs' ->
       Hstate (msg :: sigma) hs'.

Theorem Hstate_sorted : forall sigma hs,
  Hstate sigma hs -> LocallySorted hash_lt hs.
Proof.
  induction sigma; intros.
  - inversion H; subst. constructor.
  - inversion H; subst. apply IHsigma in H2.
    apply (add_in_sorted_sorted hash_lt (Hash a) hs0); try assumption.
    apply hash_lt_storder.
Qed.

(***************)
(** Estimator **)
(***************)

Variable epsilon : state -> C -> Prop.

Axiom epsilon_total : forall s : state, exists c : C, epsilon s c.


(********************)
(* State properties *)
(********************)

Definition state_sorted : state -> Prop := LocallySorted message_lt.


Inductive fault_weight_msg : message -> message -> R -> Prop :=
  | fault_weight_v_diff: forall c1 c2 v1 v2 msg1 msg2,
      v1 <> v2 ->
      fault_weight_msg (c1,v1,msg1) (c2,v2,msg2) 0
  | fault_weight_c_msg: forall c v msg,
      fault_weight_msg (c,v,msg) (c,v,msg) 0
  | fault_weight_msg1: forall c1 c2 v msg1 msg2,
      In (Hash (c1,v,msg1)) msg2 ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) 0
  | fault_weight_msg2: forall c1 c2 v msg1 msg2,
      In (Hash (c2,v,msg2)) msg1 ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) 0
  | fault_weight_next: forall c1 c2 v msg1 msg2,
      c1 <> c2 ->
      msg1 <> msg2 ->
      not (In (Hash (c1,v,msg1)) msg2) ->
      not (In (Hash (c2,v,msg2)) msg2) ->
      fault_weight_msg (c1,v,msg1) (c2,v,msg2) (weight v)
  .

Inductive fault_weight_message_state : message -> state -> R -> Prop :=
  | fault_weight_message_state_nil: forall msg,
      fault_weight_message_state msg [] 0
  | fault_weight_message_state_cons: forall msg1 msg2 sigma r1 r2,
      fault_weight_message_state msg1 sigma r1 ->
      fault_weight_msg msg1 msg2 r2 ->
      fault_weight_message_state msg1 (msg2 :: sigma) (r1 + r2)%R
.

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_nil: 
      fault_weight_state [] 0
  | fault_weight_state_cons: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (msg :: sigma) (r1 + r2)%R
.


(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The valid message condition **)
Definition valid_msg_condition (c : C) (sigma : state) : Prop :=
    epsilon sigma c.

(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  forall r,
  fault_weight_state sigma r ->
  (r <= t)%R.

Inductive protocol_state : state -> Prop :=
  | protocol_state_nil : protocol_state []
  | protocol_state_cons : forall c v sigma hsigma sigma' sigma'',
      protocol_state sigma ->
      protocol_state sigma' ->
      valid_msg_condition c sigma ->
      Hstate sigma hsigma ->
      @add_in_sorted message message_lt (c, v, hsigma) sigma' sigma'' ->
      fault_tolerance_condition sigma'' ->
      protocol_state sigma''
.

Theorem protocol_state_sorted : forall state,
  protocol_state state -> LocallySorted message_lt state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted message_lt (c,v,hsigma) sigma'); try assumption.
    apply message_lt_storder.
Qed.

Theorem protocol_state_message_sorted : forall c v hs state,
  protocol_state state ->
  In (c,v,hs) state ->
  LocallySorted hash_lt hs.
Proof.
  intros.
  induction H.
  - inversion H0.
  - apply (add_in_sorted_in (c0, v0, hsigma) (c, v, hs) sigma' sigma'' H4) in H0.
    destruct H0.
    + inversion H0; subst. apply (Hstate_sorted sigma). assumption.
    + apply IHprotocol_state2. assumption.
Qed.
