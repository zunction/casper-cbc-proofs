Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

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

(** Equality on consensus values **)

Variable c_eq : C -> C -> Prop.

Axiom c_equality_predicate : forall c1 c2,
        c1 = c2 <-> c_eq c1 c2.


(** Less than order on consensus values **)

Variable c_lt : C -> C -> Prop.

Axiom c_lt_transitive: forall c1 c2 c3,
        c_lt c1 c2 -> 
        c_lt c2 c3 -> 
        c_lt c1 c3.

(** C totally ordered **)

Axiom C_totally_ordered: forall c1 c2,
        c1 = c2 \/
        (c_lt c1 c2) \/ 
        (c_lt c2 c1).


(**************************************)
(** Non-empty set of validator names **)
(**************************************)

Variable V : Set .

Axiom V_non_empty : exists v : V, True.


(** Equality on validator names **)

Variable v_eq : V -> V -> Prop.

Axiom v_equality_predicate : forall v1 v2,
        v1 = v2 <-> v_eq v1 v2.


(** Less than order on validator names **)

Variable v_lt : V -> V -> Prop.

Axiom v_lt_transitive: forall v1 v2 v3,
        v_lt v1 v2 -> 
        v_lt v2 v3 -> 
        v_lt v1 v3.

(** V totally ordered **)

Axiom V_totally_ordered: forall v1 v2,
        v1 = v2 \/
       (v_lt v1 v2) \/ 
       (v_lt v2 v1).


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

Inductive state_eq : state -> state -> Prop :=
  | state_eq_Empty : state_eq Empty Empty 
  | state_eq_Next : forall c1 c2 v1 v2 msg1 msg2 sigma1 sigma2,
      c_eq c1 c2 -> 
      v_eq v1 v2 -> 
      state_eq msg1 msg2 ->
      state_eq sigma1 sigma2 ->
      state_eq (add (c1,v1,msg1) to sigma1) (add (c2,v2,msg2) to sigma2)
  .

Theorem state_eq_reflexive:
  forall sigma, state_eq sigma sigma.
Proof.
  induction sigma.
  - constructor.
  - constructor;try assumption.
    + apply c_equality_predicate. reflexivity.
    + apply v_equality_predicate. reflexivity.
Qed.

Theorem state_equality_predicate:
  forall sigma1 sigma2, sigma1 = sigma2 <-> state_eq sigma1 sigma2.
Proof.
  split.
  - intros. subst. apply state_eq_reflexive.
  - intros. induction H.
    + reflexivity.
    + subst. 
      apply c_equality_predicate in H; subst.
      apply v_equality_predicate in H0; subst.
      reflexivity.
Qed.

Inductive state_lt : state -> state -> Prop :=
  | state_lt_Empty : forall c v msg sigma, 
            state_lt Empty (add (c,v,msg) to sigma)
  | state_lt_C : forall c1 c2 v1 v2 msg1 msg2 sigma1 sigma2,
      c_lt c1 c2 ->
      state_lt (add (c1,v1,msg1) to sigma1) (add (c2,v2,msg2) to sigma2)
  | state_lt_V : forall c1 c2 v1 v2 msg1 msg2 sigma1 sigma2,
      c1 = c2 -> 
      v_lt v1 v2 -> 
      state_lt (add (c1,v1,msg1) to sigma1) (add (c2,v2,msg2) to sigma2)
  | state_lt_M : forall c1 c2 v1 v2 msg1 msg2 sigma1 sigma2,
      c1 = c2 -> 
      v1 = v2 -> 
      state_lt msg1 msg2 ->
      state_lt (add (c1,v1,msg1) to sigma1) (add (c2,v2,msg2) to sigma2)
  | state_lt_Next : forall c1 c2 v1 v2 msg1 msg2 sigma1 sigma2,
      c1 = c2 -> 
      v1 = v2 -> 
      msg1 = msg2 ->
      state_lt sigma1 sigma2 ->
      state_lt (add (c1,v1,msg1) to sigma1) (add (c2,v2,msg2) to sigma2)
  .

Theorem state_lt_transitive: forall sigma1 sigma2 sigma3,
    state_lt sigma1 sigma2 ->
    state_lt sigma2 sigma3 ->
    state_lt sigma1 sigma3.
Proof.
  intros. generalize dependent sigma1. induction H0.
  - intros. inversion H.
  - intros. inversion H0; subst.
    + constructor.
    + apply state_lt_C; try assumption. apply c_lt_transitive with c1; try assumption. 
    + apply state_lt_C; try assumption.
    + apply state_lt_C; try assumption.
    + apply state_lt_C; try assumption.
  - intros. inversion H1; subst.
    + constructor.
    + apply state_lt_C; try assumption.
    + apply state_lt_V; try reflexivity. apply v_lt_transitive with v1; try assumption.
    + apply state_lt_V; try reflexivity. assumption.
    + apply state_lt_V; try reflexivity. assumption.
  - intros; subst. inversion H2; subst.
    + constructor.
    + apply state_lt_C; try assumption.
    + apply state_lt_V; try reflexivity; try assumption.
    + apply state_lt_M; try reflexivity; try assumption. apply IHstate_lt; try assumption.
    + apply state_lt_M; try reflexivity; try assumption. 
  - intros; subst. inversion H3; subst.
    + constructor.
    + apply state_lt_C; try assumption.
    + apply state_lt_V; try reflexivity; try assumption.
    + apply state_lt_M; try reflexivity; try assumption.
    + apply state_lt_Next; try reflexivity; try assumption. apply IHstate_lt; try assumption.
Qed.

Theorem state_total_ordered: forall sigma1 sigma2,
    sigma1 = sigma2 \/
    state_lt sigma1 sigma2 \/ 
    state_lt sigma2 sigma1.
Proof.
  intros. generalize dependent sigma2.
  induction sigma1.
  - induction sigma2.
    + left. reflexivity.
    + right. left. apply state_lt_Empty.
  - induction sigma2.
    + right. right. apply state_lt_Empty.
    + destruct (C_totally_ordered c c0); subst.
      (* c = c0 *)  
      * destruct (V_totally_ordered v v0); subst.
        (* v = v0 *)  
        { destruct (IHsigma1_1 sigma2_1); subst.
            (* sigma1_1 = sigma2_1 *)
            { destruct (IHsigma1_2 sigma2_2); subst.
                (* sigma1_2 = sigma2_2 *)
                { left. reflexivity. }
                (* lt sigma1_2 sigma2_2 \/ lt sigma2_2 sigma2_1 *)
                { destruct H. 
                    (* lt sigma1_2 sigma2_2 *)
                    { right. left. apply state_lt_Next. 
                        {reflexivity. }
                        {reflexivity. }
                        {reflexivity. }
                        {assumption. }
                    }
                    (* lt sigma2_2 sigma1_2 *)
                    { right. right. apply state_lt_Next.
                        {reflexivity. }
                        {reflexivity. }
                        {reflexivity. }
                        {assumption. }  
                    }
                 }
             }
            (* lt sigma1_1 sigma2_1 \/ lt sigma2_1 sigma1_1 *)
            {  destruct H. 
              (* lt sigma1_1 sigma2_1 *)
              { right. left. apply state_lt_M. 
                  {reflexivity. }
                  {reflexivity. }
                  {assumption. }
              }
              (* lt sigma2_1 sigma2_1 *)
              { right. right. apply state_lt_M. 
                  {reflexivity. }
                  {reflexivity. }
                  {assumption. }                
              }
            }
        }
        (* lt v v0 \/ lt v0 v *)
        { destruct H.
          (* lt v v0 *)
          { right. left. apply state_lt_V. 
              {reflexivity. }
              {assumption. }          
          }
          (* lt v0 v *)
          {right. right. apply state_lt_V. 
              {reflexivity. }
              {assumption. }            
          }
        } 
     (* lt c c0 \/ lt c0 c *)  
     * destruct H.
        (* lt c c0 *)
        { right. left. apply state_lt_C.
          {assumption. }
        }
        (* lt c0 c *)
        { right. right. apply state_lt_C. 
          {assumption. }
        }
Qed.

(** Messages **)

Definition message := (C * V * state)%type.

Definition next (msg : message) (sigma : state) : state :=
  match msg with
  | (c, v, sigma_msg) => add (c, v, sigma_msg) to sigma
  end.

Definition msg_eq (msg1 msg2 : message) : Prop :=
  state_eq (next msg1 Empty) (next msg2 Empty).

Definition msg_lt (msg1 msg2 : message) : Prop :=
  state_lt (next msg1 Empty) (next msg2 Empty).


Corollary msg_equality_predicate:
  forall msg1 msg2, msg1 = msg2 <-> msg_eq msg1 msg2.
Proof.
  destruct msg1 as [(c1,v1) sigma_msg1].
  destruct msg2 as [(c2,v2) sigma_msg2].
  unfold msg_eq. unfold next.
  split; intros.
  - inversion H; subst. apply state_equality_predicate. reflexivity.
  - apply state_equality_predicate in H. inversion H; subst. reflexivity.
Qed.


Corollary msg_lt_transitive: forall msg1 msg2 msg3,
    msg_lt msg1 msg2 ->
    msg_lt msg2 msg3 ->
    msg_lt msg1 msg3.
Proof.
  destruct msg1 as [(c1, v1) sigma_msg1].
  destruct msg2 as [(c2, v2) sigma_msg2].
  destruct msg3 as [(c3, v3) sigma_msg3].
  unfold msg_lt. unfold next.
  intros.
  apply state_lt_transitive with (add (c2, v2, sigma_msg2)to Empty); assumption.
Qed.

Corollary msg_total_ordered: forall msg1 msg2,
    msg1 <> msg2 ->
    msg_lt msg1 msg2 \/ msg_lt msg2 msg1.
Proof.
  Admitted.

Inductive in_state : message -> state -> Prop :=
  | InStateNow : forall msg msg' sigma', 
          msg = msg' -> 
          in_state msg (next msg' sigma')
  | InStateNext : forall msg msg' sigma', 
          in_state msg sigma' -> 
          in_state msg (next msg' sigma')
  .


(*****************************************************)

Inductive strictly_sorted : state -> Prop :=
  | sorted_Empty : strictly_sorted Empty
  | sorted_Singleton : forall msg, 
          strictly_sorted (next msg Empty)
  | sorted_Next : forall msg  msg' sigma, 
          msg_lt msg msg' -> 
          strictly_sorted (next msg' sigma) -> 
          strictly_sorted (next msg (next msg' sigma))
  .

(* Attempt to define set_state

Inductive set_state : Set :=
    well_formed : forall sigma:state, strictly_sorted sigma -> set_state.

Definition set_state_empty : set_state :=
  well_formed Empty (sorted_Empty).

Definition set_state_singleton (msg : message) : set_state :=
  well_formed (next msg Empty) (sorted_Singleton msg).


Inductive add_in_sorted : message -> set_state -> set_state -> Prop :=
  | add_in_Empty : forall msg,
        add_in_sorted msg set_state_empty (set_state_singleton msg)
  | add_in_Next_eq : forall msg msg' sigma,
          msg_eq msg msg' -> 
          well_formed (next msg' sigma) -> 
          add_in_sorted msg (next msg' sigma) (next msg' sigma)
  .
*)


Inductive add_in_sorted : message -> state -> state -> Prop :=
   | add_in_Empty : forall msg,
          add_in_sorted msg Empty (next msg Empty)
   | add_in_Next_eq : forall msg msg' sigma,
          msg = msg' ->  
          add_in_sorted msg (next msg' sigma) (next msg' sigma)
   | add_in_Next_lt : forall msg msg' sigma,
          msg_lt msg msg' ->  
          add_in_sorted msg (next msg' sigma) (next msg (next msg' sigma))
   | add_in_Next_gt : forall msg msg' sigma sigma',
          msg_lt msg' msg ->
          add_in_sorted msg sigma sigma' ->
          add_in_sorted msg (next msg' sigma) (next msg' sigma')
  .

Lemma add_is_next : forall c v sigma_msg sigma,
  add (c, v, sigma_msg)to sigma = next (c, v, sigma_msg) sigma.
Proof.
  intros. unfold next. reflexivity.
Qed.
    
Theorem add_in_sorted_sorted : forall msg sigma sigma',
  strictly_sorted sigma -> add_in_sorted msg sigma sigma' -> strictly_sorted sigma'.
Proof.
  intros msg sigma sigma' Hsorted. 
  generalize dependent msg. generalize dependent sigma'.
  induction Hsorted.
  - intros. inversion H; subst;
    try (inversion H; destruct msg' as [(c', v') sigma_msg']; unfold next in H0; inversion H0).
    constructor.
  - intros. inversion H; subst.
    + destruct msg as [(c, v) sigma_msg]. unfold next in H2. inversion H2.
    + rewrite H0. constructor.
    + constructor. assumption. rewrite H0. constructor.
    + destruct msg as [(c, v) sigma_msg].      destruct msg' as [(c', v') sigma_msg']. 
      unfold next in H0. inversion H0; subst.
      inversion H3; subst;
      try (destruct msg' as [(c', v') sigma_msg']; unfold next in H2; inversion H2).
      * constructor. assumption. constructor.
  - intros. inversion H0; subst.
    + constructor.
    + destruct msg as [(c, v) sigma_msg].
      destruct msg' as [(c', v') sigma_msg'].      destruct msg'0 as [(c'0, v'0) sigma_msg'0].
      unfold next in H1. inversion H1; subst.
      rewrite (add_is_next c' v' sigma_msg' sigma). 
      constructor. assumption. assumption.
    + destruct msg as [(c, v) sigma_msg].
      destruct msg' as [(c', v') sigma_msg'].      destruct msg'0 as [(c'0, v'0) sigma_msg'0].
      unfold next in H1. inversion H1; subst.
      constructor. assumption.  
      rewrite (add_is_next c' v' sigma_msg' sigma). 
      constructor. assumption. assumption.
    Admitted.
      


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

Theorem sorted_subset_elements: forall msg sigma1 sigma2, 
    strictly_sorted(sigma1) -> 
    strictly_sorted(sigma2) ->
    sorted_subset sigma1 sigma2 -> 
    in_state msg sigma1 -> 
    in_state msg sigma2.
Proof. 
  Admitted.


Theorem add_sorted :
  forall sigma msg, strictly_sorted sigma -> in_state msg sigma -> add_in_sorted msg sigma sigma.
Proof. 
  Admitted.

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
  protocol_state state -> strictly_sorted state.
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


















