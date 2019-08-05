Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation.
Import ListNotations.  
From Casper
Require Import preamble ListExtras ListSetExtras RealsExtras protocol fullnode.

(* First trying to construct something of this type : *)
Class PartialOrder :=
  { A : Type;
    A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True;
    R : A -> A -> Prop;
    R_refl :> Reflexive R;
    R_trans :> Transitive R;
  }.

(* Using only an abstract instance of CBC_protocol *) 
(* Won't work because we need more stuff than is in there 
Context (H_prot : `{CBC_protocol}). *)

Variable fullnode.C. 
Definition pstate : Type := {s : sorted_state | protocol_state s}. 

Definition pstate_proj1 (p : pstate) : state :=
  proj1_sig p. 

Coercion pstate_proj1 : pstate >-> state.

Lemma pstate_eq_dec : forall (p1 p2 : pstate), {p1 = p2} + {p1 <> p2}.
Proof.
  intros. destruct p1, p2.
Admitted.

Lemma pstate_inhabited : exists (p1 : pstate), True.
Proof. Admitted.

Definition pstate_rel : pstate -> pstate -> Prop :=
  fun p1 p2 => reach (pstate_proj1 p1) (pstate_proj1 p2).

Lemma pstate_rel_refl : Reflexive pstate_rel.
Proof.
  red. intro p.
  destruct p as [p about_p].
  red. simpl. (* CBC_protocol is not quite strong enough to prove this. *)
Admitted.

Lemma pstate_rel_trans : Transitive pstate_rel. 
Proof. 
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  unfold pstate_rel in *; simpl in *.
  now eapply reach_trans with p2.
Qed.

Instance level0 : PartialOrder :=
  { A := pstate;
    A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    R := pstate_rel;
    R_refl := pstate_rel_refl;
    R_trans := pstate_rel_trans;
  }.

Class PartialOrderNonLCish `{PartialOrder} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        R a a1 /\ R a a2 /\
        ~ exists (a' : A), R a1 a' /\ R a2 a';
  }.

(* Now we want to define something like this. *)
