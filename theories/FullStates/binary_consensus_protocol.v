(*******************************)
(** Binary consensus protocol **)
(*******************************)

Require Import Coq.Reals.Reals.
Require Import List.
Require Import Coq.Lists.ListSet.
Import ListNotations.


Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.latest_honest_estimate_driven_estimator.


Module BinC <: Casper.FullStates.consensus_values.Consensus_Values.

(** In order make an instance of module Consensus_Values 
    we are required to have inside our module a list of 
    Definitions and Lemmas that have the same name and types 
    as those listed in the module type's Consensus_Values.

**)

(** The kernel does not recognize yet that a parameter can be 
    instantiated by an inductive type. We rename the inductive type 
    and give a definition to map the old name to the new name.
**)

Inductive binC : Set := 
  | zero : binC 
  | one : binC
  .

Definition C := binC.

Definition c_compare (c1 : C) (c2 : C) : comparison :=
  match c1, c2 with
    | zero, zero => Eq
    | zero, one => Lt
    | one, zero => Gt
    | one, one => Eq
  end.

Definition c_compare_strict_order : CompareStrictOrder c_compare.
Proof.
  unfold CompareStrictOrder. split.
  - constructor.
    + intros Hc. 
      destruct x
    ; destruct y
    ; try reflexivity
    ; try inversion Hc
    .
    + intros H; subst.
      unfold c_compare. destruct y; reflexivity.
  - unfold CompareTransitive. intros x y z comp Hxy Hyz.
    destruct x
  ; destruct y
  ; destruct z
  ; try assumption
  ; try ( unfold c_compare in Hxy; subst ;
          unfold c_compare in Hyz; subst ;
          inversion Hyz
        )
    .
Qed.

Definition c_non_empty : exists c : C, True.
Proof.
  exists one. reflexivity.
Qed.

End BinC.


(*
Definition score (c:C) (sigma:state) : R :=
  fold_right Rplus R0  
    (filter (fun v => In c (le sigma v)) (observed sigma))
  .
*)

(*
Definition estimator : state -> C -> Prop :=
  forall sigma,
  match (score zero sigma) (score one sigma) with
    | LT => one
    | GT => zero
    | Eq => 
*)







  