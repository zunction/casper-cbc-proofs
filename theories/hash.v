Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Casper.preamble.
Require Import Casper.sorted_lists.

(*******************)
(** Hash universe **)
(*******************)

Parameter hash : Set .

(** Less than order on hashes **)

Parameter hash_lt : hash -> hash -> Prop.

Parameter hash_lt_strict_order: StrictOrder hash_lt.

(** V totally ordered **)

Parameter hash_total_order: TotalOrder hash_lt.

(** Hash sets **)
Definition hash_lex := @list_lex hash hash_lt. 
Definition add_in_hash_set := @add_in_sorted hash hash_lt.

(** TODO: hash_eq_dec **)

