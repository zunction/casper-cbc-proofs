Require Import Casper.preamble.

Require Import Casper.LightStates.consensus_values.
Require Import Casper.LightStates.validators.
Require Import Casper.LightStates.hashes.
Require Import Casper.LightStates.messages.

(*******************)
(** Hash function **)
(*******************)

Module Type Hash_function
        (PCons : Consensus_Values)
        (PVal : Validators)
        (PHash : Hash)
        .

Import PCons.
Import PVal.
Import PHash.

Module PMessages := Messages PCons PVal PHash.
Import PMessages.

Parameter Hash : message -> hash.

Parameter hash_injective : Injective Hash.

End Hash_function.
