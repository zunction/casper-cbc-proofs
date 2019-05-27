Require Import List.

Require Import Casper.sorted_lists.
Require Import Casper.LightStates.messages.

Definition state : Set := list message.
Definition state_lt := @list_lex message message_lt.
