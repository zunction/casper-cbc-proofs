From Casper
Require Import vlsm composed_vlsm composed_vlsm_projections indexed_vlsm.

Definition indexed_vlsm_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_vlsm IS (inhabits i))
    (@indexed_vlsm_composed_instance oindex message Heqd IS (inhabits i))
    i
  .

Definition indexed_vlsm_constrained_projection
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> VLSM message)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_vlsm_constrained IS (inhabits i) constraint)
    (@indexed_vlsm_constrained_composed_instance oindex message Heqd IS (inhabits i) constraint)
    i
  .

