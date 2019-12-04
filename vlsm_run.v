Require Import List ListSet.
Import ListNotations.

From Casper
Require Import vlsm.

(* a run is a tuple (s0, loms, (sf,om)) with the meaning:

execution starts in state s0 and uses labels and messages from loms to get to sf, potentially also generating om)

*)
Record proto_run `{VLSM} : Type := mk_proto_run
  { start : initial_state
  ; transitions : list (label * option proto_message * option proto_message)
  ; final : state * option proto_message
  }.

Inductive vlsm_run_prop `{VLSM} : proto_run -> Prop :=
  | empty_run_initial_state
      (is : initial_state)
      (s : state := proj1_sig is)
    : vlsm_run_prop {| start := is; transitions := []; final := (s, None) |}
  | empty_run_initial_message
      (im : initial_message)
      (s : state := proj1_sig s0)
      (om : option proto_message := Some (proj1_sig im))
    : vlsm_run_prop {| start := s0; transitions := []; final := (s, om) |}
  | extend_run
      (state_run : proto_run)
      (Hs : vlsm_run_prop state_run)
      (s := fst (final state_run))
      (is := start state_run)
      (ts := transitions state_run)
      (msg_run : proto_run)
      (Hm : vlsm_run_prop msg_run)
      (om := snd (final msg_run))
      (l : label)
      (Hv : valid l (s, om))
      (som' := transition l (s, om))
    : vlsm_run_prop {| start := is; transitions := ts ++ [(l, om, snd som')]; final := som' |}.

Definition vlsm_run `{VLSM} : Type := { r : proto_run | vlsm_run_prop r }.

Lemma run_is_protocol `{VLSM}
  (vr : vlsm_run)
  : protocol_prop (final (proj1_sig vr)).
Proof.
  destruct vr as [r Hr]; simpl.
  induction Hr; simpl in *; try constructor.
  unfold om in *; clear om. unfold s in *; clear s.
  destruct (final state_run) as [s _om].
  destruct (final msg_run) as [_s om].
  specialize (protocol_generated l s _om IHHr1 _s om IHHr2 Hv). intro. assumption.
Qed.

Lemma protocol_is_run `{VLSM}
  (som' : state * option proto_message)
  (Hp : protocol_prop som')
  : exists vr : vlsm_run, (som' = final (proj1_sig vr)).
Proof.
  induction Hp.
  - exists (exist _ _ (empty_run_initial_state is)); reflexivity.
  - exists (exist _ _ (empty_run_initial_message im)); reflexivity.
  - destruct IHHp1 as [[state_run Hsr] Heqs]. destruct IHHp2 as [[msg_run Hmr] Heqm]. 
    specialize (extend_run state_run Hsr). simpl. intros Hvr.
    specialize (Hvr msg_run Hmr l). simpl in Heqs. simpl in Heqm.
    rewrite <- Heqs in Hvr. rewrite <- Heqm in Hvr. specialize (Hvr Hv).
    exists (exist _ _ Hvr). reflexivity.
Qed.
