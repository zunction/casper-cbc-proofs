Require Import List.
Import ListNotations.

From Casper
Require Import vlsm.

(* a run is a tuple (s0, loms, (sf,om)) with the meaning:

execution starts in state s0 and uses labels and messages from loms to get to sf, potentially also generating om)

*)
Record proto_run `{VLSM} : Type := mk_proto_run
  { start : initial_state
  ; transitions : list (label * option proto_message)
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
    : vlsm_run_prop {| start := is; transitions := ts ++ [(l, om)]; final := som' |}.

Definition vlsm_run `{VLSM} : Type := { r : proto_run | vlsm_run_prop r }.

Definition vlsm_state_prop `{VLSM} (s : state) : Prop :=
  exists vr : vlsm_run, s = fst (final (proj1_sig vr)).

Definition vlsm_state `{VLSM} : Type := {s : state | vlsm_state_prop s}.

Definition gen_state `{VLSM}
  (vr : vlsm_run)
  : vlsm_state.
exists (fst (final (proj1_sig vr))). exists vr. reflexivity.
Defined.

Definition vlsm_message_prop `{VLSM} (m : proto_message) : Prop :=
  exists vr : vlsm_run, Some m = snd (final (proj1_sig vr)).

Definition vlsm_message `{VLSM} : Type := {m : proto_message | vlsm_message_prop m}.

Definition vlsm_valid `{VLSM}
  (l : label)
  (vsom : vlsm_state * option vlsm_message)
  : Prop
  :=
  valid l (proj1_sig (fst vsom), option_map (@proj1_sig _ _) (snd vsom)).

Definition extend_vlsm_run `{VLSM}
  (vr : vlsm_run)
  (l : label)
  (vom : option vlsm_message)
  (Hv : vlsm_valid l (gen_state vr, vom))
  : vlsm_run.
remember (proj1_sig vr) as r.
remember (option_map (@proj1_sig _ _) vom) as om.
remember (fst (final r)) as s.
remember (transition l (s, om)) as som'.
exists {| start := start r; transitions := transitions r ++ [(l,om)]; final := som' |}.
subst. destruct vr as [sr Hsr].
specialize (extend_run sr Hsr); simpl; intros HExt.
destruct vom as [[m [[mr Hmr] Hm]]|].
- specialize (HExt mr Hmr l).
  unfold vlsm_valid in Hv; simpl in Hv. simpl in Hm. rewrite Hm in Hv.
  specialize (HExt Hv).
  simpl. rewrite Hm. assumption.
- remember (empty_run_initial_state s0) as Hmr; simpl in Hmr.
  remember {| start := s0; transitions := []; final := (proj1_sig s0, None) |} as mr.
  specialize (HExt mr Hmr l); rewrite Heqmr in HExt; simpl in HExt.
  unfold vlsm_valid in Hv; simpl in Hv.
  specialize (HExt Hv).
  simpl. assumption.
Defined.

Lemma next_state_proof `{VLSM}
  (l : label)
  (vsom : vlsm_state * option vlsm_message)
  (Hv : vlsm_valid l vsom)
  : 
  vlsm_state_prop (fst (transition l (proj1_sig (fst vsom),option_map (@proj1_sig _ _) (snd vsom)))).
Proof.
destruct vsom as [[s [sr Hs]] vom].
remember (option_map (@proj1_sig _ _) vom) as om.
simpl.
destruct (transition l (s, om)) as [s' om'] eqn:Ht.
assert (Hv' : vlsm_valid l (gen_state sr, vom))
  by (subst; assumption).
exists (extend_vlsm_run sr l vom Hv').
subst. simpl. rewrite Ht. reflexivity.
Qed.

Lemma next_message_proof `{VLSM}
  (l : label)
  (vsom : vlsm_state * option vlsm_message)
  (Hv : vlsm_valid l vsom)
  (s : state := proj1_sig (fst vsom))
  (om : option proto_message := option_map (@proj1_sig _ _) (snd vsom))
  (t := transition l (s, om))
  (m' : proto_message)
  (Hm : snd t = Some m')
  : vlsm_message_prop m'.
Proof.
  unfold s in *. clear s. unfold t in *; clear t. unfold om in *; clear om.
  destruct vsom as [[s [sr Hs]] vom].
  simpl in *.
  destruct (transition l (s, option_map (proj1_sig (P:=fun m : proto_message => vlsm_message_prop m)) vom)) as (s', om') eqn:Ht.
  simpl in Hm. destruct om' as [m''|]; inversion Hm; subst; clear Hm.
  assert (Hv' : vlsm_valid l (gen_state sr, vom))
    by (subst; assumption).
  exists (extend_vlsm_run sr l vom Hv').
  subst. simpl. rewrite Ht. reflexivity.
Qed.  

Definition vlsm_state_transition `{VLSM}
  (l : label)
  (vsom : vlsm_state * option vlsm_message)
  (Hv : vlsm_valid l vsom)
  (s : state := proj1_sig (fst vsom))
  (om : option proto_message := option_map (@proj1_sig _ _) (snd vsom))
  (t := transition l (s, om))
  : vlsm_state
  := exist _ (fst t) (next_state_proof l vsom Hv).

Lemma vlsm_transition_consistency `{VLSM}
  (l : label)
  (vsom : vlsm_state * option vlsm_message)
  (Hv : vlsm_valid l vsom)
  (s : state := proj1_sig (fst vsom))
  (om : option proto_message := option_map (@proj1_sig _ _) (snd vsom))
  (som' := transition l (s, om))
  (vs' := vlsm_state_transition l vsom Hv)
  : proj1_sig vs' = fst som'.
Proof.
  destruct vsom as [vs ovm].
  unfold vlsm_state_transition in vs'. simpl in *.
  reflexivity.
Qed.

(* Any valid state is either initial, or obtained through a transition from a valid state using a valid message *)
Lemma vlsm_state_prop_iff
  {message}
  `{V : VLSM message}
  : forall s' : state,
  vlsm_state_prop s'
  <-> (exists is : initial_state, s' = proj1_sig is)
  \/ exists (vs : vlsm_state) (l : label) (ovm : option vlsm_message) (Hv : vlsm_valid l (vs, ovm)),
    s' = proj1_sig (vlsm_state_transition l (vs, ovm) Hv).
Proof.
  intros; split.
  - intros [[r Hvr] Hs']. inversion Hvr; subst
    ; try (left; exists s0; reflexivity)
    ; try (left; exists is; reflexivity)
    .
    right.
    assert (Hvs : vlsm_state_prop s)
      by (exists (exist _ state_run Hs); reflexivity).
    exists (exist _ s Hvs).
    exists l.
    destruct (snd (final msg_run)) as [m|] eqn:Hm_eq.
    + assert (Hvm : vlsm_message_prop m)
       by (exists (exist _ msg_run Hm); symmetry; assumption).
      exists (Some (exist _ m Hvm)); simpl. exists Hv.
      reflexivity.
    + exists None; simpl. split; try assumption. reflexivity.
  - intros [[is Heq] | [[s [rs Hs]] [l [ovm [Hv Ht]]]]].
    + exists (exist _ _ (empty_run_initial_state is)); assumption.
    + subst; exists (extend_vlsm_run rs l ovm Hv); reflexivity.
Qed.

(* Any valid message is either initial, or obtained through a transition from a valid state using a valid message *)
Lemma vlsm_message_prop_iff
  {message}
  `{V : VLSM message}
  : forall m' : proto_message,
  vlsm_message_prop m'
  <-> (exists im : initial_message, m' = proj1_sig im)
  \/ exists (vs : vlsm_state) (l : label) (ovm : option vlsm_message) (Hv : vlsm_valid l (vs, ovm)),
    Some m' = snd (transition l (proj1_sig vs, option_map (@proj1_sig _ _) ovm)).
Proof.
  intros; split.
  - intros [[r Hvr] Hm']. inversion Hvr; subst; simpl in Hm'.
    + inversion Hm'.
    + inversion Hm'. left. exists im.  reflexivity.
    + right.
      assert (Hvs : vlsm_state_prop s)
        by (exists (exist _ state_run Hs); reflexivity).
      exists (exist _ s Hvs).
      exists l. simpl.
      destruct (snd (final msg_run)) as [m|] eqn:Hm_eq.
      * assert (Hvm : vlsm_message_prop m)
         by (exists (exist _ msg_run Hm); symmetry; assumption).
        exists (Some (exist _ m Hvm)); simpl. exists Hv.
        assumption. 
      * exists None; simpl. split; try assumption.
  - intros [[is Heq] | [vs [l [ovm [Hv Ht]]]]].
    + exists (exist _ _ (empty_run_initial_message is)). subst; reflexivity. 
    + subst. apply (next_message_proof l (vs, ovm) Hv). symmetry. assumption.
Qed.

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
