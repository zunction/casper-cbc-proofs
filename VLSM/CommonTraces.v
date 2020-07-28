From Coq Require Import List Streams.
From Coq Require Import Program.Equality.
From CasperCBC Require Import Lib.SsrExport Lib.Traces Lib.TraceProperties Lib.StreamExtras Lib.Preamble VLSM.Common.
Import ListNotations.

Section VLSM.

Context `{vlsm : VLSM}.

Record tr_data := mkTrData { tr_label : label; tr_input : option message; tr_output : option message }.

Local Notation trace := (@trace state tr_data).

CoInductive protocol_trace : trace -> Prop :=
| protocol_trace_nil : forall (s : state), protocol_state_prop vlsm s -> protocol_trace (Tnil s)
| protocol_trace_further : forall (s : state) (d : tr_data) (tr : trace),
    protocol_trace tr ->
    protocol_transition vlsm (tr_label d) (s, tr_input d) (hd tr, tr_output d) ->
    protocol_trace (Tcons s d tr).

Definition protocol_ptrace tr :=
  protocol_trace tr /\ initial_state_prop (hd tr).

Fixpoint protocol_trace_finite_transition_items (tr : trace) (h: finite tr) {struct h} : list transition_item :=
  match tr as tr' return (finite tr' -> _) with
  | Tnil s => fun _ => []
  | Tcons s d tr => fun h =>
     {| l := tr_label d; input := tr_input d; destination := hd tr; output := tr_output d |} ::
      protocol_trace_finite_transition_items tr (invert_finite_delay h)
  end h.

Program CoFixpoint protocol_trace_infinite_transition_items (tr : trace) (h: infinite tr) : Stream transition_item :=
match tr with
| Tnil _ => False_rect _ _
| Tcons s d tr =>
  Cons {| l := tr_label d; input := tr_input d; destination := hd tr; output := tr_output d |}
       (protocol_trace_infinite_transition_items tr _)
end.
Next Obligation.
by inversion h.
Defined.
Next Obligation.
by inversion h; subst.
Defined.

Lemma protocol_trace_finite_finite_protocol_trace_from : forall tr (h:finite tr), protocol_trace tr ->
 finite_protocol_trace_from vlsm (hd tr) (protocol_trace_finite_transition_items tr h).
Proof.
refine (fix IH tr h {struct h} := _).
case: tr h => [s|s d tr] h Htr /=.
- dependent inversion h; subst => /=.
  inversion Htr; subst.
  by apply finite_ptrace_empty.
- dependent inversion h; subst => /=.
  inversion Htr; subst.
  apply finite_ptrace_extend => //.
  by apply IH.
Qed.

Lemma protocol_trace_infinite_infinite_protocol_trace_from : forall tr (h:infinite tr), protocol_trace tr ->
 infinite_protocol_trace_from vlsm (hd tr) (protocol_trace_infinite_transition_items tr h).
Proof.
cofix CIH.
destruct tr; first by move => h; inversion h. 
move => h Htr /=.
inversion Htr; subst.
dependent inversion h; subst.
rewrite -(recons (protocol_trace_infinite_transition_items _ _)).
simpl.
apply infinite_ptrace_extend => //.
by apply CIH.
Qed.

Fixpoint transition_items_list_protocol_trace (s : state) (ls : list transition_item) : trace :=
match ls with
| [] => Tnil s
| ti :: ls' =>
  Tcons s {| tr_label := l ti; tr_input := input ti; tr_output := output ti |}
   (transition_items_list_protocol_trace (destination ti) ls')
end.

CoFixpoint transition_items_stream_protocol_trace (s : state) (st : Stream transition_item) : trace :=
match st with
| Cons ti st' =>
  Tcons s {| tr_label := l ti; tr_input := input ti; tr_output := output ti |}
   (transition_items_stream_protocol_trace (destination ti) st')
end.

Lemma transition_items_list_protocol_trace_hd_nil : forall l s0 s1,
 Tnil s0 = transition_items_list_protocol_trace s1 l ->
 s0 = s1.
Proof.
case => //=.
move => s0 s1 Hs.
by inversion Hs.
Qed.

Lemma transition_items_list_protocol_trace_hd_cons : forall l s0 s1 d tr,
 Tcons s0 d tr = transition_items_list_protocol_trace s1 l ->
 s0 = s1.
Proof.
case => //=.
move => a l s0 s1 d tr Hs.
by inversion Hs.
Qed.

Lemma finite_protocol_trace_from_protocol_trace : forall ls s, finite_protocol_trace_from vlsm s ls ->
 protocol_trace (transition_items_list_protocol_trace s ls).
Proof.
elim => //=.
- move => s Hf.
  inversion Hf; subst.
  by apply protocol_trace_nil.
- move => a l IH s Hf.
  inversion Hf; subst => /=.
  apply protocol_trace_further => /=; last first.
  * have IH' := IH _ H2.
    inversion IH'; subst.
    + by rewrite /= (transition_items_list_protocol_trace_hd_nil _ _ _ H).
    + by rewrite /= (transition_items_list_protocol_trace_hd_cons _ _ _ _ _ H).
  * by apply IH.
Qed.

Lemma infinite_protocol_trace_from_protocol_trace : forall st s, infinite_protocol_trace_from vlsm s st ->
 protocol_trace (transition_items_stream_protocol_trace s st).
Proof.
cofix CIH.
case => ti st' s Hif.
inversion Hif; subst.
rewrite [transition_items_stream_protocol_trace _ _]trace_destr /=.
apply protocol_trace_further.
- by apply CIH.
- by inversion H2; subst.
Qed.

End VLSM.
