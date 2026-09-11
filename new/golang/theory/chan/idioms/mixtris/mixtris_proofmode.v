(*
   This file is part of Mixtris (https://zenodo.org/records/18749895).

   Copyright (c) Mixtris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

From New.proof Require Import proof_prelude.
From New.golang.theory.chan.au_spec
     Require Export chan_au_send chan_au_new chan_au_recv chan_au_base chan_init.
From iris.proofmode Require Import coq_tactics reduction spec_patterns proofmode.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms.mixtris Require Export mixtris.

(** * Proof automation for Mixtris protocols

    The one thing that genuinely needs automating is *choosing*: when the
    protocol of an endpoint is a mixed choice [p1 <+> p2 <+> ...], every message
    passing rule needs it narrowed down to the single choice matching the
    operation at hand. Which choice that is, is determined by the Go channel the
    operation runs on, via [is_edge_chan]: the channel fixes the edge [i → j],
    the operation fixes [Send] or [Recv], and together they fix the action.

    [ProtoChoice] below does that search by typeclass resolution, left to right
    over the choices, so that discharging a clause of a [select] never requires
    naming the choice or composing [iProto_le_union_l_l]/[iProto_le_union_r_r]
    by hand. *)

(** * Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** * Choice selection

    [ProtoChoice p a m] finds a choice of [p] whose action is [a], and gives the
    subprotocol relation witnessing that [p] may be narrowed to it. The action
    is an input, so resolution backtracks over the choices until one matches. *)
Class ProtoChoice {Σ V} (p : iProto Σ V) (a : action) (m : iMsg Σ V) :=
  proto_choice : ⊢ p ⊑ <a> m.
Global Hint Mode ProtoChoice ! ! ! ! - : typeclass_instances.
Arguments ProtoChoice {_ _} _%_proto _ _%_msg.

(** A protocol given by a [Definition] (in particular a recursive one, via
    [fixpoint]) has no [ProtoChoice] instance of its own; declare an instance of
    [ProtoUnfold] to let resolution look through it. Same convention as Actris's
    and [dsp_proofmode]'s [ProtoUnfold].

    IMPORTANT: always follow such an instance with

      Global Typeclasses Opaque my_prot.

    Without it, resolution can delta-unfold [my_prot] in the *premise* of the
    very instance that just unfolded it, match its own conclusion again, and
    loop forever. The symptom is [mixtris_send_case]/[mixtris_recv_case]
    hanging. See [party_prot] in [channel_mixtris.v] for the pattern. *)
Notation ProtoUnfold p1 p2 := (∀ a m, ProtoChoice p2 a m → ProtoChoice p1 a m).

Section choice.
  Context `{!protoG Σ V}.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoChoice => Hp a m H. by rewrite Hp. Qed.

  (** The choice is this message. *)
  Global Instance proto_choice_here a m : ProtoChoice (<a> m) a m | 0.
  Proof. rewrite /ProtoChoice. iApply iProto_le_refl. Qed.

  (** Otherwise search the left choice, then the right. *)
  Global Instance proto_choice_union_l p1 p2 a m :
    ProtoChoice p1 a m → ProtoChoice (p1 <+> p2) a m | 10.
  Proof.
    rewrite /ProtoChoice => H.
    iApply iProto_le_trans; [iApply iProto_le_union_l_l|iApply H].
  Qed.

  Global Instance proto_choice_union_r p1 p2 a m :
    ProtoChoice p2 a m → ProtoChoice (p1 <+> p2) a m | 20.
  Proof.
    rewrite /ProtoChoice => H.
    iApply iProto_le_trans; [iApply iProto_le_union_r_r|iApply H].
  Qed.

End choice.

Section lang.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context {sem : go.Semantics}.
  Context `{!mixtrisG Σ V}.
  Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
  Collection W := sem + IntoValTyped0.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  (** Discharge an [is_chan] goal straight from an [is_edge_chan] hypothesis.
      A [select] clause asks for the bare [is_chan] of its channel, while the
      rule that consumes the clause asks for the [is_edge_chan] that assigns it
      to an edge; with these instances [iFrame]/[iAssumption] bridge the two, so
      the edge hypothesis only has to be named once, where it is used. *)
  Global Instance is_edge_chan_from_assumption (b : bool) γ ch γch i j :
    FromAssumption b (is_edge_chan γ ch γch i j) (is_chan ch γch V).
  Proof.
    rewrite /FromAssumption. destruct b; simpl; iIntros "#H";
      by iApply is_edge_chan_is_chan.
  Qed.

  Global Instance is_edge_chan_frame (b : bool) γ ch γch i j :
    Frame b (is_edge_chan γ ch γch i j) (is_chan ch γch V) True | 2.
  Proof.
    rewrite /Frame. destruct b; simpl; iIntros "[#H _]";
      by iApply is_edge_chan_is_chan.
  Qed.

  (** ** Sending, with the choice found automatically

      [q] is the endpoint's whole protocol, mixed choice and all; the [Send]
      choice towards [j] is picked out by [ProtoChoice]. The final premise is
      stated as a telescope existential so that a protocol with no binders needs
      no instantiation at all, and one with binders is instantiated with
      [iExists]. *)
  Lemma mixtris_select_send {TT : tele}
      γ ch γch i j q m (tv : TT -t> V) (tP : TT -t> iProp Σ)
      (tp : TT -t> iProto Σ V) (v : V) Φ :
    ProtoChoice q (Send, j) m →
    MsgTele m tv tP tp →
    £1 -∗
    is_edge_chan γ ch γch i j -∗
    i ↣[γ] q -∗
    (∃.. x : TT, ⌜ v = tele_app tv x ⌝ ∗ tele_app tP x ∗
                 ▷ (i ↣[γ] tele_app tp x -∗ Φ)) -∗
    send_au γch V v Φ.
  Proof.
    rewrite /ProtoChoice /MsgTele.
    iIntros (Hc Hm) "H£ #He Hown H".
    iDestruct "H" as (x) "(-> & HP & HΦ)".
    iDestruct (mixtris_own_le _ _ _
                 (<![j]> MSG tele_app tv x; tele_app tp x)%proto
                with "Hown [HP]") as "Hown".
    { iIntros "!>". iApply iProto_le_trans; [iApply Hc|]. rewrite Hm.
      iApply iProto_le_trans; [iApply (iProto_le_texist_intro_l _ _ x)|].
      by iFrame "HP". }
    iApply (mixtris_send_au with "H£ He Hown [] HΦ").
    by rewrite iMsg_base_eq.
  Qed.

  (** ** Receiving, with the choice found automatically *)
  Lemma mixtris_select_recv {TT : tele}
      γ ch γch i j q m (tv : TT -t> V) (tP : TT -t> iProp Σ)
      (tp : TT -t> iProto Σ V) Φ :
    ProtoChoice q (Recv, i) m →
    MsgTele m tv tP tp →
    £1 -∗
    is_edge_chan γ ch γch i j -∗
    j ↣[γ] q -∗
    ▷ (∀.. x : TT, tele_app tP x -∗ j ↣[γ] tele_app tp x -∗
                   Φ (tele_app tv x) true) -∗
    recv_au γch V Φ.
  Proof.
    rewrite /ProtoChoice /MsgTele.
    iIntros (Hc Hm) "H£ #He Hown HΦ".
    iDestruct (mixtris_own_le _ _ _
                 (<?[i].. x> MSG tele_app tv x {{ tele_app tP x }};
                             tele_app tp x)%proto with "Hown []") as "Hown".
    { iIntros "!>". iApply iProto_le_trans; [iApply Hc|]. by rewrite Hm. }
    iApply (mixtris_recv_au with "H£ He Hown").
    iIntros "!>" (w q') "Hm Hown".
    rewrite iMsg_texist_exist. iDestruct "Hm" as (x) "Hm".
    rewrite iMsg_base_eq /=. iDestruct "Hm" as "(%Hv & #Heq & HP)". subst.
    rewrite later_equivI_1.
    iApply ("HΦ" $! x with "HP"). iApply (mixtris_own_le with "Hown").
    iNext. iRewrite -"Heq". iApply iProto_le_refl.
  Qed.

  (** ** Committed send and receive, with the choice found automatically

      These are the same rules without a surrounding [select]: a bare
      [chan.send] / [chan.receive] on a channel assigned to the right edge. *)
  Lemma wp_mixtris_send' {TT : tele} (x : TT)
      γ ch γch i j q m (tv : TT -t> V) (tP : TT -t> iProp Σ)
      (tp : TT -t> iProto Σ V) :
    ProtoChoice q (Send, j) m →
    MsgTele m tv tP tp →
    {{{ is_edge_chan γ ch γch i j ∗ i ↣[γ] q ∗ tele_app tP x }}}
      chan.send t #ch #(tele_app tv x)
    {{{ RET #(); i ↣[γ] tele_app tp x }}}.
  Proof using W.
    iIntros (Hc Hm Φ) "(#He & Hown & HP) HΦ".
    iDestruct (is_edge_chan_is_chan with "He") as "#Hch".
    iApply (chan.wp_send with "Hch"). iIntros "(H£ & _)".
    iApply (mixtris_select_send with "H£ He Hown [HP HΦ]").
    iExists x. iFrame "HP". by iSplit.
  Qed.

  Lemma wp_mixtris_recv' {TT : tele}
      γ ch γch i j q m (tv : TT -t> V) (tP : TT -t> iProp Σ)
      (tp : TT -t> iProto Σ V) :
    ProtoChoice q (Recv, i) m →
    MsgTele m tv tP tp →
    {{{ is_edge_chan γ ch γch i j ∗ j ↣[γ] q }}}
      chan.receive t #ch
    {{{ x, RET (#(tele_app tv x), #true);
        j ↣[γ] tele_app tp x ∗ tele_app tP x }}}.
  Proof using W.
    iIntros (Hc Hm Φ) "[#He Hown] HΦ".
    iDestruct (is_edge_chan_is_chan with "He") as "#Hch".
    iApply (chan.wp_receive with "Hch"). iIntros "(H£ & _)".
    iApply (mixtris_select_recv with "H£ He Hown").
    iIntros "!>" (x) "HP Hown".
    iApply "HΦ". iFrame.
  Qed.

End lang.

(** * Tactics

    A clause of [chan.wp_select_blocking] comes with a pile of existentials
    (the element type, the channel, its ghost names, the typeclass instances)
    and a pure equation identifying the channel; [mixtris_case] discharges all
    of that from the [is_edge_chan] hypothesis it is given, leaving just the
    atomic update. Then [mixtris_send_case] / [mixtris_recv_case] apply the
    corresponding rule, with the choice resolved by typeclass search. *)

Tactic Notation "mixtris_case" :=
  repeat iExists _; iSplitL ""; [done|]; iFrame "#".

Tactic Notation "mixtris_send_case" "with" constr(pat) :=
  mixtris_case; iApply (mixtris_select_send with pat).

Tactic Notation "mixtris_recv_case" "with" constr(pat) :=
  mixtris_case; iApply (mixtris_select_recv with pat).
