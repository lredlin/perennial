(*
   This file is part of Mixtris (https://zenodo.org/records/18749895).

   Copyright (c) Mixtris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

Require Import New.proof.proof_prelude.
From New.golang.theory.chan.au_spec
     Require Export chan_au_base.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms.mixtris
     Require Export proto.
From iris.base_logic.lib Require Import saved_prop.

(** * Mixed Choice Multiparty Session Types (Mixtris) over Go Channels

    This file builds the Mixtris channel layer on top of the logically atomic Go
    channel specifications, in the same way [dsp.v] builds binary dependent
    separation protocols on top of them.

    Mixtris [11] implements an [n]-participant channel as an [n × n] matrix of
    synchronisation cells, where cell [(i,j)] carries messages from [i] to [j],
    and emulates mixed choice by alternating between *uncommitted* [try_send] and
    [try_recv] primitives until one of them succeeds. Two things change here:

    - Go's unbuffered channels already are synchronisation cells, and Go's
      [select] already is mixed choice. A blocking [select] with a mix of send
      and receive cases performs the choice in the runtime, so there is no need
      for the uncommitted primitives or the retry loop. 

    - Rather than materialising all [n × n] cells, the client allocates whatever
      set of Go channels it likes and assigns each one to a directed edge
      [i → j] using [mixtris_chan_init]. A protocol action [<![j]> m] of
      participant [i] may then be discharged on *any* channel assigned to the
      edge [(i,j)]; the channel is named by the program and the edge by the
      protocol, and [is_edge_chan] links the two. Only the edges a protocol
      actually uses need channels, so e.g. a ring of [n] participants needs [n]
      channels rather than [n²].

    A Go channel must be dedicated to a single directed edge. If one channel
    served two edges then a receiver could be handed a value from a participant
    its protocol has no [Recv] choice for, and the rendezvous having already
    happened would have no way to give it back.

    The protocol layer in [proto.v] is used unchanged: a protocol action is
    annotated with the *participant* it communicates with, exactly as in the
    paper, so protocol consistency proofs carry over verbatim.
 *)

Class mixtrisG Σ V := {
  mixtris_protoG :: protoG Σ V;
  mixtris_savedPropG :: savedPropG Σ;
  mixtris_savedPredG :: savedPredG Σ V;
}.

(** Ghost names for a session: the protocol pool, and the number of
    participants in it. Unlike [dsp_names] this does not mention any channels;
    channels are attached to edges one at a time by [mixtris_chan_init]. *)
Record mixtris_names := MixtrisNames {
  mx_proto : gname;
  mx_nparties : nat;
}.

Section mixtris.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!mixtrisG Σ V}.

Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
Collection W := sem + IntoValTyped0.

Let N := nroot .@ "mixtris".

(** ** The per-channel invariant

    A party that parks on a channel has to recognise its own continuation when
    it wakes up again. The two saved-proposition cells [γs] and [γr] are that
    link: they are wholly owned by the invariant while nobody is parked, and
    split into halves for the duration of a park. *)
Definition snd_cell_free (γs : gname) : iProp Σ :=
  ∃ Φ, saved_prop_own γs (DfracOwn (1/2)) Φ ∗ saved_prop_own γs (DfracOwn (1/2)) Φ.
Definition rcv_cell_free (γr : gname) : iProp Σ :=
  ∃ Ψ, saved_pred_own γr (DfracOwn (1/2)) Ψ ∗ saved_pred_own γr (DfracOwn (1/2)) Ψ.

(** What a receiver on the edge [i → j] ends up owning once a value has been
    exchanged against message [m]. *)
Definition recv_result (γp : gname) (j : nat) (m : iMsg Σ V) : V → iProp Σ :=
  λ v, (∃ p, iMsg_car m v (Next p) ∗ iProto_own γp j p)%I.

(** One Go channel, dedicated to the directed edge [i → j]. Buffered and closed
    states are ruled out: these channels are unbuffered and never closed.

    The two "pending" states hold the parked party's [iProto_own], which is what
    lets the party arriving second run [iProto_step] at a single atomic step.
    The two "commit" states hold the result the arriving party left behind. Note
    that the parked party's contribution is spelled out concretely rather than
    hidden behind an opaque continuation; that is what makes [SndWait] and
    [RcvDone] refutable for a second sender, and [RcvWait] and [SndDone]
    refutable for a second receiver, since [iProto_own] is exclusive. *)
Definition chan_slot_inv
    (γp : gname) (γch : chan_names) (i j : nat) (γs γr : gname) : iProp Σ :=
  ∃ s, own_chan γch V s ∗
    match s with
    | chanstate.Idle =>
        snd_cell_free γs ∗ rcv_cell_free γr
    | chanstate.SndWait v =>
        (∃ m p, saved_prop_own γs (DfracOwn (1/2)) (iProto_own γp i p) ∗
                iProto_own γp i (<(Send, j)> m) ∗ iMsg_car m v (Next p)) ∗
        rcv_cell_free γr
    | chanstate.RcvDone =>
        (∃ p, saved_prop_own γs (DfracOwn (1/2)) (iProto_own γp i p) ∗
              ▷ iProto_own γp i p) ∗
        rcv_cell_free γr
    | chanstate.RcvWait =>
        snd_cell_free γs ∗
        (∃ m, saved_pred_own γr (DfracOwn (1/2)) (recv_result γp j m) ∗
              iProto_own γp j (<(Recv, i)> m))
    | chanstate.SndDone v =>
        snd_cell_free γs ∗
        (∃ m, saved_pred_own γr (DfracOwn (1/2)) (recv_result γp j m) ∗
              ▷ recv_result γp j m v)
    | _ => False
    end.

(** ** Session and endpoint ownership *)

(** The protocol pool is consistent and governs [mx_nparties] participants. *)
Definition mixtris_ctx (γ : mixtris_names) : iProp Σ :=
  inv (N .@ "ctx") (iProto_ctx γ.(mx_proto) γ.(mx_nparties)).

(** [ch] is a Go channel of this session carrying messages from participant [i]
    to participant [j]. Persistent, and presented at each use site: this is what
    it means to annotate a protocol action with a channel. *)
Definition is_edge_chan
    (γ : mixtris_names) (ch : loc) (γch : chan_names) (i j : nat) : iProp Σ :=
  ∃ γs γr,
    is_chan ch γch V ∗
    inv (N .@ "chan") (chan_slot_inv γ.(mx_proto) γch i j γs γr).

(** Exclusive permission to drive participant [i] according to protocol [p].
    Unlike the Mixtris endpoint [(m,i)] this has no runtime counterpart: the Go
    program just uses the channels directly. *)
Definition mixtris_own
    (γ : mixtris_names) (i : nat) (p : iProto Σ V) : iProp Σ :=
  mixtris_ctx γ ∗ iProto_own γ.(mx_proto) i p.

Notation "i ↣[ γ ] p" := (mixtris_own γ i p%proto) (at level 20, format "i  ↣[  γ  ]  p").

Global Instance is_edge_chan_pers γ ch γch i j : Persistent (is_edge_chan γ ch γch i j).
Proof. apply _. Qed.

Lemma is_edge_chan_is_chan γ ch γch i j :
  is_edge_chan γ ch γch i j -∗ is_chan ch γch V.
Proof. iIntros "H". by iDestruct "H" as (??) "[$ _]". Qed.

Global Instance mixtris_own_ne γ i : NonExpansive (mixtris_own γ i).
Proof. solve_proper. Qed.
Global Instance mixtris_own_proper γ i : Proper ((≡) ==> (≡)) (mixtris_own γ i).
Proof. apply (ne_proper _). Qed.

(** Weakening along the subprotocol relation. For mixed choice this is how a
    choice is made: [iProto_le_union_l_l : p1 <+> p2 ⊑ p1]. *)
Lemma mixtris_own_le γ i p1 p2 : i ↣[γ] p1 -∗ ▷ (p1 ⊑ p2) -∗ i ↣[γ] p2.
Proof.
  iIntros "[$ Hp] Hle". by iApply (iProto_own_le with "Hp").
Qed.

Lemma mixtris_own_excl γ i p1 p2 : i ↣[γ] p1 -∗ i ↣[γ] p2 -∗ False.
Proof.
  iIntros "[_ H1] [_ H2]". by iDestruct (iProto_own_excl with "H1 H2") as "[]".
Qed.

(** ** Initialisation *)

(** Allocate a session from a consistent pool of protocols. No channels yet;
    the client decides how many to make and which edge each one serves. *)
Lemma mixtris_init E (ps : list (iProto Σ V)) :
  ▷ iProto_consistent ps ={E}=∗
  ∃ γ, ⌜ γ.(mx_nparties) = length ps ⌝ ∗ [∗ list] i ↦ p ∈ ps, i ↣[γ] p.
Proof.
  iIntros "Hcons".
  iMod (iProto_init with "Hcons") as (γp) "[Hctx Hown]".
  set γ := MixtrisNames γp (length ps).
  iMod (inv_alloc (N .@ "ctx") _ (iProto_ctx γp (length ps)) with "[Hctx]") as "#Hinv".
  { by iFrame. }
  iModIntro. iExists γ. iSplit; [done|].
  iApply (big_sepL_impl with "Hown").
  iIntros "!>" (???) "?". by iFrame "#∗".
Qed.

(** Assign a fresh unbuffered Go channel to the edge [i → j]. *)
Lemma mixtris_chan_init E γ (ch : loc) γch (i j : nat) :
  is_chan ch γch V -∗
  own_chan γch V chanstate.Idle ={E}=∗
  is_edge_chan γ ch γch i j.
Proof.
  iIntros "#Hch Hown".
  iMod (saved_prop_alloc True%I (DfracOwn 1) ltac:(done)) as (γs) "Hs".
  iDestruct "Hs" as "[Hs1 Hs2]".
  iMod (saved_pred_alloc (λ _, True%I) (DfracOwn 1) ltac:(done)) as (γr) "Hr".
  iDestruct "Hr" as "[Hr1 Hr2]".
  iMod (inv_alloc (N .@ "chan") _
          (chan_slot_inv γ.(mx_proto) γch i j γs γr) with "[Hown Hs1 Hs2 Hr1 Hr2]") as "#Hinv".
  { iIntros "!>". iExists chanstate.Idle. iFrame. }
  iModIntro. iFrame "#".
Qed.

(** The intended way to set a session up: one map from directed edges to Go
    channels, initialised in one step. Keying by the edge means an edge cannot
    accidentally be given two channels — which would type-check but deadlock,
    since a send on one would never meet a receive on the other. *)
Definition is_edge_chans
    (γ : mixtris_names) (chs : gmap (nat * nat) (loc * chan_names)) : iProp Σ :=
  [∗ map] e ↦ c ∈ chs, is_edge_chan γ c.1 c.2 e.1 e.2.

Global Instance is_edge_chans_pers γ chs : Persistent (is_edge_chans γ chs).
Proof. apply _. Qed.

Lemma mixtris_chans_init E γ (chs : gmap (nat * nat) (loc * chan_names)) :
  ([∗ map] c ∈ chs, is_chan c.1 c.2 V ∗ own_chan c.2 V chanstate.Idle) ={E}=∗
  is_edge_chans γ chs.
Proof.
  iIntros "H". rewrite /is_edge_chans.
  iApply big_sepM_fupd. iApply (big_sepM_impl with "H").
  iIntros "!>" (e c ?) "[#Hch Hown]".
  by iApply (mixtris_chan_init with "Hch Hown").
Qed.

(** Look the channel for one edge up. *)
Lemma is_edge_chans_lookup γ chs i j ch γch :
  chs !! (i, j) = Some (ch, γch) →
  is_edge_chans γ chs -∗ is_edge_chan γ ch γch i j.
Proof.
  iIntros (Hl) "H". by iDestruct (big_sepM_lookup with "H") as "H".
Qed.

(** ** Sending *)

(** The atomic-update form of the send rule.

    This is what a [SendCase] clause of [chan.wp_select_blocking] needs. The
    clauses of a [select] are combined with ∧, so every clause is discharged from
    the same [i ↣[γ] q] — each one picking a different choice of [q] via
    [mixtris_own_le] — and only the clause that wins consumes it. That is exactly
    Mixtris's mixed choice, performed by the Go runtime in one step rather than
    emulated by a retry loop over uncommitted primitives. *)
(* Open the slot invariant and the protocol context, then hand the arm the
   invariant's half of [own_chan].  Mixtris edges are unbuffered and never
   closed, so the [Buffered]/[Closed] arms are discharged from [Hrest : False]. *)
Local Ltac mx_open :=
  iMod (inv_acc with "Hslot") as "[IH Hcloses]"; [solve_ndisj|];
  iMod (inv_acc with "Hctx") as "[Hctxi Hclosec]"; [solve_ndisj|];
  iDestruct "IH" as (s) "[>Hoc Hrest]";
  iCombine "Hrest Hctxi" as "Hrc";
  iMod (lc_fupd_elim_later with "Hlc Hrc") as "[Hrest Hctxi]".
(* One credit strips the slot invariant and the client's continuation together. *)
Local Ltac mx_openc :=
  iMod (inv_acc with "Hslot") as "[IH Hcloses]"; [solve_ndisj|];
  iMod (inv_acc with "Hctx") as "[Hctxi Hclosec]"; [solve_ndisj|];
  iDestruct "IH" as (s) "[>Hoc Hrest]";
  iCombine "Hrest Hctxi HΦ" as "Hrc";
  iMod (lc_fupd_elim_later with "Hlc Hrc") as "[Hrest [Hctxi HΦ]]".
Local Ltac mx_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
Local Ltac mx_step st h :=
  mx_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %h;
  iMod (own_chan_halves_update st with "Hoc Himpl") as "[H1 H2]";
  [ simpl in h |- *; lia | ].

Lemma mixtris_send_au γ ch γch i j (v : V) m (p : iProto Σ V) Φ :
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  is_edge_chan γ ch γch i j -∗
  i ↣[γ] (<(Send, j)> m) -∗
  iMsg_car m v (Next p) -∗
  ▷ (i ↣[γ] p -∗ Φ) -∗
  send_au γch V v Φ.
Proof.
  iIntros "(H£1 & H£2 & H£3 & H£4) #Hedge Hown Hm HΦ".
  iDestruct "Hedge" as (γs γr) "[#Hch #Hslot]".
  iDestruct "Hown" as "[#Hctx Hp]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : a receiver is parked, so complete the exchange here *)
    iIntros "[Hlc Himpl]". mx_openc. mx_step (chanstate.SndDone v) Hcv1.
    iDestruct "Hrest" as "[Hsfree (%m2 & Hr1 & Hpj)]".
    iMod (iProto_step with "Hctxi Hp Hpj Hm") as "Hstep".
    iMod (lc_fupd_elim_later with "H£2 Hstep") as (p2) "(Hm2 & Hctxi & Hpi & Hpj)".
    iMod ("Hclosec" with "[$Hctxi]") as "_".
    iMod ("Hcloses" with "[H1 Hsfree Hr1 Hm2 Hpj]") as "_".
    { iNext. iExists (chanstate.SndDone v). iFrame "H1 Hsfree".
      iExists m2. iFrame "Hr1". iNext. iExists p2. iFrame. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* send_slow_path_au : nobody is here yet, so park the offer *)
    iIntros "[Hlc Himpl]". mx_openc. mx_step (chanstate.SndWait v) Hcv2.
    iDestruct "Hrest" as "[[%Φ0 [Hsa Hsb]] Hrfree]".
    iMod (saved_prop_update_halves (iProto_own γ.(mx_proto) i p)
           with "Hsa Hsb") as "[Hs1 Hs2]".
    iMod ("Hclosec" with "[$Hctxi]") as "_".
    iMod ("Hcloses" with "[H1 Hs1 Hp Hm Hrfree]") as "_".
    { iNext. iExists (chanstate.SndWait v). iFrame "H1 Hrfree".
      iExists m, p. iFrame. }
    iModIntro. iFrame "H2".
    (* phase two: the receiver ran [iProto_step] on our behalf, collect it *)
    iIntros "[Hlc Himpl]".
    iMod (inv_acc with "Hslot") as "[IH Hcloses]"; [solve_ndisj|].
    iDestruct "IH" as (s') "[>Hoc Hrest]".
    iMod (lc_fupd_elim_later with "Hlc Hrest") as "Hrest".
    iDestruct (own_chan_agree with "Hoc Himpl") as %->. simpl.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv3.
    iMod (own_chan_halves_update (@chanstate.Idle V) with "Hoc Himpl") as "[H1 H2]";
      [ simpl in Hcv3 |- *; lia | ].
    iDestruct "Hrest" as "[(%p' & Hs1 & Hres) Hrfree]".
    iDestruct (saved_prop_agree with "Hs2 Hs1") as "#Heq".
    iMod (saved_prop_update_halves True%I with "Hs2 Hs1") as "[Hsa Hsb]".
    iMod ("Hcloses" with "[H1 Hsa Hsb Hrfree]") as "_".
    { iNext. iExists chanstate.Idle. iFrame "H1 Hrfree". iExists True%I. iFrame. }
    iCombine "Heq Hres" as "H".
    iMod (lc_fupd_elim_later with "H£3 H") as "[Heq' Hres]".
    iRewrite -"Heq'" in "Hres".
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* send_enq_au : these channels are unbuffered *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". mx_openc. mx_agree. iDestruct "Hrest" as "[]".
  - (* send_closed_au : these channels are never closed *)
    iIntros (drain) "[Hlc Himpl]". mx_openc. mx_agree. iDestruct "Hrest" as "[]".
Qed.

(** A plain blocking send. The protocol must offer a [Send] choice towards [j];
    if it is a mixed choice, discard the others first with [mixtris_own_le]. *)
Lemma wp_mixtris_send γ ch γch i j (v : V) m (p : iProto Σ V) :
  {{{ is_edge_chan γ ch γch i j ∗ i ↣[γ] (<(Send, j)> m) ∗ iMsg_car m v (Next p) }}}
    chan.send t #ch #v
  {{{ RET #(); i ↣[γ] p }}}.
Proof using W.
  iIntros (Φ) "(#Hedge & Hown & Hm) HΦ".
  iDestruct "Hedge" as (γs γr) "#[Hch Hslot]".
  iApply (chan.wp_send with "Hch").
  iIntros "H£".
  iApply (mixtris_send_au with "H£ [$Hch $Hslot] Hown Hm").
  iIntros "!> Hp". by iApply "HΦ".
Qed.

(** The same, in the telescope form protocols are usually written in. *)
Lemma wp_mixtris_send_tele {TT : tele} (tt : TT)
    γ ch γch i j (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ is_edge_chan γ ch γch i j ∗
      i ↣[γ] (<![j].. x> MSG (v x) {{ P x }}; p x) ∗ P tt }}}
    chan.send t #ch #(v tt)
  {{{ RET #(); i ↣[γ] p tt }}}.
Proof using W.
  iIntros (Φ) "(#Hedge & Hown & HP) HΦ".
  iDestruct (mixtris_own_le _ _ _ (<![j]> MSG (v tt); p tt)%proto
              with "Hown [HP]") as "Hown".
  { iIntros "!>". iApply iProto_le_trans;
      [iApply iProto_le_texist_intro_l|]. by iFrame "HP". }
  iApply (wp_mixtris_send with "[$Hedge $Hown] HΦ").
  by rewrite iMsg_base_eq.
Qed.

(** ** Receiving *)

(** The atomic-update form of the receive rule, for [RecvCase] clauses of
    [chan.wp_select_blocking]. *)
Lemma mixtris_recv_au γ ch γch i j m Φ :
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  is_edge_chan γ ch γch i j -∗
  j ↣[γ] (<(Recv, i)> m) -∗
  ▷ (∀ v p, iMsg_car m v (Next p) -∗ j ↣[γ] p -∗ Φ v true) -∗
  recv_au γch V Φ.
Proof.
  iIntros "(H£1 & H£2 & H£3 & H£4) #Hedge Hown HΦ".
  iDestruct "Hedge" as (γs γr) "[#Hch #Hslot]".
  iDestruct "Hown" as "[#Hctx Hp]".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : a sender is parked, so complete the exchange here *)
    iIntros (w) "[Hlc Himpl]". mx_openc. mx_step (@chanstate.RcvDone V) Hcv1.
    iDestruct "Hrest" as "[(%m1 & %p1 & Hs1 & Hpi & Hm1) Hrfree]".
    iMod (iProto_step with "Hctxi Hpi Hp Hm1") as "Hstep".
    iMod (lc_fupd_elim_later with "H£2 Hstep") as (p2) "(Hm2 & Hctxi & Hpi & Hpj)".
    iMod ("Hclosec" with "[$Hctxi]") as "_".
    iMod ("Hcloses" with "[H1 Hs1 Hpi Hrfree]") as "_".
    { iNext. iExists chanstate.RcvDone. iFrame "H1 Hrfree". iExists p1. iFrame. }
    iModIntro. iFrame "H2". iApply ("HΦ" with "Hm2"). by iFrame "#∗".
  - (* recv_slow_path_au : nobody is here yet, so park *)
    iIntros "[Hlc Himpl]". mx_openc. mx_step (@chanstate.RcvWait V) Hcv2.
    iDestruct "Hrest" as "[Hsfree [%Ψ0 [Hra Hrb]]]".
    iMod (saved_pred_update_halves (recv_result γ.(mx_proto) j m)
           with "Hra Hrb") as "[Hr1 Hr2]".
    iMod ("Hclosec" with "[$Hctxi]") as "_".
    iMod ("Hcloses" with "[H1 Hsfree Hr1 Hp]") as "_".
    { iNext. iExists chanstate.RcvWait. iFrame "H1 Hsfree". iExists m. iFrame. }
    iModIntro. iFrame "H2".
    (* phase two: the sender ran [iProto_step] on our behalf, collect it *)
    iIntros (w) "[Hlc Himpl]".
    iMod (inv_acc with "Hslot") as "[IH Hcloses]"; [solve_ndisj|].
    iDestruct "IH" as (s') "[>Hoc Hrest]".
    iMod (lc_fupd_elim_later with "Hlc Hrest") as "Hrest".
    iDestruct (own_chan_agree with "Hoc Himpl") as %->. simpl.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv3.
    iMod (own_chan_halves_update (@chanstate.Idle V) with "Hoc Himpl") as "[H1 H2]";
      [ simpl in Hcv3 |- *; lia | ].
    iDestruct "Hrest" as "[Hsfree (%m' & Hr1 & Hres)]".
    iDestruct (saved_pred_agree _ _ _ _ _ w with "Hr2 Hr1") as "#Heq".
    iMod (saved_pred_update_halves (λ _, True%I) with "Hr2 Hr1") as "[Hra Hrb]".
    iMod ("Hcloses" with "[H1 Hsfree Hra Hrb]") as "_".
    { iNext. iExists chanstate.Idle. iFrame "H1 Hsfree". iExists (λ _, True%I). iFrame. }
    iCombine "Heq Hres" as "H".
    iMod (lc_fupd_elim_later with "H£3 H") as "[Heq' Hres]".
    iRewrite -"Heq'" in "Hres".
    iDestruct "Hres" as (p2) "[Hm2 Hpj]".
    iModIntro. iFrame "H2". iApply ("HΦ" with "Hm2"). by iFrame "#∗".
  - (* recv_deq_au : these channels are unbuffered *)
    iIntros (w rest) "[Hlc Himpl]". mx_openc. mx_agree. iDestruct "Hrest" as "[]".
  - (* recv_drain_au : these channels are never closed *)
    iIntros (w rest) "[Hlc Himpl]". mx_openc. mx_agree. iDestruct "Hrest" as "[]".
  - (* recv_closed_au : these channels are never closed *)
    iIntros "[Hlc Himpl]". mx_openc. mx_agree. iDestruct "Hrest" as "[]".
Qed.

(** A plain blocking receive. *)
Lemma wp_mixtris_recv γ ch γch i j m Φ :
  is_edge_chan γ ch γch i j -∗
  j ↣[γ] (<(Recv, i)> m) -∗
  ▷ (∀ v p, iMsg_car m v (Next p) -∗ j ↣[γ] p -∗ Φ (#v, #true)%V) -∗
  WP chan.receive t #ch {{ Φ }}.
Proof using W.
  iIntros "#Hedge Hown HΦ".
  iDestruct "Hedge" as (γs γr) "#[Hch Hslot]".
  iApply (chan.wp_receive with "Hch").
  iIntros "H£".
  by iApply (mixtris_recv_au with "H£ [$Hch $Hslot] Hown HΦ").
Qed.

(** The same, in telescope form. *)
Lemma wp_mixtris_recv_tele {TT : tele}
    γ ch γch i j (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ is_edge_chan γ ch γch i j ∗
      j ↣[γ] (<?[i].. x> MSG (v x) {{ P x }}; p x) }}}
    chan.receive t #ch
  {{{ x, RET (#(v x), #true); j ↣[γ] p x ∗ P x }}}.
Proof using W.
  iIntros (Φ) "[#Hedge Hown] HΦ".
  iApply (wp_mixtris_recv with "Hedge Hown").
  iIntros "!>" (w q) "Hm Hown".
  rewrite iMsg_texist_exist.
  iDestruct "Hm" as (x) "Hm". rewrite iMsg_base_eq /=.
  iDestruct "Hm" as "(%Hv & #Heq & HP)". subst.
  rewrite later_equivI_1.
  iApply "HΦ". iFrame "HP".
  iApply (mixtris_own_le with "Hown").
  iNext. iRewrite -"Heq". iApply iProto_le_refl.
Qed.

End mixtris.

Notation "i ↣[ γ ] p" := (mixtris_own γ i p%proto) (at level 20, format "i  ↣[  γ  ]  p").
