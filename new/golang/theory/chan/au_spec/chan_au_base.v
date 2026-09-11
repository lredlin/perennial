From New.golang.theory.chan.au_spec Require Import chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.mit_pdos.perennial.goose.model.channel.
From New.generatedproof.github_com.mit_pdos.perennial.goose Require Import model.channel.

(** The specification state for a channel. *)
Module chanstate.
Inductive t (V : Type) : Type :=
| Buffered (buff : list V)     (* Buffered channel with pending messages *)
| Idle                        (* Empty unbuffered channel, ready for operations *)
| SndWait (v : V)          (* Unbuffered channel with sender waiting *)
| RcvWait                 (* Unbuffered channel with receiver waiting *)
| SndDone (v : V)           (* Sender committed, waiting for receiver to complete *)
| RcvDone                  (* Receiver committed, waiting for sender to complete *)
| Closed (drain : list V)  (* Closed channel, possibly drain remaining messages *)
.
#[global] Instance witness V : Inhabited (t V) := populate!.

Global Arguments Buffered {V}.
Global Arguments Idle {V}.
Global Arguments SndWait {V}.
Global Arguments RcvWait {V}.
Global Arguments SndDone {V}.
Global Arguments RcvDone {V}.
Global Arguments Closed {V}.

End chanstate.

(** The state machine representation matching the model implementation.
    This is slightly different from the mathematical representation
    in that we don't go to the SndWait state logically until an offer
    is about to be accepted. *)
Module chanphys.
Inductive t (V : Type) : Type :=
| Buffered (buffer : list V)     (* Channel with buffered messages *)
| Idle                        (* Ready for operations *)
| SndWait (v : V)            (* Sender offers *)
| RcvWait                    (* Receiver offers *)
| SndDone (v : V)            (* Sender operation completed, handshake in progress *)
| RcvDone            (* Receiver operation completed, handshake in progress *)
| Closed (buffer : list V)  (* Closed channel *)
.

Global Arguments Idle {V}.
Global Arguments SndWait {V}.
Global Arguments RcvWait {V}.
Global Arguments SndDone {V}.
Global Arguments RcvDone {V}.
Global Arguments Closed {V}.
Global Arguments Buffered {V}.

End chanphys.

(** The offer protocol coordinates handshakes between senders and receivers
    in unbuffered channels. An "offer" represents a pending operation that
    can be accepted by the other party. This ghost state ensures that
    an outstanding offer can only be accepted or left as-is for when we lock
    the channel to check the status. *)
Inductive offer_lock (V : Type) : Type :=
| Snd (v : V)                (* Sender has made an offer *)
| Rcv                        (* Receiver has made an offer *)
.

Global Arguments Snd {V}.
Global Arguments Rcv {V}.

(** Ghost names for tracking various aspects of channel state in the logic *)
Record chan_names := {
  state_name : gname;                    (* Main channel state *)
  offer_lock_name : gname;               (* Offer protocol lock *)
  offer_parked_prop_name : gname;        (* The saved prop that we can leave with the channel to support select *)
  offer_parked_pred_name : gname;        (* The saved continuation for receive, which is a predicate on v, ok *)
  offer_continuation_name : gname;       (* The continuation for send *)
  chan_cap : w64;                        (* The channel capacity *)
}.

Section au_defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Context (ch : loc) (γ : chan_names) (V : Type) (v : V).
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

Definition chanstate (q : Qp) (s : chanstate.t V) : iProp Σ :=
  ghost_var γ.(state_name) q s.

Definition chan_cap_valid (s : chanstate.t V) (cap : Z) : Prop :=
  match s with
  | chanstate.Buffered buf =>
      (* chanphys.Buffered is only used for buffered channels, and buffer size is bounded
      by capacity *)
      (length buf ≤ cap)%Z ∧ (0 < cap)
  | chanstate.Closed [] => (0 ≤ cap)
  | chanstate.Closed drain =>
      (* Draining closed channels are buffered channels, and draining elements
      are bounded by capacity *)
      (Z.of_nat (length drain) ≤ cap) ∧ (0 < cap)
  | _ => cap = 0                            (* All other states are unbuffered *)
  end.

(** Represents ownership of a channel with its logical state *)
Definition own_chan (s: chanstate.t V) : iProp Σ :=
  "Hchanrepfrag" ∷ chanstate (1/2) s ∗
  "%Hcapvalid" ∷ ⌜ chan_cap_valid s (sint.Z $ chan_cap γ) ⌝.

(** ** Per-transition ("conjunctive") atomic updates.

    These are the AUs the program specs are proved against.  Each names a
    concrete pre-state with no [⌜s = _⌝] guard, because it *receives* the mutex
    invariant's half of [own_chan] and hands back a half at the post-state,
    rather than the client handing its own half out.  The implementation always
    knows the state before it fires an AU (it holds the lock, and the mutex
    invariant holds the other half), so it selects the matching conjunct.

    A client discharges every conjunct in every state: agreement between the two
    halves either says the pre-state matches or yields a contradiction -- so the
    arms are exactly the reachable transitions, rather than one case per
    physical state. *)

Definition send_fast_path_au (Φ : iProp Σ) : iProp Σ :=
  £1 ∗ own_chan chanstate.RcvWait ={⊤}=∗ own_chan (chanstate.SndDone v) ∗ Φ.

(** A two-phase AU.  Phase one posts the offer; the receiver that accepts it
    hands phase two back to the sender, which fires it on relocking once the
    receiver has committed.  Neither phase has a "closed" case: [tryClose] only
    closes from Idle/Buffered and spins on SndWait, so a parked send offer
    cannot be closed underneath. *)
Definition send_slow_path_au (Φ : iProp Σ) : iProp Σ :=
  £1 ∗ own_chan chanstate.Idle ={⊤}=∗
    (* phase one: Idle -> SndWait v *)
    own_chan (chanstate.SndWait v) ∗
    (* phase two: RcvDone -> Idle, once the receiver has committed *)
    (£1 ∗ own_chan chanstate.RcvDone ={⊤}=∗ own_chan chanstate.Idle ∗ Φ).

(** The capacity fact is supplied by the implementation, which has just checked
    there is room; [own_chan (Buffered buf)] only bounds [buf] by the capacity. *)
Definition send_enq_au (Φ : iProp Σ) : iProp Σ :=
  ∀ buf, £1 ∗ ⌜ (length buf < sint.Z $ chan_cap γ)%Z ⌝ ∗
         own_chan (chanstate.Buffered buf) ={⊤}=∗
         own_chan (chanstate.Buffered (buf ++ [v])) ∗ Φ.

Definition send_closed_au : iProp Σ :=
  ∀ drain, £1 ∗ own_chan (chanstate.Closed drain) ={⊤}=∗ False.

Definition send_au (Φ : iProp Σ) : iProp Σ :=
  send_fast_path_au Φ ∧ send_slow_path_au Φ ∧ send_enq_au Φ ∧ send_closed_au.

Definition recv_fast_path_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  ∀ w, £1 ∗ own_chan (chanstate.SndWait w) ={⊤}=∗
       own_chan chanstate.RcvDone ∗ Φ w true.

(** The two-phase AU for receive, mirroring [send_slow_path_au]. *)
Definition recv_slow_path_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  £1 ∗ own_chan chanstate.Idle ={⊤}=∗
    (* phase one: Idle -> RcvWait *)
    own_chan chanstate.RcvWait ∗
    (* phase two: SndDone w -> Idle, once the sender has committed *)
    (∀ w, £1 ∗ own_chan (chanstate.SndDone w) ={⊤}=∗
          own_chan chanstate.Idle ∗ Φ w true).

Definition recv_deq_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  ∀ w rest, £1 ∗ own_chan (chanstate.Buffered (w :: rest)) ={⊤}=∗
            own_chan (chanstate.Buffered rest) ∗ Φ w true.

Definition recv_drain_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  ∀ w rest, £1 ∗ own_chan (chanstate.Closed (w :: rest)) ={⊤}=∗
            own_chan (chanstate.Closed rest) ∗ Φ w true.

Definition recv_closed_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  £1 ∗ own_chan (chanstate.Closed []) ={⊤}=∗
       own_chan (chanstate.Closed []) ∗ Φ (zero_val V) false.

Definition recv_au (Φ : V → bool → iProp Σ) : iProp Σ :=
  recv_fast_path_au Φ ∧ recv_slow_path_au Φ ∧ recv_deq_au Φ ∧ recv_drain_au Φ ∧ recv_closed_au Φ.

Definition close_idle_au (Φ : iProp Σ) : iProp Σ :=
  £1 ∗ own_chan chanstate.Idle ={⊤}=∗ own_chan (chanstate.Closed []) ∗ Φ.

Definition close_buf_au (Φ : iProp Σ) : iProp Σ :=
  ∀ buf, £1 ∗ own_chan (chanstate.Buffered buf) ={⊤}=∗
         own_chan (chanstate.Closed buf) ∗ Φ.

Definition close_closed_au : iProp Σ :=
  ∀ drain, £1 ∗ own_chan (chanstate.Closed drain) ={⊤}=∗ False.

Definition close_au (Φ : iProp Σ) : iProp Σ :=
  close_idle_au Φ ∧ close_buf_au Φ ∧ close_closed_au.

(** ** Nonblocking variants.

    A nonblocking operation posts no offer, so it is the same choice of
    transitions minus the slow path.  The two forms differ in exactly one
    conjunct: the plain one is handed [Φnotready] unconditionally, so the client
    must be prepared for the case to be skipped no matter what; the [Alt] one
    gets it only from a state that really is not ready, which is what lets a
    client prove a select's default branch unreachable.

    Splitting the transitions apart is what makes these two comparable at all.
    While the not-ready case was a branch of the same [match], it shared the one
    [∃ s, own_chan s] opening with every other case, and neither form implied
    the other; both had to be shipped.  Given its own conjunct it opens nothing,
    and [nonblocking_send_au -∗ nonblocking_send_au_alt] goes through
    ([nonblocking_send_au_to_alt] below), so only the weaker [Alt] form is
    primitive and the plain one is a corollary.

    [send_not_ready] / [recv_not_ready] are the states with no enabled
    transition -- note a closed channel is *not* among them, since sending on
    one panics rather than blocking. *)

Definition send_not_ready (s : chanstate.t V) : Prop :=
  match s with
  | chanstate.RcvWait => False
  | chanstate.Closed _ => False
  | chanstate.Buffered buf => ¬ (length buf < sint.Z $ chan_cap γ)%Z
  | _ => True
  end.

Definition recv_not_ready (s : chanstate.t V) : Prop :=
  match s with
  | chanstate.SndWait _ => False
  | chanstate.Closed _ => False
  | chanstate.Buffered [] => True
  | chanstate.Buffered (_ :: _) => False
  | _ => True
  end.

(** The stutter transition: the state is not ready, so nothing moves and the
    caller learns it. *)
Definition send_not_ready_au (Φnotready : iProp Σ) : iProp Σ :=
  ∀ s, £1 ∗ ⌜ send_not_ready s ⌝ ∗ own_chan s ={⊤}=∗ own_chan s ∗ Φnotready.

Definition recv_not_ready_au (Φnotready : iProp Σ) : iProp Σ :=
  ∀ s, £1 ∗ ⌜ recv_not_ready s ⌝ ∗ own_chan s ={⊤}=∗ own_chan s ∗ Φnotready.

Definition nonblocking_send_au (Φ Φnotready : iProp Σ) : iProp Σ :=
  send_fast_path_au Φ ∧ send_enq_au Φ ∧ send_closed_au ∧ Φnotready.

Definition nonblocking_send_au_alt (Φ Φnotready : iProp Σ) : iProp Σ :=
  send_fast_path_au Φ ∧ send_enq_au Φ ∧ send_closed_au ∧ send_not_ready_au Φnotready.

Definition nonblocking_recv_au (Φ : V → bool → iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
  recv_fast_path_au Φ ∧ recv_deq_au Φ ∧ recv_drain_au Φ ∧ recv_closed_au Φ ∧ Φnotready.

Definition nonblocking_recv_au_alt (Φ : V → bool → iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
  recv_fast_path_au Φ ∧ recv_deq_au Φ ∧ recv_drain_au Φ ∧ recv_closed_au Φ ∧ recv_not_ready_au Φnotready.

End au_defns.

Global Arguments own_chan {_ _ _ _ _} (γ V) (s).
Global Arguments chan_cap_valid {_} (s cap).

Section defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Context (ch : loc) (γ : chan_names) (V : Type).
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

(** Maps physical channel states to their heap representations.
    Each state corresponds to specific field values in the Go struct. *)
Definition chan_phys (s: chanphys.t V) : iProp Σ :=
  match s with
    | chanphys.Closed [] =>
        (∃ (slice_val: slice.t),
            "state" ∷ (ch.[channel.Channel.t V , "state"] ↦ (W64 6)) ∗
            "slice" ∷ slice_val ↦* ([] : list V) ∗
            "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
            "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val)
    | chanphys.Closed drain =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 6) ∗
        "slice" ∷ slice_val ↦* drain ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.Buffered buff =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 0) ∗
        "slice" ∷ slice_val ↦* buff ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.Idle =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 1) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.SndWait v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 2) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.RcvWait =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 3) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.SndDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 4) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    | chanphys.RcvDone =>
        ∃ (v : V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel.t V, "state"] ↦ (W64 5) ∗
        "v" ∷ ch.[channel.Channel.t V, "v"] ↦ v ∗
        "slice" ∷ slice_val ↦* ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel.t V, "buffer"] ↦ slice_val
    end.

(** Bundles together offer-related ghost state for atomic operations *)
Definition saved_offer (q : Qp)
  (lock_val : option (offer_lock V))
  (parked_prop continuation_prop : iProp Σ) : iProp Σ :=
  ghost_var γ.(offer_lock_name) q lock_val ∗
  saved_prop_own γ.(offer_parked_prop_name) (DfracOwn q) parked_prop ∗
  saved_prop_own γ.(offer_continuation_name) (DfracOwn q) continuation_prop.

(** Maps physical states to their logical representations with ghost state.
    This is the key invariant that connects the physical implementation
    to the logical specifications. *)
Definition chan_logical (s : chanphys.t V): iProp Σ :=
  match s with
  | chanphys.Idle =>
       ∃ (Φr: V → bool → iProp Σ),
           "Hoffer" ∷ saved_offer 1 None True True ∗
           "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
            own_chan γ V chanstate.Idle

  | chanphys.SndWait v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
          "Hoffer" ∷ saved_offer (1/2) (Some (Snd v)) P Φ ∗
          "HP" ∷ P ∗
          "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
          "Hau" ∷ (P -∗ send_slow_path_au γ V v Φ) ∗
           own_chan γ V chanstate.Idle

  | chanphys.RcvWait =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ saved_offer (1/2) (Some Rcv) P True ∗
         "HP" ∷ P ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (uncurry Φr) ∗
         "Hau" ∷ (P -∗ recv_slow_path_au γ V Φr) ∗
         own_chan γ V chanstate.Idle

  | chanphys.SndDone v =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
       "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (uncurry Φr) ∗
       "Hoffer" ∷ saved_offer (1/2) (Some Rcv) P True ∗
       "Hau" ∷ (∀ w, £1 ∗ own_chan γ V (chanstate.SndDone w) ={⊤}=∗
                     own_chan γ V chanstate.Idle ∗ Φr w true) ∗
       own_chan γ V (chanstate.SndDone v)

  | chanphys.RcvDone =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ) (v:V),
         "Hoffer" ∷ saved_offer (1/2) (Some (Snd v)) P Φ ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (uncurry Φr) ∗
         "Hau" ∷ (£1 ∗ own_chan γ V chanstate.RcvDone ={⊤}=∗
                  own_chan γ V chanstate.Idle ∗ Φ) ∗
       own_chan γ V chanstate.RcvDone

  | chanphys.Closed [] =>
          own_chan γ V (chanstate.Closed []) ∗
           "Hoffer" ∷ (⌜ chan_cap γ = W64 0 ⌝ -∗ saved_offer 1 None True True)

  | chanphys.Closed drain =>
          own_chan γ V (chanstate.Closed drain)

  | chanphys.Buffered buff =>
          own_chan γ V (chanstate.Buffered buff)
  end.

(** The main invariant protected by the channel's mutex.
    This connects the physical heap state with the logical state. *)
Definition chan_inv_inner : iProp Σ :=
  ∃ (s : chanphys.t V),
    "phys" ∷ chan_phys s ∗
    "offer" ∷ chan_logical s
.

(** The public predicate that clients use to interact with channels.
    This is persistent and provides access to the channel's capabilities. *)
Definition is_chan : iProp Σ :=
  ∃ (mu_loc: loc),
    "#cap" ∷ ch.[channel.Channel.t V, "cap"] ↦□ (chan_cap γ) ∗
    "#mu" ∷ ch.[channel.Channel.t V, "mu"] ↦□ mu_loc ∗
    "#lock" ∷ is_lock mu_loc chan_inv_inner ∗
    "%Hnotnull" ∷ ⌜ ch ≠ chan.nil ⌝ ∗
    "%Hcap" ∷ ⌜ 0 ≤ sint.Z γ.(chan_cap) ⌝.
#[global] Typeclasses Opaque is_chan.
#[global] Opaque is_chan.
#[local] Transparent is_chan.
#[local] Typeclasses Transparent is_chan.

(** A nonblocking operation posts no offer, so it needs exactly the blocking
    conjuncts minus the slow path.  Both directions are pure ∧-projections, and
    [Φnotready] is [True] because the plain nonblocking form is always free to
    skip the case. *)
Lemma blocking_rcv_implies_nonblocking (Φ : V → bool → iProp Σ) :
  recv_au γ V Φ -∗
  nonblocking_recv_au γ V Φ True.
Proof.
  iIntros "H". rewrite /recv_au /nonblocking_recv_au.
  iSplit; [| iSplit; [| iSplit; [| iSplit ] ] ].
  - iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". iRight in "H". iFrame.
  - done.
Qed.

Lemma blocking_send_implies_nonblocking (Φ : iProp Σ) (v : V) :
  send_au γ V v Φ -∗
  nonblocking_send_au γ V v Φ True.
Proof.
  iIntros "H". rewrite /send_au /nonblocking_send_au.
  iSplit; [| iSplit; [| iSplit ] ].
  - iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". iFrame.
  - done.
Qed.

Lemma offer_idle_to_send parked_prop cont v :
  saved_offer 1 None True True ==∗
  saved_offer (1/2) (Some (Snd v)) parked_prop cont ∗
  saved_offer (1/2) (Some (Snd v)) parked_prop cont.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Snd v)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_halves_to_idle x y parked_prop cont :
  saved_offer (1/2) (Some x) parked_prop cont -∗
  saved_offer (1/2) (Some y) parked_prop cont ==∗
  saved_offer 1 None True True.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iIntros "[Hlock2 [Hoffer2 Hcont2]]".
  iCombine "Hlock Hlock2" gives %Heq.
  assert (x = y) by (destruct_and!; congruence); subst.
  iCombine "Hlock Hlock2" as "Hlock".
  iMod (saved_prop_update_halves True with "Hoffer Hoffer2") as "[Hoffer Hoffer2]".
  iMod (saved_prop_update_halves True with "Hcont Hcont2") as "[Hcont Hcont2]".
  iCombine "Hcont Hcont2" as "Hcont".
  iCombine "Hoffer Hoffer2" as "Hoffer".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iModIntro. iFrame.
Qed.

Lemma offer_idle_to_recv parked_prop cont:
  saved_offer 1 None True True ==∗
  saved_offer (1/2) (Some Rcv) parked_prop cont ∗
  saved_offer (1/2) (Some Rcv) parked_prop cont.
Proof.
   iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Rcv)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_reset parked_prop cont state :
  saved_offer 1 state parked_prop cont ==∗
  saved_offer 1 None True True.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iMod (saved_prop_update True with "Hcont") as "Hcont".
  iMod (saved_prop_update True with "Hoffer") as "Hoffer".
  iModIntro.
  iFrame.
Qed.

Lemma saved_offer_agree q1 q2
  lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer q1 lock1 parked1 cont1 ∗
  saved_offer q2 lock2 parked2 cont2 ⊢
  ⌜lock1 = lock2⌝ ∗
  ▷(parked1 ≡ parked2) ∗ ▷(cont1 ≡ cont2).
Proof.
  iIntros "[[Hl1 [Hp1 Hc1]] [Hl2 [Hp2 Hc2]]]".
  iDestruct (ghost_var_agree with "Hl1 Hl2") as %->.
  iDestruct (saved_prop_agree with "Hp1 Hp2") as "Hp_eq".
  iDestruct (saved_prop_agree with "Hc1 Hc2") as "Hc_eq".
  auto.
Qed.

Lemma saved_offer_lc_agree
  lock1 parked1 cont1 lock2 parked2 cont2 :
  £ 1 -∗
  saved_offer (1/2) lock1 parked1 cont1 -∗
  saved_offer (1/2) lock2 parked2 cont2 -∗
  |={⊤}=> ⌜lock1 = lock2⌝ ∗
         (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
         saved_offer 1 None True True.
Proof.
  iIntros "Hlc1".
  iIntros "[Hl1 [Hp1 Hc1]]".
  iIntros "[Hl2 [Hp2 Hc2]]".
  iDestruct (ghost_var_agree with "[$Hl1] [$Hl2]") as %->.
  iDestruct (saved_prop_agree with "[$Hp1] [$Hp2]") as "#Hp_eq".
  iDestruct (saved_prop_agree with "[$Hc1] [$Hc2]") as "#Hc_eq".

  iCombine "Hp_eq Hc_eq" as "Heq".
  iClear "Hp_eq Hc_eq".
  iMod (lc_fupd_elim_later with "Hlc1 Heq") as "[Hp_eq Hc_eq]".
  iFrame.
  iSplitR; first done.  (* ⌜lock2 = lock2⌝ is trivial *)

  (* Combine and update ghost variable *)
  iCombine "Hl1 Hl2" as "Hlock".
  iMod ((ghost_var_update None) with "Hlock") as "Hlock".

  (* Update saved propositions using halves lemmas *)
  iMod (saved_prop_update_halves True with "Hp1 Hp2") as "[Hp1 Hp2]".
  iMod (saved_prop_update_halves True with "Hc1 Hc2") as "[Hc1 Hc2]".

  (* Combine the updated halves to get full ownership *)
  iCombine "Hp1 Hp2" as "Hparked".
  iCombine "Hc1 Hc2" as "Hcont".

  iFrame.
  auto.
Qed.

Lemma saved_offer_fractional_invalid q1 q2 lock1 parked1 cont1 lock2 parked2 cont2 :
  (1 < q1 + q2)%Qp →
  saved_offer q1 lock1 parked1 cont1 -∗
  saved_offer q2 lock2 parked2 cont2 -∗
  False.
Proof.
  iIntros (Hq) "[Hlock1 [Hp1 Hc1]] [Hlock2 [Hp2 Hc2]]".
  iDestruct (ghost_var_valid_2 with "Hlock1 Hlock2") as "[%Hvalid _]".
  iPureIntro.
apply Qp.lt_nge in Hq.
contradiction.
Qed.

Lemma saved_offer_half_full_invalid lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer (1/2) lock1 parked1 cont1 -∗
  saved_offer 1 lock2 parked2 cont2 -∗
  False.
Proof.
  iApply saved_offer_fractional_invalid.
  compute_done. (* 1/2 + 1 = 3/2 > 1 *)
Qed.

Lemma chanstate_update s s' :
  chanstate γ V 1 s ==∗ chanstate γ V 1 s'.
Proof.
  iApply ghost_var_update.
Qed.

Lemma chanstate_agree q1 q2 s s' :
  chanstate γ V q1 s -∗ chanstate γ V q2 s' -∗ ⌜s = s'⌝.
Proof.
  iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2").
Qed.

(* NOTE: unused *)
#[local] Lemma chanstate_combine s s' :
  chanstate γ V (1/2) s -∗ chanstate γ V (1/2) s' -∗ chanstate γ V 1 s.
Proof.
  iIntros "H1 H2". iDestruct (chanstate_agree with "H1 H2") as %->.
  iCombine "H1 H2" as "H". done.
Qed.

Lemma chanstate_halves_update s1 s2 s' :
  chanstate γ V (1/2) s1 -∗ chanstate γ V (1/2) s2 ==∗
  chanstate γ V (1/2) s' ∗ chanstate γ V (1/2) s'.
Proof.
  rewrite /chanstate.
  apply ghost_var_update_halves.
Qed.

(** The plain nonblocking AU implies the [Alt] one: [Alt] is the weaker
    precondition, so it is the one the program specs should take.  This is
    provable only because the not-ready case is its own conjunct -- ∧-introduction
    proves each conjunct separately from the same resources, so we never need the
    transition arms and [Φnotready] simultaneously.  In the pattern-matching form
    they live in one [match] under one fupd, and a single proof would need both
    at once, which [∧] cannot give. *)
Lemma nonblocking_send_au_to_alt v Φ Φnotready :
  nonblocking_send_au γ V v Φ Φnotready -∗ nonblocking_send_au_alt γ V v Φ Φnotready.
Proof using All.
  iIntros "H". rewrite /nonblocking_send_au /nonblocking_send_au_alt. repeat iSplit.
  - iLeft in "H". iFrame.
  - iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". rewrite /send_not_ready_au.
    iIntros (s) "(Hlc & %Hnr & Hoc)". iModIntro. iFrame.
Qed.

Lemma nonblocking_recv_au_to_alt (Φ : V → bool → iProp Σ) Φnotready :
  nonblocking_recv_au γ V Φ Φnotready -∗ nonblocking_recv_au_alt γ V Φ Φnotready.
Proof using All.
  iIntros "H". rewrite /nonblocking_recv_au /nonblocking_recv_au_alt. repeat iSplit.
  - iLeft in "H". iFrame.
  - iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". iLeft in "H". iFrame.
  - iRight in "H". iRight in "H". iRight in "H". iRight in "H".
    rewrite /recv_not_ready_au.
    iIntros (s) "(Hlc & %Hnr & Hoc)". iModIntro. iFrame.
Qed.

Lemma own_chan_cap_valid s :
  own_chan γ V s -∗ ⌜ chan_cap_valid s (sint.Z $ chan_cap γ) ⌝.
Proof. rewrite /own_chan. iNamed 1. done. Qed.

(* FIXME: iCombine instances. *)
Lemma own_chan_agree s s' :
   own_chan γ V s -∗ own_chan γ V s' -∗ ⌜s = s'⌝.
Proof.
  iIntros "H1 H2". iNamedSuffix "H1" "1". iNamedSuffix "H2" "2".
  iDestruct (ghost_var_agree with "[$Hchanrepfrag1] [$Hchanrepfrag2]") as "%Hag".
  unfold chan_cap_valid in *.
  by iApply (ghost_var_agree with "Hchanrepfrag1 Hchanrepfrag2").
Qed.

(* Needs [chan_cap_valid s'' cap] as precondition? *)
Lemma own_chan_halves_update s'' s s' :
  chan_cap_valid s'' (sint.Z $ chan_cap γ) →
  own_chan γ V s -∗ own_chan γ V s' ==∗
  own_chan γ V s'' ∗ own_chan γ V s''.
Proof.
  intros Hvalid.
  iIntros "(Hv1 & %) (Hv2 & %)". rewrite /named.
  iMod (chanstate_halves_update with "Hv1 Hv2") as "[$ $]".
  iFrame "#∗".
  iPureIntro.
  auto.
Qed.

Lemma own_chan_buffer_size buf :
  own_chan γ V (chanstate.Buffered buf) -∗
  ⌜Z.of_nat (length buf) ≤ sint.Z $ chan_cap γ⌝.
Proof.
  iNamed 1.
  simpl in Hcapvalid.
  iPureIntro. lia.
Qed.

Lemma own_chan_drain_size drain :
  own_chan γ V (chanstate.Closed drain) -∗
  ⌜Z.of_nat (length drain) ≤ sint.Z $ chan_cap γ⌝.
Proof.
  iNamed 1.
  simpl in Hcapvalid.
  destruct drain.
  { simpl. iPureIntro; lia. }
  iPureIntro. lia.
Qed.

Global Instance is_chan_pers : Persistent is_chan.
Proof. apply _. Qed.

Global Instance own_chan_timeless s : Timeless (own_chan γ V s).
Proof. apply _. Qed.

Lemma is_chan_not_null :
  is_chan -∗ ⌜ch ≠ null⌝.
Proof. iNamed 1. done. Qed.

End defns.

#[global] Opaque is_chan own_chan.

Global Arguments own_chan_halves_update {_ _ _ _ _ _ _} (_).
