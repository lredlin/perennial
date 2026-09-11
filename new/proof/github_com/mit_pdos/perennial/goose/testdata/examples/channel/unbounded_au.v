Require Import New.proof.proof_prelude.
From New.ghost Require Export own dghost_var.
From New.golang.theory Require Import chan.

(** * Atomic updates for [Unbounded] (gRPC-Go's unbounded buffer).

    [unbounded.go] wraps a capacity-1 channel with a mutex-guarded backlog so
    that a producer never blocks.  Its clients reason about an abstract queue
    and never about the channel inside.

    The abstract state deliberately mirrors [chanstate.t]: an unbounded buffer
    is morally a channel whose capacity is unbounded, so it has exactly the two
    states a buffered channel can be in -- [Buffered buff] and [Closed drain] --
    and none of the five rendezvous states, which only arise at capacity 0.
    Constructor and field names are the channel's.

    The per-transition ("conjunctive") atomic updates below are named after the
    channel arm each one corresponds to, and carry a later credit in the same
    shape as [chan_au_base]'s [send_au]/[recv_au]/[close_au]:

      ub_send_enq_au      <->  send_enq_au       (append to the buffer)
      ub_send_closed_au   <->  send_closed_au    (but a no-op, not [False])
      ub_recv_deq_au      <->  recv_deq_au       (take the head)
      ub_recv_drain_au    <->  recv_drain_au     (take the head while closed)
      ub_recv_closed_au   <->  recv_closed_au    (closed and drained)
      ub_close_buf_au     <->  close_buf_au      (the buffer becomes the drain)
      ub_close_closed_au  <->  close_closed_au   (but a no-op, not [False])

    Two deliberate divergences from the raw channel spec, both places where the
    wrapper's semantics differ:

    - [Put] never blocks and never panics.  On a closed buffer it is a silent
      no-op, matching [Unbounded.Put] returning [errBufferClosed] -- where
      [send_closed_au] is [False], since a send on a closed channel panics.

    - [Close] is idempotent.  [Unbounded.Close] tests [b.closing] and returns
      early on a repeat call -- where [close_closed_au] is [False], since a
      second [close] panics.

    There is no [send_fast_path]/[send_slow_path] or [recv_fast_path]/
    [recv_slow_path] arm, because there is no rendezvous to have.  There is also
    no arm for [Buffered []] on the receive side: an empty open buffer admits no
    transition, exactly as [recv_au] has no arm for [chanstate.Idle].  The
    caller retries once a [Put] or a [Close] has run. *)

Module ubstate.
Inductive t (V : Type) : Type :=
| Buffered (buff : list V) (* buffer accepts Puts; [buff] is the pending FIFO *)
| Closed (drain : list V)  (* Close has been called; [drain] is what is left *)
.
Global Arguments Buffered {V}.
Global Arguments Closed {V}.
#[global] Instance witness V : Inhabited (t V) := populate (Buffered []).
End ubstate.

Section unbounded_au.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !allG Σ}.
Context {sem : go.Semantics}.
Context (γ : gname) (V : Type) `{!ZeroVal V}.

Definition own_ub (q : Qp) (s : ubstate.t V) : iProp Σ :=
  dghost_var γ (DfracOwn q) s.

(** These AUs are parameterized by a mask [E] rather than fixed at [⊤].
    [own_ub]'s other half lives in a bare invariant ([unbounded]'s [Inv_ub])
    with its own namespace, and the implementation fires the client's update
    from *inside* that invariant's opening -- so the update must be fireable at
    whatever mask is left over, [⊤∖↑N], not at the full [⊤].

    This is unlike [chan_au_base]'s updates, which do run at [⊤]: [is_chan]
    holds an [is_lock], not an [inv], so a channel occupies no namespace.  The
    buffer genuinely needs an invariant here, because a thread receiving off
    [Get()] does not hold the buffer's mutex and cannot acquire it from inside
    a view shift. *)

(** ** Put *)

Definition ub_send_enq_au (E : coPset) (v : V) (Φ : iProp Σ) : iProp Σ :=
  ∀ buff, £1 ∗ own_ub (1/2) (ubstate.Buffered buff) ={E}=∗
          own_ub (1/2) (ubstate.Buffered (buff ++ [v])) ∗ Φ.

Definition ub_send_closed_au (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  ∀ drain, £1 ∗ own_ub (1/2) (ubstate.Closed drain) ={E}=∗
           own_ub (1/2) (ubstate.Closed drain) ∗ Φ.

Definition ub_send_au (E : coPset) (v : V) (Φ : iProp Σ) : iProp Σ :=
  ub_send_enq_au E v Φ ∧ ub_send_closed_au E Φ.

(** ** Receiving off [Get()]

    The effect of a receive on the channel [Get] returns, after the
    implementation's internal [Load] bookkeeping.  It takes the head whether or
    not the buffer is closed, since closing only stops new [Put]s -- [Close]'s
    doc comment promises previously buffered data is still drained. *)

Definition ub_recv_deq_au (E : coPset) (Φ : V → bool → iProp Σ) : iProp Σ :=
  ∀ w rest, £1 ∗ own_ub (1/2) (ubstate.Buffered (w :: rest)) ={E}=∗
            own_ub (1/2) (ubstate.Buffered rest) ∗ Φ w true.

Definition ub_recv_drain_au (E : coPset) (Φ : V → bool → iProp Σ) : iProp Σ :=
  ∀ w rest, £1 ∗ own_ub (1/2) (ubstate.Closed (w :: rest)) ={E}=∗
            own_ub (1/2) (ubstate.Closed rest) ∗ Φ w true.

Definition ub_recv_closed_au (E : coPset) (Φ : V → bool → iProp Σ) : iProp Σ :=
  £1 ∗ own_ub (1/2) (ubstate.Closed []) ={E}=∗
  own_ub (1/2) (ubstate.Closed []) ∗ Φ (zero_val V) false.

Definition ub_recv_au (E : coPset) (Φ : V → bool → iProp Σ) : iProp Σ :=
  ub_recv_deq_au E Φ ∧ ub_recv_drain_au E Φ ∧ ub_recv_closed_au E Φ.

(** ** Close *)

Definition ub_close_buf_au (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  ∀ buff, £1 ∗ own_ub (1/2) (ubstate.Buffered buff) ={E}=∗
          own_ub (1/2) (ubstate.Closed buff) ∗ Φ.

Definition ub_close_closed_au (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  ∀ drain, £1 ∗ own_ub (1/2) (ubstate.Closed drain) ={E}=∗
           own_ub (1/2) (ubstate.Closed drain) ∗ Φ.

Definition ub_close_au (E : coPset) (Φ : iProp Σ) : iProp Σ :=
  ub_close_buf_au E Φ ∧ ub_close_closed_au E Φ.

(** ** Ghost state laws, named after [chan_au_base]'s. *)

Lemma own_ub_agree q1 q2 s1 s2 :
  own_ub q1 s1 -∗ own_ub q2 s2 -∗ ⌜s1 = s2⌝.
Proof. iApply dghost_var_agree. Qed.

Lemma own_ub_halves_update s' s1 s2 :
  own_ub (1/2) s1 -∗ own_ub (1/2) s2 ==∗ own_ub (1/2) s' ∗ own_ub (1/2) s'.
Proof. iApply dghost_var_update_halves. Qed.

Global Instance own_ub_timeless q s : Timeless (own_ub q s).
Proof. apply _. Qed.

End unbounded_au.

Lemma ub_alloc `{hG: heapGS Σ, !ffi_semantics _ _, !allG Σ} {sem : go.Semantics}
    (V : Type) :
  ⊢ |==> ∃ γ, own_ub γ V (1/2) (ubstate.Buffered []) ∗
              own_ub γ V (1/2) (ubstate.Buffered []).
Proof.
  iMod (dghost_var_alloc (ubstate.Buffered [] : ubstate.t V)) as (γ) "Hub".
  iDestruct "Hub" as "[Hub1 Hub2]".
  iModIntro. iExists γ. iFrame.
Qed.

Global Opaque own_ub.
