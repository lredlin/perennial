From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth.


Record chan_names := {
  offer_name : gname;
  state_name: gname;
  close_name : gname;
}.

Inductive offer_state :=
  | Idle
  | Offer
  | Accept
  | Closed.
  #[global] Instance offer_state_eq_dec : EqDecision offer_state.
Proof. solve_decision. Defined.

Module chan_state.
Inductive BufferedChannel (V : Type) : Type :=
| Buffer : list V -> nat -> BufferedChannel V.

Inductive UnbufferedChannel (V : Type) : Type :=
| Idle : UnbufferedChannel V
| SndWait : V -> UnbufferedChannel V
| RcvWait : UnbufferedChannel V
| SndDone : V -> UnbufferedChannel V
| RcvDone : UnbufferedChannel V
.

Inductive OpenChannel (V : Type) : Type :=
| Buffered : BufferedChannel V -> OpenChannel V
| Unbuffered : UnbufferedChannel V -> OpenChannel V.

Inductive Channel (V : Type) : Type :=
| Open : OpenChannel V -> Channel V
| Closed : Channel V.

(* Unified physical state for both buffered and unbuffered channels *)
Record chan_phys_state (V : Type) :=
  mk_chan_phys {
    ch: loc;
    mu: loc;
    state: OpenChannel V;  (* Either buffered or unbuffered *)
    buff_slice_or: option slice.t;  (* Some for buffered, None for unbuffered *)
  }.

(* Alternative: Separate records if you really need them *)
Record buff_chan_phys_state (V : Type) :=
  mk_buff_chan {
    buff_ch: loc;
    buff_mu: loc;
    buff_state: BufferedChannel V;
    buff_slice: slice.t;
  }.

Record unbuff_chan_phys_state (V: Type) :=
  mk_unbuff_chan {
    unbuff_ch: loc;
    unbuff_mu: loc;
    unbuff_state: UnbufferedChannel V;
  }.

(* Arguments for inductive constructors *)
Global Arguments Buffer {V}.
Global Arguments Idle {V}.
Global Arguments SndWait {V}.
Global Arguments RcvWait {V}.
Global Arguments SndDone {V}.
Global Arguments RcvDone {V}.
Global Arguments Buffered {V}.
Global Arguments Unbuffered {V}.
Global Arguments Open {V}.
Global Arguments Closed {V}.

(* Arguments for the unified record *)
Global Arguments mk_chan_phys {V}.
Global Arguments ch {V} _.
Global Arguments mu {V} _.
Global Arguments state {V} _.
Global Arguments buff_slice_or {V} _.  

(* Arguments for separate buffered record *)
Global Arguments mk_buff_chan {V}.
Global Arguments buff_ch {V} _.
Global Arguments buff_mu {V} _.
Global Arguments buff_state {V} _.
Global Arguments buff_slice {V} _.

(* Arguments for separate unbuffered record *)
Global Arguments mk_unbuff_chan {V}.
Global Arguments unbuff_ch {V} _.
Global Arguments unbuff_mu {V} _.
Global Arguments unbuff_state {V} _.
End chan_state.



Class chanGhostStateG Σ V := ChanGhostStateG {
  offer_tokG :: ghost_varG Σ (option V);
  chan_stateG :: ghost_varG Σ (chan_state.Channel V);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ (option V); ghost_varΣ (chan_state.Channel V) ].



#[global] Instance subG_chanGhostStateG Σ V :
  subG (chanGhostStateΣ V) Σ → chanGhostStateG Σ V.
Proof. solve_inG. Qed.

Section lemmas.
  Context `{!chanGhostStateG Σ V}.

  Definition idle_tok (γ : gname) : iProp Σ :=
    ghost_var γ 1%Qp None.

  Definition snd_wait_tok (γ : gname) (v: V) : iProp Σ :=
    ghost_var γ (1/2%Qp) (Some v).

  Definition rcv_wait_tok (γ : gname) : iProp Σ :=
    ghost_var γ (1/2%Qp) None.

End lemmas.

