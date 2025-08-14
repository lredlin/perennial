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
Record t (V : Type) :=
  mk {
    mu: loc;
    (* slice that acts as buffered channel's buffer *)
    buff: list V;
    buff_slice: slice.t;
    (* 0 for unbuffered, size of buffer for buffered *)
    cap: w64;
    value: option V;
    state: offer_state;
  }.
Global Arguments mk {V}.
Global Arguments mu {V} (_).
Global Arguments buff {V} (_).
Global Arguments buff_slice {V} (_).
Global Arguments cap {V} (_).
Global Arguments value {V} (_).
Global Arguments state {V} (_).
Global Instance settable (V : Type) : Settable (t V) :=
  settable! (mk (V:=V)) < mu; buff; buff_slice; cap; value; state >.
End chan_state.



Class chanGhostStateG Σ V := ChanGhostStateG {
  offer_tokG :: ghost_varG Σ unit;
  chan_stateG :: ghost_varG Σ (chan_state.t V);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ unit; ghost_varΣ (chan_state.t V) ].



#[global] Instance subG_chanGhostStateG Σ V :
  subG (chanGhostStateΣ V) Σ → chanGhostStateG Σ V.
Proof. solve_inG. Qed.

Section lemmas.
  Context `{!chanGhostStateG Σ V}.

  Definition offer_idle (γ : gname) : iProp Σ :=
    ghost_var γ 1%Qp ().

  Definition offer_out (γ : gname) : iProp Σ :=
    ghost_var γ (1/2%Qp) ().

End lemmas.

