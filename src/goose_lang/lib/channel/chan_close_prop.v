From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import auth_set.
From Perennial.algebra Require Import ghost_var.
From Perennial.goose_lang Require Import prelude. 
 From Perennial.goose_lang Require Import proofmode wpc_proofmode.
 From Perennial.goose_lang.lib Require Import typed_mem.
 From Perennial.goose_lang Require Import notation typing.

Record chan_close_prop_names :=
  { send_close_prop_name: gname;
    recv_close_prop_names_name: gname;
  }.


Class chanCloseG Σ := ChanCloseG {
    barrier_saved_propG :: savedPropG Σ;
    barrier_auth_setG :: auth_setG Σ gname;
  }.

Definition chanCloseΣ: gFunctors :=
  #[ savedPropΣ; auth_setΣ gname ].

#[global] Instance subG_chanCloseG Σ : subG chanCloseΣ Σ → chanCloseG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{hG: heapGS Σ, !ext_types _, chanCloseG Σ }.
Implicit Types (v:val).

Definition own_chan_close_props_ghost (γ: chan_close_prop_names) 
      : iProp Σ :=
(* The values of all the ghost state are existentially quantified since the
    caller interacts with them via ghost state: the [recv] predicate for [recvQ]
    and [send] predicates for the names in [sendNames] for the names in
    [sendNames]. *)
    "HChan"  ∷  ∃ (sendClosedQ: iProp Σ) (recvClosePropNames: gset gname),
(*| This ghost ownership owns only half of `γ.(recv_prop_name)`; the other half is controlled by `recv γ Q`. This division into two halves, one in a lock invariant and one owned by a thread, is a common pattern; we already saw it in the ParallelAdd example's ghost variables. |*)
    "sendClosedQ" ∷ saved_prop_own γ.(send_close_prop_name) (DfracOwn (1/2)) sendClosedQ ∗
(*| The number of `send` names (and thus number of predicates) is the number of waiting threads. An important consequence is that if `num_waiting = W64 0`, then there are no sendNames, and thus all threads have finished. |*)
    (*"%HnumWaiting" ∷ ⌜size sendNames = uint.nat num_waiting⌝ ∗ *)
    "HrecvNames_auth" ∷ auth_set_auth γ.(recv_close_prop_names_name) recvClosePropNames ∗
(*| This is the most important and most complex part of the ghost state. A useful bit of context is that whenever we create a `γS ∈ sendNames`, it will be used for a saved proposition, and it will be persisted into a read-only saved proposition (we never change the proposition of a given `send γ P`).

The effect of writing `∃ P, saved_prop_own γS DfracDiscarded P` is to "read" the value of γS as `P`, since ownership of the ghost variable means we know its value is `P`. We also have `∗ ▷ P` which asserts ownership over (later) P. Then all of this business implies `recvQ`, the value of `γ.(recv_prop_name)`.

Need the opposite here, must prove all of the recvclosed prop 
|*)
    "HsendClosedQ_wand" ∷ (▷sendClosedQ -∗ ([∗ set] γR ∈ recvClosePropNames,
                        ∃ P, saved_prop_own γR DfracDiscarded P ∗ ▷P)).

Definition recv_close_prop (γ: chan_close_prop_names) (P: iProp Σ): iProp Σ :=
∃ γR, auth_set_frag γ.(recv_close_prop_names_name) γR ∗
      saved_prop_own γR DfracDiscarded P.

Definition send_close_prop (γ: chan_close_prop_names) (Q: iProp Σ): iProp Σ :=
∃ Q', saved_prop_own γ.(send_close_prop_name) (DfracOwn (1/2)) Q' ∗
      (Q' -∗ Q).



Lemma recv_close_prop_split γ: 
∀ (P Q: iProp Σ), own_chan_close_props_ghost γ ∗ recv_close_prop γ (P ∗ Q) ==∗ own_chan_close_props_ghost γ ∗ (recv_close_prop γ P ∗ recv_close_prop γ Q).
Proof.
    iIntros (P). iIntros (Q).
   iIntros "HPQ". unfold own_chan_close_props_ghost. iNamed "HPQ". iNamed "HChan".
iMod (saved_prop_alloc_cofinite recvClosePropNames P DfracDiscarded)
        as (γRQ) "[%Hfresh #HrecRQ]".
      { done. }
      iNamed "Hbar".
      iDestruct "Hrecv" as (Q') "[recvQ2 HQwand]".
      iDestruct (saved_prop_agree with "recvQ recvQ2") as "#HQeq".
      iMod (saved_prop_update_halves (P ∗ recvQ) with "recvQ recvQ2")
        as "[recvQ recvQ2]".
      (* Allocating the new [send] saved proposition name is somewhat subtle: it
      needs to be different from any other (in-use) saved proposition. Since set
      available ghost names is infinite but the used names [sendNames] is finite,
      it's always possible to allocate such a name, and there's a "cofinite"
      allocation lemma to do just this. *)
      iMod (saved_prop_alloc_cofinite sendNames P DfracDiscarded)
        as (γS) "[%Hfresh #Hsend]".
      { done. }