From iris.algebra.lib Require Import dfrac_agree.
Require Import New.golang.theory.
Require Import New.proof.proof_prelude.

(** A pattern for channel usage: a channel that never has anything sent, and is
    only closed at some point. Closing broadcasts a persistent proposition to
    all readers. *)

Record broadcast_internal_names :=
  { done_gn : gname }.

Module broadcast.
Inductive t := Pending | Done | Unknown.
End broadcast.
Import broadcast.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!go.Semantics}.

(* Note: could make the namespace be user-chosen *)
#[local] Definition is_broadcast_chan_internal (ch : chan.t) γ γch (Q : iProp Σ) : iProp Σ :=
  "#His_ch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ (st : chanstate.t unit),
        "Hch" ∷ own_chan γ unit st ∗
        "Hs" ∷ (match st with
                | chanstate.Idle
                | chanstate.RcvWait =>
                    own γch.(done_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
                | chanstate.Closed [] =>
                    □ Q ∗ own γch.(done_gn) (to_dfrac_agree DfracDiscarded true)
                | _ => False
                end)
    ).

Definition own_broadcast_chan (ch : chan.t) γ (Q : iProp Σ) (st : broadcast.t) : iProp Σ :=
  ∃ γch,
  "#Hinv" ∷ is_broadcast_chan_internal ch γ γch Q ∗
  "Hown" ∷ (match st with
            | Pending => own γch.(done_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
            | Done => own γch.(done_gn) (to_dfrac_agree DfracDiscarded true)
            | Unknown => True
            end).

#[global] Opaque own_broadcast_chan.
#[local] Transparent own_broadcast_chan.
#[global] Instance own_broadcast_chan_Unknown_pers ch γch P :
  Persistent (own_broadcast_chan ch γch P Unknown) := _.
#[global] Instance own_broadcast_chan_Done_pers ch γch P :
  Persistent (own_broadcast_chan ch γch P Done) := _.

Lemma broadcast_chan_done ch γ Q :
  £ 1 -∗ own_broadcast_chan ch γ Q Done ={⊤}=∗
  Q.
Proof.
  iIntros "Hlc". iNamed 1. iNamed "Hinv". iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  destruct st; try by iExFalso; simpl.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - destruct drain; try done.
    iClear "Hown". iDestruct "Hs" as "[#? ?]". iMod ("Hclose" with "[-]"). { iFrame. iFrame "∗#". }
    iModIntro. iFrame "#".
Qed.

(* Open the broadcast invariant and hand the arm the invariant's half. *)
Local Ltac bc_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iDestruct "Hi" as (st) "[Hoc Hs]".
(* One credit strips the invariant body and the client's continuation together:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Phase two of a two-phase arm uses [bc_open], since
   the continuation was already stripped in phase one. *)
Local Ltac bc_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi HΦ" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi HΦ]";
  iDestruct "Hi" as (st) "[Hoc Hs]".
Local Ltac bc_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
(* States the broadcast invariant bans. *)
Local Ltac bc_absurd := bc_agree; iDestruct "Hs" as "[]".
Local Ltac bc_step st :=
  bc_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %?;
  iMod (own_chan_halves_update st with "Hoc Himpl") as "[H1 H2]";
  [ simpl in *; lia | ].

Lemma broadcast_chan_receive ch γ Q Φ cl :
  own_broadcast_chan ch γ Q cl -∗
  (□Q ∗ own_broadcast_chan ch γ Q Done -∗ Φ () false) -∗
  recv_au γ unit Φ.
Proof.
  iNamed 1. iIntros "HΦ". iNamed "Hinv".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au: no sender ever offers on a broadcast channel *)
    iIntros (w) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_slow_path_au: post the offer; the second phase can never fire, so the
       wake-up goes through recv_closed_au after the offer is rescinded *)
    iIntros "[Hlc Himpl]". bc_open. bc_step (@chanstate.RcvWait unit).
    iMod ("Hclose" with "[H1 Hs]") as "_".
    { iNext. iExists chanstate.RcvWait. iFrame. }
    iModIntro. iFrame "H2".
    iIntros (w) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_deq_au: unbuffered *)
    iIntros (w rest) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_drain_au: the closed channel is always drained *)
    iIntros (w rest) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_closed_au: closed means the broadcast fired *)
    iIntros "[Hlc Himpl]". bc_open. bc_agree.
    iDestruct "Hs" as "[#HQ #Hdone]".
    iMod ("Hclose" with "[Hoc]") as "_".
    { iNext. iExists (chanstate.Closed []). iFrame "Hoc". iFrame "#". }
    iModIntro. iFrame "Himpl". iApply "HΦ". iFrame "#".
Qed.

Lemma own_broadcast_chan_nonblocking_receive ch γ Q Φ Φnotready cl :
  own_broadcast_chan ch γ Q cl -∗
  (match cl with
   | Unknown | Done => (own_broadcast_chan ch γ Q Done -∗ Φ () false)
   | _ => True
   end ∧
   match cl with
   | Unknown | Pending => (own_broadcast_chan ch γ Q cl -∗ Φnotready)
   | _ => True
   end)
  -∗
  nonblocking_recv_au_alt γ unit Φ Φnotready.
Proof.
  iNamed 1. iNamed "Hinv". subst. iIntros "HΦ".
  rewrite /nonblocking_recv_au_alt. repeat iSplit.
  - (* recv_fast_path_au *)
    iIntros (w) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_deq_au *)
    iIntros (w rest) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_drain_au *)
    iIntros (w rest) "[Hlc Himpl]". bc_open. bc_absurd.
  - (* recv_closed_au: the broadcast has fired *)
    iIntros "[Hlc Himpl]". bc_open. bc_agree.
    iDestruct "Hs" as "[#HQ #Hdone]".
    iMod ("Hclose" with "[Hoc]") as "_".
    { iNext. iExists (chanstate.Closed []). iFrame "Hoc". iFrame "#". }
    iModIntro. iFrame "Himpl".
    destruct cl.
    + (* Pending contradicts the discarded token *)
      iCombine "Hdone Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iLeft in "HΦ". iApply "HΦ". iFrame "#".
    + iLeft in "HΦ". iApply "HΦ". iFrame "#".
  - (* recv_not_ready_au: not ready means the broadcast has not fired yet *)
    rewrite /recv_not_ready_au.
    iIntros (s) "(Hlc & %Hnr & Himpl)".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iDestruct "Hi" as (st) "[Hoc Hs]".
    iDestruct (own_chan_agree with "Hoc Himpl") as %<-.
    destruct st; simpl in Hnr; try done; try (iDestruct "Hs" as "[]").
    (* a not-ready state means the broadcast has not fired, so cl ≠ Done *)
    all: iAssert (⌜ cl ≠ Done ⌝)%I as %Hcl;
         [ destruct cl; try done;
           iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid; naive_solver | ].
    all: iMod ("Hclose" with "[Hoc Hs]") as "_";
         [ iNext; iExists _; iFrame "Hoc Hs" | ].
    all: try iModIntro; iFrame "Himpl"; destruct cl; try done;
         iRight in "HΦ"; iApply "HΦ"; iFrame "∗#".
Qed.

Lemma broadcast_close_au ch γch Q Φ :
  own_broadcast_chan ch γch Q Pending -∗
  □ Q -∗
  ▷ (own_broadcast_chan ch γch Q Done -∗ Φ) -∗
  close_au γch unit Φ.
Proof.
  iNamed 1. iIntros "#HQ HΦ". iNamed "Hinv".
  rewrite /close_au. repeat iSplit.
  - (* close_idle_au *)
    iIntros "[Hlc Himpl]". bc_openc. bc_step (@chanstate.Closed unit []).
    iCombine "Hown Hs" as "Hown". rewrite -dfrac_agree_op dfrac_op_own Qp.half_half.
    iMod (own_update _ _ (to_dfrac_agree DfracDiscarded true) with "Hown") as "#H".
    { apply cmra_update_exclusive. done. }
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists (chanstate.Closed []). iFrame "H1". iFrame "#". }
    iModIntro. iFrame "H2". iApply "HΦ". iFrame "∗#".
  - (* close_buf_au: unbuffered *)
    iIntros (buf) "[Hlc Himpl]". bc_openc. bc_absurd.
  - (* close_closed_au: a Pending token rules out an already-closed channel *)
    iIntros (drain) "[Hlc Himpl]". bc_openc. bc_agree.
    destruct drain; last (iDestruct "Hs" as "[]").
    iRight in "Hs".
    iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
Qed.

Lemma wp_broadcast_chan_close `[!ty ↓u go.ChannelType dir (go.StructType [])] ch γch Q :
  {{{ own_broadcast_chan ch γch Q Pending ∗ □ Q }}}
  #(functions go.close [ty]) #ch
  {{{ RET #(); own_broadcast_chan ch γch Q Done }}}.
Proof.
  wp_start_folded as "[Hown #HQ]".
  iAssert (is_chan ch γch unit) as "#His".
  { iNamed "Hown". iNamed "Hinv". iFrame "#". }
  wp_apply (chan.wp_close with "His"). iIntros "Hlcs".
  iApply (broadcast_close_au with "Hown HQ [HΦ]").
  iNext. iIntros "Hclosed". by iApply "HΦ".
Qed.

Lemma alloc_broadcast_chan {E} Q γ ch :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={E}=∗
  own_broadcast_chan ch γ Q Pending.
Proof.
  iIntros "#? Hch".
  iMod (own_alloc
          ((to_dfrac_agree (DfracOwn (1/2)) false) ⋅ (to_dfrac_agree (DfracOwn (1/2)) false))
       ) as (tok_gn) "Htok".
  { rewrite -dfrac_agree_op //. }
  iDestruct "Htok" as "[Htok Htok2]".
  iAssert (|={E}=> is_broadcast_chan_internal ch γ ltac:(econstructor) Q)%I with "[-Htok]" as ">#H".
  2:{ iFrame "∗#". simpl. iFrame. done. }
  simpl. iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame. iFrame.
Qed.

Lemma own_broadcast_chan_Unknown ch γ Q cl :
  own_broadcast_chan ch γ Q cl -∗
  own_broadcast_chan ch γ Q Unknown.
Proof. iNamed 1. iFrame "#". Qed.

Lemma own_broadcast_chan_is_chan ch γ Q cl :
  own_broadcast_chan ch γ Q cl -∗
  is_chan ch γ unit.
Proof. iNamed 1. iNamed "Hinv". iFrame "#". Qed.

End proof.
