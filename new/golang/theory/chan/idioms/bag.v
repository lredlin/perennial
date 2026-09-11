Require Import New.proof.proof_prelude.
From New.golang.theory.chan.au_spec Require Import
  chan_au_base.
Require Import New.golang.theory.

(** * "Bag" channel specification.

    This channel spec has a user-chosen predicate P over values sent on the
    channel, but no ordering guarantees. It's like a "bag" of values, with
    `send` inserting and `receive` removing.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Collection W := sem + IntoValTyped0.

Definition is_chan_bag (γ : chan_names) (ch : loc) (P : V → iProp Σ) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ V ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chanstate.t V),
      "Hch" ∷ own_chan γ V s ∗
      match s with
      | chanstate.Idle => True
      | chanstate.SndWait v => P v
      | chanstate.SndDone v => P v
      | chanstate.Buffered vs => [∗ list] v ∈ vs, P v
      | chanstate.Closed buffer => False
      | _ => True
      end
  )%I.
#[global] Opaque is_chan_bag.
#[local] Transparent is_chan_bag.
#[global] Instance is_chan_bag_pers γ ch P : Persistent (is_chan_bag γ ch P).
Proof. apply _. Qed.

Lemma start_bag (P : V → iProp Σ) s (ch : loc) (γ : chan_names)  :
  match s with
  | chanstate.Idle | chanstate.Buffered [] => True
  | _ => False
  end →
  is_chan ch γ V -∗
  own_chan γ V s ={⊤}=∗
  is_chan_bag γ ch P.
Proof.
  iIntros "% #Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. destruct s; try destruct buff; done. }
  simpl.
  by iFrame "#".
Qed.

Lemma is_bag_is_chan γ ch P :
  is_chan_bag γ ch P -∗ is_chan ch γ V.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

(* Open the bag invariant and hand the arm the invariant's half. *)
Local Ltac bg_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iDestruct "Hi" as (s) "[Hoc HI]".
(* One credit strips the invariant body and the client's continuation together:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Phase two of a two-phase arm uses [bg_open], since
   the continuation was already stripped in phase one. *)
Local Ltac bg_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi HΦ" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi HΦ]";
  iDestruct "Hi" as (s) "[Hoc HI]".
Local Ltac bg_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
(* Closed states are banned by the invariant. *)
Local Ltac bg_absurd := bg_agree; iDestruct "HI" as "[]".
Local Ltac bg_step st :=
  bg_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %?;
  iMod (own_chan_halves_update st with "Hoc Himpl") as "[H1 H2]";
  [ simpl in *; lia | ].

Lemma bag_recv_au γ ch P Φ  :
  is_chan_bag γ ch P -∗
  (▷ ∀ v, P v -∗ Φ v true ) -∗
  recv_au γ V Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hbag HΦ". iNamed "Hbag".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : SndWait w -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". bg_openc. bg_step (@chanstate.RcvDone V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.RcvDone. by iFrame. }
    iModIntro. iFrame "H2". by iApply "HΦ".
  - (* recv_slow_path_au : Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". bg_openc. bg_step (@chanstate.RcvWait V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.RcvWait. by iFrame. }
    iModIntro. iFrame "H2". try iClear "HI".
    (* phase two: the continuation was stripped in phase one *)
    iIntros (w) "[Hlc Himpl]". bg_open. bg_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iModIntro. iFrame "H2". by iApply "HΦ".
  - (* recv_deq_au *)
    iIntros (w rest) "[Hlc Himpl]". bg_openc. bg_agree.
    iDestruct "HI" as "[HP HRest]".
    iDestruct (own_chan_cap_valid with "Himpl") as %?.
    iMod (own_chan_halves_update (chanstate.Buffered rest) with "Hoc Himpl") as "[H1 H2]".
    { simpl in *. lia. }
    iMod ("Hclose" with "[H1 HRest]") as "_".
    { iNext. iExists (chanstate.Buffered rest). iFrame. }
    iModIntro. iFrame "H2". by iApply "HΦ".
  - (* recv_drain_au : this idiom never closes *)
    iIntros (w rest) "[Hlc Himpl]". bg_openc. bg_absurd.
  - (* recv_closed_au *)
    iIntros "[Hlc Himpl]". bg_openc. bg_absurd.
Qed.

Lemma wp_bag_receive γ ch P :
  {{{ is_chan_bag γ ch P }}}
    chan.receive t #ch
  {{{ v, RET (#v, #true); P v }}}.
Proof using W.
  wp_start_folded as "#Hbag".
  iNamed "Hbag".
  wp_apply (chan.wp_receive ch γ with "[$Hch]").
  iIntros "_".
  iApply (bag_recv_au with "[$]").
  iNext. iFrame.
Qed.

Lemma bag_send_au γ ch P v (Φ: iProp Σ) :
  is_chan_bag γ ch P -∗
  P v -∗
  (▷ Φ) -∗
  send_au γ V v Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hbag HP HΦ". iNamed "Hbag".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". bg_openc. bg_step (chanstate.SndDone v).
    iMod ("Hclose" with "[H1 HP]") as "_".
    { iNext. iExists (chanstate.SndDone v). iFrame. }
    iModIntro. iFrame.
  - (* send_slow_path_au : Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". bg_openc. bg_step (chanstate.SndWait v).
    iMod ("Hclose" with "[H1 HP]") as "_".
    { iNext. iExists (chanstate.SndWait v). iFrame. }
    iModIntro. iFrame. try iClear "HI".
    (* phase two: the continuation was stripped in phase one *)
    iIntros "[Hlc Himpl]". bg_open. bg_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iModIntro. iFrame.
  - (* send_enq_au *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". bg_openc. bg_agree.
    iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v])) with "Hoc Himpl")
      as "[H1 H2]".
    { simpl. rewrite length_app /=. lia. }
    iMod ("Hclose" with "[H1 HI HP]") as "_".
    { iNext. iExists (chanstate.Buffered (buf ++ [v])).
      rewrite big_sepL_app /=. iFrame. }
    iModIntro. iFrame.
  - (* send_closed_au : this idiom never closes *)
    iIntros (drain) "[Hlc Himpl]". bg_openc. bg_absurd.
Qed.

Lemma wp_bag_send γ ch v P :
  {{{ is_chan_bag γ ch P ∗ P v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof using W.
  wp_start_folded as "[#Hbag HP]".
  unfold is_chan_bag. iNamed "Hbag".
  wp_apply (chan.wp_send ch with "[$Hch]").
  iIntros "_".
  iApply (bag_send_au with "[$] [$HP]").
  wp_end.
Qed.

End proof.
