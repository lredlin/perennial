Require Import New.proof.proof_prelude.
From New.golang.theory.chan.idioms Require Export base.
From New.golang.theory Require Import chan.

Section handshake.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Collection W := sem + IntoValTyped0.

(*----------------------------------------------------------------------------
  Invariant for a simple handshake on an unbuffered channel with unit payloads.

  - When the channel has an in-flight *send* (SndWait/SndDone), predicate [P]
    must hold (producer-side obligation).
  - When the channel has an in-flight *receive* (RcvWait/RcvDone), predicate [Q]
    must hold (consumer-side obligation).
  - Buffered channels are intentionally disallowed.
  - Closing is also disallowed in this idiom ([_ => False]).

  ---------------------------------------------------------------------------*)
Definition is_handshake γ (ch : loc)  (P: V -> iProp Σ) Q : iProp Σ :=
  is_chan ch γ V  ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_chan γ V s ∗
    (match s with
     | chanstate.Idle =>
        True
     | chanstate.SndWait v | chanstate.SndDone v =>
         P v
     | chanstate.RcvWait | chanstate.RcvDone =>
         Q
     (* Can't use buffered channel and we don't close here. *)
     | _ => False
     end
    )).

Lemma start_handshake ch P Q  γ:
  is_chan ch γ V -∗
  own_chan γ V chanstate.Idle ={⊤}=∗
  is_handshake γ ch P Q .
Proof.
  intros.
  iIntros "#? Hchan".
  iFrame "#". iFrame. simpl.
  iApply inv_alloc.
  iExists chanstate.Idle.
  iFrame "∗%#".
Qed.

(* Open the handshake invariant and hand the arm the invariant's half. *)
Local Ltac hs_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi Hcont" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi Hcont]";
  iDestruct "Hi" as (s) "[Hoc HI]".
(* Phase two of a two-phase arm: [Hcont] was already stripped in phase one. *)
Local Ltac hs_open2 :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iDestruct "Hi" as (s) "[Hoc HI]".
Local Ltac hs_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
(* The arm's pre-state contradicts the invariant. *)
Local Ltac hs_absurd := hs_agree; iDestruct "HI" as "[]".
Local Ltac hs_step st :=
  hs_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %?;
  iMod (own_chan_halves_update st with "Hoc Himpl") as "[H1 H2]";
  [ simpl in *; lia | ].

(* No later credits needed: each conjunct is discharged by agreement between
   the invariant's half of [own_chan] and the half the arm is handed. *)
Lemma handshake_receive_au γ ch P Q Φ :
  is_handshake γ ch P Q -∗
  Q -∗
  ▷(∀ v, P v -∗ Φ v true) -∗
  recv_au γ V Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#His HQ Hcont". iDestruct "His" as "[_ #Hinv]".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : SndWait v -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". hs_open. hs_step (@chanstate.RcvDone V).
    iMod ("Hclose" with "[H1 HQ]") as "_".
    { iNext. iExists chanstate.RcvDone. iFrame. }
    iModIntro. iFrame. by iApply ("Hcont" with "HI").
  - (* recv_slow_path_au : Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". hs_open. hs_step (@chanstate.RcvWait V).
    iMod ("Hclose" with "[H1 HQ]") as "_".
    { iNext. iExists chanstate.RcvWait. iFrame. }
    iModIntro. iFrame. try iClear "HI".
    iIntros (w) "[Hlc Himpl]". hs_open2. hs_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iModIntro. iFrame. by iApply ("Hcont" with "HI").
  - (* recv_deq_au : this idiom bans buffered channels *)
    iIntros (w rest) "[Hlc Himpl]". hs_open. hs_absurd.
  - (* recv_drain_au *)
    iIntros (w rest) "[Hlc Himpl]". hs_open. hs_absurd.
  - (* recv_closed_au : this idiom never closes *)
    iIntros "[Hlc Himpl]". hs_open. hs_absurd.
Qed.

Lemma wp_handshake_receive γ ch P Q :
  {{{
      is_handshake γ ch P Q  ∗
      Q
  }}}
    chan.receive t #ch
  {{{
      v, RET (#v, #true); P v
  }}}.
Proof using W.
  iIntros (?) "((#Hchan & #Hinv) & HQ) HΦ".
  wp_apply ((chan.wp_receive ch γ Φ  ) with "[$Hchan]").
  iIntros "_".
  iApply (handshake_receive_au with "[$Hchan $Hinv] [$HQ]").
  done.
Qed.

Lemma handshake_send_au γ ch v P Q Φ :
  is_handshake γ ch P Q -∗
  P v -∗
  ▷(Q -∗ Φ) -∗
  send_au γ V v Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#His HP Hcont". iDestruct "His" as "[_ #Hinv]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". hs_open. hs_step (chanstate.SndDone v).
    iMod ("Hclose" with "[H1 HP]") as "_".
    { iNext. iExists (chanstate.SndDone v). iFrame. }
    iModIntro. iFrame. by iApply ("Hcont" with "HI").
  - (* send_slow_path_au : Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". hs_open. hs_step (chanstate.SndWait v).
    iMod ("Hclose" with "[H1 HP]") as "_".
    { iNext. iExists (chanstate.SndWait v). iFrame. }
    iModIntro. iFrame. try iClear "HI".
    iIntros "[Hlc Himpl]". hs_open2. hs_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iModIntro. iFrame. by iApply ("Hcont" with "HI").
  - (* send_enq_au : this idiom bans buffered channels *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". hs_open. hs_absurd.
  - (* send_closed_au : this idiom never closes *)
    iIntros (drain) "[Hlc Himpl]". hs_open. hs_absurd.
Qed.

Lemma wp_handshake_send γ ch v P Q :
  {{{
      is_handshake γ ch P Q ∗
      P v
  }}}
    chan.send t #ch #v
  {{{
      RET (#()); Q
  }}}.
Proof using W.
  iIntros (?) "((#Hchan & #Hinv) & HP) HΦ".
  wp_apply ((chan.wp_send ch v γ Φ  ) with "[$Hchan]").
  iIntros "_".
  iApply (handshake_send_au with "[$Hchan $Hinv] [$HP]").
  done.
Qed.

End handshake.
