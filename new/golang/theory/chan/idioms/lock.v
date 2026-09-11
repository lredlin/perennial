Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms Require Export base.


(** * Lock Channel Idiom

    Note: If you can change the code and you aren't using select, just use a mutex.
    This pattern otherwise doesn't serve a practical purpose.

    This file provides a mutual exclusion abstraction using a buffered channel
    with capacity 1. The idiom uses channel buffer presence as the lock state:
    - Empty buffer: unlocked, resource R is available
    - One value in buffer: locked, resource R is inaccessible

    Key features:
    - Exactly one lock holder at a time (enforced by channel capacity)
    - Unbuffered and close operations are banned
    - Lock acquisition via send (blocking until buffer empty)
    - Lock release via receive (emptying the buffer)
    - Mutual exclusion guaranteed by channel's inherent single-slot capacity
*)

Section lock_channel.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
Collection W := sem + IntoValTyped0.
Set Default Proof Using "W".

Record lock_channel_names := {
  lchan_name : chan_names;      (* Underlying channel ghost state *)
  locked_name : gname;          (* Ghost bool tracking lock state *)
}.

Definition is_lock_channel (γ : lock_channel_names) (ch : loc)
                            (R : iProp Σ) : iProp Σ :=
  "#Hchan" ∷ is_chan ch γ.(lchan_name) V ∗
  "#Hinv" ∷ inv nroot (
    ∃ s locked,
      "Hch" ∷ own_chan γ.(lchan_name) V s ∗
      "%Hcap" ∷ ⌜ chan_cap γ.(lchan_name) = W64 1 ⌝ ∗
      (match s with
       | chanstate.Buffered [] =>
          ⌜locked = false⌝ ∗ R
       | chanstate.Buffered [v] =>
           ⌜locked = true⌝
       | _ =>
           (* Ban unbuffered and close states *)
           False
       end)
  )%I.

Lemma start_lock_channel ch (R : iProp Σ) γ :
  chan_cap γ = W64 1 ->
  is_chan ch γ V -∗
  own_chan γ V (chanstate.Buffered []) -∗
  ▷ R ={⊤}=∗
    (∃ γlock, is_lock_channel γlock ch R).
Proof.
  intros Hcap.
  iIntros "#Hch Hoc HR".
  iMod (dghost_var_alloc false) as (γlocked) "[HlockedI HlockedF]".
  set (γlock := {| lchan_name := γ; locked_name := γlocked |}).

  iMod (inv_alloc nroot _ (
            ∃ s locked,
              "Hch" ∷ own_chan γ V s ∗
              "%Hcap" ∷ ⌜ chan_cap γ = W64 1 ⌝ ∗
              (match s with
               | chanstate.Buffered [] =>
                   ⌜locked = false⌝∗ R
               | chanstate.Buffered [v] =>
                   ⌜locked = true⌝
               | _ =>
                   False
               end)
          ) with "[Hoc HlockedI HlockedF HR]") as "#Hinv".
  {
    iNext.  iFrame. replace (γlocked) with (γlock.(locked_name)) by done.  
    iExists false. iFrame. done.
  }
  iModIntro.
  iFrame "#".
  iExists γlock.
  unfold is_lock_channel.
  replace (γ) with (γlock.(lchan_name)) by done.
  iFrame "#".
Qed.

Lemma is_lock_channel_is_chan γ ch R :
  is_lock_channel γ ch R ⊢ is_chan ch γ.(lchan_name) V.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

(* Open the lock-channel invariant and hand the arm the invariant's half. *)
Local Ltac lc_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iDestruct "Hi" as (s locked) "(Hoc & %Hcap & HI)".
(* When the client's continuation is itself latered, one credit strips both:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Lemmas with an unlatered continuation use [lc_open]. *)
Local Ltac lc_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi Hcont" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi Hcont]";
  iDestruct "Hi" as (s locked) "(Hoc & %Hcap & HI)".
Local Ltac lc_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
(* Unbuffered and closed states are banned by the invariant. *)
Local Ltac lc_absurd := lc_agree; iDestruct "HI" as "[]".

Lemma lock_channel_send_au γ ch (v : V) (R : iProp Σ) :
  ∀ (Φ: iProp Σ),
  is_lock_channel γ ch R -∗
  ▷ (R -∗ Φ) -∗
  send_au γ.(lchan_name) V v Φ.
Proof.
  iIntros (Φ) "#Hlock Hcont".
  iDestruct "Hlock" as "[#Hchan #Hinv]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au: unbuffered states are banned *)
    iIntros "[Hlc Himpl]". lc_openc. lc_absurd.
  - (* send_slow_path_au *)
    iIntros "[Hlc Himpl]". lc_openc. lc_absurd.
  - (* send_enq_au: cap = 1, so the capacity fact forces an empty buffer *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". lc_openc. lc_agree.
    destruct buf as [|v' rest].
    + iDestruct "HI" as "(%Hlocked & HR)".
      iMod (own_chan_halves_update (chanstate.Buffered [v]) with "Hoc Himpl") as "[H1 H2]".
      { simpl. rewrite Hcap. word. }
      iMod ("Hclose" with "[H1]") as "_".
      { iNext. iExists (chanstate.Buffered [v]), true. iFrame "H1". iFrame "%". done. }
      iModIntro. iFrame "H2". by iApply ("Hcont" with "HR").
    + exfalso. rewrite Hcap in Hlt. simpl in Hlt. word.
  - (* send_closed_au *)
    iIntros (drain) "[Hlc Himpl]". lc_openc. lc_absurd.
Qed.

(* Nonblocking acquire.  Same three real obligations as the blocking version;
   the not-ready payload is [True] because failing to acquire tells us nothing. *)
Lemma lock_channel_nonblocking_send_au γ ch (v : V) (R : iProp Σ) :
  ∀ Φ,
  is_lock_channel γ ch R -∗
  (R -∗ Φ) -∗
  nonblocking_send_au γ.(lchan_name) V v Φ True.
Proof.
  iIntros (Φ) "#Hlock Hcont".
  iDestruct "Hlock" as "[#Hchan #Hinv]".
  rewrite /nonblocking_send_au. iSplit; [| iSplit; [| iSplit ] ].
  - (* send_fast_path_au: unbuffered states are banned *)
    iIntros "[Hlc Himpl]". lc_open. lc_absurd.
  - (* send_enq_au: cap = 1, so the capacity fact forces an empty buffer *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". lc_open. lc_agree.
    destruct buf as [|v' rest].
    + iDestruct "HI" as "(%Hlocked & HR)".
      iMod (own_chan_halves_update (chanstate.Buffered [v]) with "Hoc Himpl") as "[H1 H2]".
      { simpl. rewrite Hcap. word. }
      iMod ("Hclose" with "[H1]") as "_".
      { iNext. iExists (chanstate.Buffered [v]), true. iFrame "H1". iFrame "%". done. }
      iModIntro. iFrame "H2". by iApply ("Hcont" with "HR").
    + exfalso. rewrite Hcap in Hlt. simpl in Hlt. word.
  - (* send_closed_au: this idiom never closes *)
    iIntros (drain) "[Hlc Himpl]". lc_open. lc_absurd.
  - done.
Qed.

Lemma wp_lock_channel_lock γ ch (v:V) (R : iProp Σ) :
  {{{ is_lock_channel γ ch R }}}
    chan.send t #ch #v
  {{{ RET #(); R }}}.
Proof.
  iIntros (Φ) "#Hlock Hcont".
  iNamed "Hlock".
  wp_apply (chan.wp_send ch v γ.(lchan_name) with "[$Hchan]").
  iIntros "_".
  iApply (lock_channel_send_au with "[$Hchan $Hinv]").
  iNext. iFrame.
Qed.

Lemma lock_channel_recv_au γ ch (R : iProp Σ) :
  ∀ Φ,
  is_lock_channel γ ch R -∗
  R -∗
  ▷ (∀ v, Φ v true) -∗
  recv_au γ.(lchan_name) V Φ.
Proof.
  iIntros (Φ) "#Hlock HR Hcont".
  iDestruct "Hlock" as "[#Hchan #Hinv]".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au *)
    iIntros (w) "[Hlc Himpl]". lc_openc. lc_absurd.
  - (* recv_slow_path_au *)
    iIntros "[Hlc Himpl]". lc_openc. lc_absurd.
  - (* recv_deq_au: the buffer holds exactly the one token *)
    iIntros (w rest) "[Hlc Himpl]". lc_openc. lc_agree.
    destruct rest as [|? ?]; last (iDestruct "HI" as "[]").
    iDestruct "HI" as "%Hlocked".
    iMod (own_chan_halves_update (@chanstate.Buffered V []) with "Hoc Himpl") as "[H1 H2]".
    { simpl. rewrite Hcap. word. }
    iMod ("Hclose" with "[H1 HR]") as "_".
    { iNext. iExists (chanstate.Buffered []), false. iFrame "H1". iFrame "%". by iFrame. }
    iModIntro. iFrame "H2". by iApply "Hcont".
  - (* recv_drain_au *)
    iIntros (w rest) "[Hlc Himpl]". lc_openc. lc_absurd.
  - (* recv_closed_au *)
    iIntros "[Hlc Himpl]". lc_openc. lc_absurd.
Qed.

Lemma wp_lock_channel_unlock γ ch (R : iProp Σ) :
  {{{ is_lock_channel γ ch R ∗ R }}}
    chan.receive t #ch
  {{{ (v : V), RET (#v, #true); True }}}.
Proof.
  iIntros (Φ) "(#Hlock & HR) Hcont".

  iDestruct "Hlock" as "[#Hchan #Hinv]".

  iApply (chan.wp_receive ch γ.(lchan_name) with "[$Hchan]").
  iIntros "_".
  iApply ((lock_channel_recv_au γ ch R) with "[$Hchan $Hinv] [$HR]").
  iNext. iIntros (w). iApply "Hcont". done.
Qed.

End lock_channel.
