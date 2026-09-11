From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require Import channel_examples_init.
From New.golang.theory.chan.idioms
  Require Import base.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Invariant: channel must be Idle, all other states are False *)
Definition is_select_nb_only (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ s,
        "Hoc" ∷ own_chan γ unit s ∗
        "%" ∷ ⌜ (match s with
                | chanstate.Idle => True
                | _ => False
                end) ⌝
  ).

Lemma start_select_nb_only (ch : loc) (γ : chan_names) :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={⊤}=∗
  is_select_nb_only γ ch.
Proof.
  iIntros "#Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  iFrame "#". done.
Qed.

(* Every arm names a non-Idle pre-state, which the invariant rules out. *)
Local Ltac nb_open :=
  iInv "Hinv" as ">Hi" "Hclose";
  iNamed "Hi".
Local Ltac nb_absurd :=
  iDestruct (own_chan_agree with "Hoc Himpl") as %->; done.

(** Nonblocking send AU - vacuous since we ban all send preconditions *)
Lemma select_nb_only_send_au γ ch (v : unit) :
  ∀ Φ Φnotready,
  is_select_nb_only γ ch -∗
  Φnotready -∗
  nonblocking_send_au γ unit v Φ Φnotready.
Proof.
  iIntros (Φ Φnotready) "#Hnb Hnotready".
  iNamed "Hnb". rewrite /nonblocking_send_au.
  iSplit; [| iSplit; [| iSplit ] ].
  - iIntros "[Hlc Himpl]". nb_open. nb_absurd.
  - iIntros (buf) "(Hlc & %Hlt & Himpl)". nb_open. nb_absurd.
  - iIntros (drain) "[Hlc Himpl]". nb_open. nb_absurd.
  - iFrame "Hnotready".
Qed.

(** Nonblocking receive AU - vacuous since we ban all receive preconditions *)
Lemma select_nb_only_rcv_au γ ch :
   ∀ (Φ: unit → bool → iProp Σ) (Φnotready: iProp Σ),
  is_select_nb_only γ ch -∗
  Φnotready -∗
  nonblocking_recv_au γ unit (λ (v:unit) (ok:bool), Φ v ok) Φnotready.
Proof.
  iIntros (Φ Φnotready) "#Hnb Hnotready".
  iNamed "Hnb". rewrite /nonblocking_recv_au.
  iSplit; [| iSplit; [| iSplit; [| iSplit ] ] ].
  - iIntros (w) "[Hlc Himpl]". nb_open. nb_absurd.
  - iIntros (w rest) "[Hlc Himpl]". nb_open. nb_absurd.
  - iIntros (w rest) "[Hlc Himpl]". nb_open. nb_absurd.
  - iIntros "[Hlc Himpl]". nb_open. nb_absurd.
  - iFrame "Hnotready".
Qed.


(* Example 1 *)
Lemma wp_select_nb_not_ready :
  {{{ is_pkg_init channel_examples}}}
    @! channel_examples.select_nb_not_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#His_chan & _Hcap & Hownchan)".
  do 2 (iRename select (£1) into "Hlc1").
  wp_auto_lc 2.
  iRename select (£1) into "Hlc2".
  iPersist "ch".
  do 2 (iRename select (£1) into "Hlc4").
  iMod (start_select_nb_only ch with "[$His_chan] [$Hownchan]") as "#Hnb".
  wp_apply (wp_fork with "[Hnb]").
  {
  wp_auto_lc 4.
  wp_apply chan.wp_select_nonblocking.
  simpl. iSplitL.
  - (* Prove the receive case - will be vacuous *)
    iSplitL. all: try done.
    repeat iExists _; iSplitR; first done.
    (* extract is_chan *)
    iPoseProof "Hnb" as "[$ _]".
    (* Now use our select_nb_only_rcv_au lemma *)
    iRename select (£1) into "Hlc1".
    iApply (select_nb_only_rcv_au with " [$Hnb]");first done.
  - (* Prove the default case *)
    wp_auto.
    done.
  }
  {
  wp_apply chan.wp_select_nonblocking. simpl.
  iFrame.
  iSplitL "Hlc1 Hlc4".
  - (* Prove the receive case - will be vacuous *)
    iSplitL; last done.
    repeat iExists _; iSplitR; first done. iFrame "#". iClear "His_chan".
    iApply (select_nb_only_send_au with "[$Hnb] []"); first done.
  - (* Prove the default case *)
    wp_auto.
    iApply "HΦ".
    done.
  }
Qed.

(**  Example 2 *)
Lemma wp_select_nb_guaranteed_ready :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.select_nb_guaranteed_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros "* (#His_ch & %Hcap & Hch)". simpl.
  wp_auto.
  wp_apply (chan.wp_close with "[$]").
  iIntros "_". rewrite /close_au. iSplit; [| iSplit ].
  - (* close_idle_au: the channel is fresh, so it is idle *)
    iIntros "[Hlc Himpl]".
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
    iMod (own_chan_halves_update (chanstate.Closed []) with "Hch Himpl")
      as "[Hch H2]"; [ simpl in Hcv |- *; lia | ]. iModIntro. iFrame "H2".
    wp_auto.
    wp_apply (chan.wp_select_nonblocking_alt [False%I] with "[Hch] [-]");
      [|iNamedAccu|].
    + simpl. iSplitL; last done. iIntros "HP".
      repeat iExists _; iSplitR; first done. iFrame "#".
      rewrite /nonblocking_recv_au_alt.
      iSplit; [| iSplit; [| iSplit; [| iSplit ] ] ].
      * (* recv_fast_path_au *)
        iIntros (w) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hch Himpl") as %?.
      * (* recv_deq_au *)
        iIntros (w rest) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hch Himpl") as %?.
      * (* recv_drain_au: the channel was closed empty, so there is no drain *)
        iIntros (w rest) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hch Himpl") as %?.
      * (* recv_closed_au: the one reachable arm *)
        iIntros "[Hlc Himpl]". iModIntro. iFrame "Himpl".
        iNamed "HP". wp_auto. by iApply "HΦ".
      * (* recv_not_ready_au: this is what rules out the default branch -- a closed
           channel is always ready, so [recv_not_ready] is false here *)
        iIntros (s) "(Hlc & %Hnr & Himpl)".
        iDestruct (own_chan_agree with "Hch Himpl") as %<-.
        simpl in Hnr. done.
    + iNamed 1. simpl. iIntros ([[]]).
  - (* close_buf_au: the channel is unbuffered *)
    iIntros (buf) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hch Himpl") as %?.
  - (* close_closed_au: it is not closed yet *)
    iIntros (drain) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hch Himpl") as %?.
Qed.

(* Invariant for the "full buffer" situation                                  *)
Definition is_select_nb_full1 (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch"  ∷ is_chan ch γ w64 ∗
  "%Hcap1" ∷ ⌜chan_cap γ = (W64 1)⌝ ∗
  "#Hinv" ∷ (own_chan γ w64 (chanstate.Buffered [W64 0])).

Lemma start_select_nb_full1 (ch : loc) (γ : chan_names) :
  is_chan ch γ w64 -∗
  ⌜chan_cap γ = (W64 1)⌝ -∗
  own_chan γ w64 (chanstate.Buffered [W64 0]) ={⊤}=∗
  is_select_nb_full1 γ ch.
Proof.
  iIntros "#Hch %Hcap Hoc".
  iModIntro. iFrame "#". iFrame "%". iFrame.
Qed.

Lemma select_nb_full1_send_au (γ : chan_names) (ch : loc) :
  ∀ Φ Φnotready,
    is_select_nb_full1 γ ch -∗
    Φnotready -∗
    nonblocking_send_au γ w64 (W64 0) Φ Φnotready.
Proof.
  intros Φ Φnotready.
  iIntros "Hfull Hnotready".
  iNamed "Hfull".
  rewrite /nonblocking_send_au. iSplit; [| iSplit; [| iSplit ] ].
  - (* send_fast_path_au: a full buffer is not a rendezvous *)
    iIntros "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hfull Himpl") as %?.
  - (* send_enq_au: the implementation hands over the capacity fact, and at
       capacity 1 with one buffered value it is already false *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)".
    iDestruct (own_chan_agree with "Hfull Himpl") as %Heq.
    inversion Heq. subst buf. rewrite Hcap1 in Hlt. simpl in Hlt. word.
  - (* send_closed_au *)
    iIntros (drain) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hfull Himpl") as %?.
  - iFrame "Hnotready".
Qed.

Lemma send_au_from_empty_buffer_to
    (ch: loc) (γ: chan_names) (Φ : iProp Σ) :
  own_chan γ w64 (chanstate.Buffered []) -∗
  (own_chan γ w64 (chanstate.Buffered [W64 0]) -∗ Φ) -∗
  send_au γ w64 (W64 0) Φ.
Proof.
  iIntros "Hoc Hk".
  rewrite /send_au. iSplit; [| iSplit; [| iSplit ] ].
  - iIntros "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
  - iIntros "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
  - (* the only reachable arm: enqueue into the empty buffer *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)".
    iDestruct (own_chan_agree with "Hoc Himpl") as %Heq. inversion Heq. subst buf.
    iMod (own_chan_halves_update (chanstate.Buffered [W64 0]) with "Hoc Himpl")
      as "[H1 H2]"; [ simpl; simpl in Hlt; lia | ]. iModIntro. iFrame "H2". by iApply ("Hk" with "H1").
  - iIntros (drain) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
Qed.

(*
  From a send on full buffer (which blocks indefinitely), any Φ can be derived
*)
Lemma SendAU_full_cap1_vacuous
  (ch : loc) (γ : chan_names) (v0 v : w64) (Φ : iProp Σ) :
  chan_cap γ = (W64 1) ->
  own_chan γ w64 (chanstate.Buffered [v0]) -∗
  send_au γ w64 v Φ.
Proof.
  intros Hcap. iIntros "Hoc".
  rewrite /send_au. iSplit; [| iSplit; [| iSplit ] ].
  - iIntros "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
  - iIntros "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
  - (* the buffer is at capacity, so the enqueue arm's own premise is false *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)".
    iDestruct (own_chan_agree with "Hoc Himpl") as %Heq. inversion Heq. subst buf.
    rewrite Hcap in Hlt. simpl in Hlt. word.
  - iIntros (drain) "[Hlc Himpl]". by iDestruct (own_chan_agree with "Hoc Himpl") as %?.
Qed.

(* Example 3 *)
Lemma wp_select_nb_full_buffer_not_ready :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.select_nb_full_buffer_not_ready #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2.

  wp_apply (chan.wp_make2) as (ch γ) "(#His_chan & %Hcap & Hown)"; first done.

  (* First send: use the empty-buffer AU to fill buffer to [0]. *)
  wp_apply (chan.wp_send ch (W64 0) γ with "[$His_chan]").
  iIntros "Hlc_send". simpl.
  iApply ((send_au_from_empty_buffer_to ch γ) with "Hown").

  (* Now we have: own_chan ch (Buffered [0]) γ in the continuation. *)
  iIntros "Hoc".
  iMod (start_select_nb_full1 ch γ with "[$His_chan] [%] [$Hoc]") as "Hfull".
{ exact Hcap. }  (* supplies ⌜chan_cap γ = 1⌝ *)
wp_auto.

  (* Nonblocking select: show send case is disabled -> default taken. *)
  wp_apply chan.wp_select_nonblocking.

  iSplit.
  - simpl. iSplit; last done.
    iExists w64, ch,γ, (W64 0). repeat iExists _.

    iSplit; [iPureIntro; split;first done;reflexivity|].
    iSplit; [iFrame "#"; done|].
    (* AU for send case: forced not-ready by full-buffer invariant.
      => We can get contradiction
    *)
    iApply (select_nb_full1_send_au γ ch with "[$Hfull]").
    all:try done.
  - (* default branch *)
    wp_auto. iApply "HΦ". done.
    Unshelve.
    + apply sem.
    + apply _.
Qed.

End proof.
