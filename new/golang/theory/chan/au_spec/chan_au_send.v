From New.golang.theory.chan.au_spec Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.mit_pdos.perennial.goose.model.channel.
From New.generatedproof.github_com.mit_pdos.perennial.goose Require Import model.channel.
Require Import New.proof.github_com.goose_lang.primitive.

#[local] Transparent is_chan own_chan.
#[local] Typeclasses Transparent is_chan own_chan.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.
Collection Wp := sem_fn + pre_sem + sem.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Collection W := Wp + IntoValTyped0.

Implicit Types (ch : loc) (γ : chan_names) (v : V).

Lemma wp_Cap ch γ :
  {{{ is_chan ch γ V }}}
    ch @! (go.PointerType (channel.Channel t)) @! "Cap" #()
  {{{ RET #(chan_cap γ); True }}}.
Proof using W.
  wp_start as "#Hch".
  wp_auto.
  iDestruct (is_chan_not_null with "Hch") as %Hnn.
  iNamed "Hch".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Len ch γ :
  {{{ is_chan ch γ V }}}
    ch @! (go.PointerType (channel.Channel t)) @! "Len" #()
  {{{ (l: w64), RET #l; ⌜0 ≤ sint.Z l ≤ sint.Z $ chan_cap γ⌝ }}}.
Proof using W.
  wp_start as "#His".
  wp_auto.
  iDestruct (is_chan_not_null with "His") as %Hnn.
  iNamed "His".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  destruct s.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    cbn [chan_logical].
    iDestruct (own_chan_buffer_size with "offer") as %Heq.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.Buffered buffer); iFrame. }
    iApply "HΦ".
    iPureIntro.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - (* chanphys.Closed(buffer) *)
    destruct buffer.
    {
      (* buffer = nil *)
      iNamed "phys".
      wp_auto.
      iDestruct (own_slice_len with "slice") as %Hlen.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
      { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
      iApply "HΦ".
      iPureIntro.
      simpl in *.
      word.
    }
    (* length buffer > 0 *)
    {
      iNamed "phys".
      iAssert (⌜1 + (Z.of_nat (length buffer)) ≤ sint.Z $ chan_cap γ⌝)%I as %Hbuffer_bound.
      {
        iNamedSuffix "offer" "2".
        simpl in Hcapvalid2.
        iPureIntro. lia.
      }
      wp_auto.
      iDestruct (own_slice_len with "slice") as %Hlen.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
      { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
      iApply "HΦ".
      iPureIntro.
      simpl in *.
      lia.
    }
Qed.

Local Lemma wp_TrySend_blocking ch v γ :
  ∀ Φ,
  is_chan ch γ V -∗
  send_au γ V v (Φ (#true)) ∧ Φ (#false) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TrySend" #v #true {{ Φ }}.
Proof using W.
  wp_start as "Hunb". iNamed "Hunb".
  wp_auto_lc 5.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s.

  - (* chanphys.Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl [Hsl _]". wp_auto.
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]") as (fr) "(Hfr & Hfrsl & Hsl)" --lc 1.

      iApply fupd_wp. iLeft in "HΦ".
      iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* send_enq_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Buffered buffer))%I with "[Hchanrepfrag]" as "Hown".
      { iFrame "#∗". iPureIntro. unfold chan_cap_valid. done. }
      assert (length buffer < sint.Z $ chan_cap γ).
      { word. }
      iMod ("HΦ" $! buffer with "[$Hlc $Hown]") as "[Hgv2 Hstep]".
      { iPureIntro. lia. }
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer Hfr Hfrsl Hgv2 $Hlock]").
      { unfold chan_inv_inner. iExists (chanphys.Buffered (buffer ++ [v])). iFrame. }
      done.
    }
    {
      wp_apply (wp_Mutex__Unlock
        with "[$lock state slice_cap Hchanrepfrag buffer slice $Hlock]").
      { unfold chan_inv_inner. iExists (chanphys.Buffered buffer). iFrame "#∗".
        iPureIntro. done.
      }
      iRight in "HΦ". iFrame.
    }
  - (* chanphys.Idle - make offer *)
    iNamed "phys". wp_auto_lc 4.
    iNamed "offer".
    iDestruct (offer_idle_to_send γ _ (_ ∧ Φ #false) (Φ (# true)) v with "Hoffer") as ">[offer1 offer2]".

    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer1 Hpred Hchanrepfrag HΦ $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndWait v).
      (* Frame the invariant's own half explicitly: [own_chan] is transparent
         here, so a bare [iFrame] would push it into the parked AU's own
         [own_chan chanphys.Idle] instead. *)
      iFrame "state v slice slice_cap buffer offer1 Hpred HΦ".
      iSplitR "Hchanrepfrag".
      { (* park exactly the conjunct this offer will be fired with *)
        iIntros "H". iLeft in "H". iRight in "H". iLeft in "H". iFrame. }
      iFrame "∗#%". }

    wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys". iNamed "offer".
    destruct s.

    + iNamed "phys". wp_auto_lc 5.
      simpl in Hcapvalid.
      iNamedSuffix "offer" "2".
      simpl in Hcapvalid2.
      lia.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iApply (saved_offer_half_full_invalid with "offer2 Hoffer").

    + unfold chan_phys. iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iDestruct (saved_offer_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      iMod (saved_prop.saved_pred_update (uncurry Φr0) with "Hpred") as "[Hpred1 Hpred2]".
      iCombine "Hpred1 Hpred2" as "Hp".
      wp_apply (wp_Mutex__Unlock
        with "[$lock state v slice slice_cap buffer Hchanrepfrag Hp H1 $Hlock]").
      { unfold chan_inv_inner. iExists (@chanphys.Idle V). iFrame. done. }
      iRewrite -"Hpeq" in "HP".
      iRight in "HP". iFrame.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (saved_offer_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      congruence.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (saved_offer_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      congruence.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".

      iApply fupd_wp.
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.RcvDone))%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
      iMod ("Hau" with "[$Hlc $Hown]") as "[Hgv2 Hcont]".
      iModIntro.
      iDestruct (saved_offer_lc_agree with "[$] [$offer2] [$Hoffer]") as
        ">(%Heq & Hpeq & H & H1)".
      wp_apply (wp_Mutex__Unlock
        with "[$lock state v slice slice_cap buffer Hpred Hgv2 Hpeq H1 $Hlock]").
      { unfold chan_inv_inner. iExists (@chanphys.Idle V). iFrame. }
      iRewrite -"H" in "Hcont". done.

    + iNamed "phys".
      unfold chan_logical.
      destruct buffer.
      {
        iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
        iNamedSuffix "Hoc" "2".
        unfold chan_cap_valid in *.
        iNamed "Hoffer". iSpecialize ("Hoffer" with "[%]"); first word.
        iDestruct (saved_offer_fractional_invalid with "[$offer2] [$Hoffer]") as "H".
        { done. }
        done.
      }
      {
        iNamed "phys". iNamedSuffix "offer" "2".
        cbn [chan_cap_valid] in *.
        lia.
      }

  - (* chanphys.SndWait *)
    iNamed "phys". wp_auto_lc 5.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndWait v0). iFrame. }
    iRight in "HΦ". iApply "HΦ".

  - (* chanphys.RcvWait - unbuffered channel *)
    (* NOTE: this leaves no freedom for picking the linearization order. *)
    iNamed "phys". wp_auto_lc 2. iNamed "offer".
    (* Two transitions in one atomic step: fire the parked receiver's offer
       arm (Idle -> RcvWait), then our own fast path (RcvWait ->
       SndDone v).  Each arm is handed the invariant's half. *)
    iApply "Hau" in "HP".
    iApply fupd_wp.
    iAssert (£1 ∗ £1)%I with "[$]" as "[Hlc1 Hlc2]".
    iAssert (own_chan γ V (chanstate.Idle))%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iMod ("HP" with "[$Hlc1 $Hown]") as "[Hgv1 Hcont1]".
    iLeft in "HΦ". iLeft in "HΦ".  (* send_fast_path_au *)
    iMod ("HΦ" with "[$Hlc2 $Hgv1]") as "[Hgv1 Hcont]". iModIntro.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer Hgv1 Hcont1 Hpred Hoffer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndDone v).
      (* frame the parked phase-two AU by name: a bare [iFrame] digs into its
         [own_chan] occurrences *)
      iFrame "Hcont1". iFrame. all: try (iPureIntro; done). }
    done.

  - (* chanphys.SndDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndDone v0). iFrame. }
    iRight in "HΦ". done.

  - (* chanphys.RcvDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame. }
    iRight in "HΦ". done.

  - (* chanphys.Closed *)
    destruct buffer.
    {
      iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
      iNamed "Hoc". iLeft in "HΦ". iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Closed []))%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#%". }
      iMod ("HΦ" $! [] with "[$Hlc $Hown]") as "[]".
    }
    {
      iNamed "phys". iDestruct "offer" as "[Hoc %Hoffer]".
      iNamed "Hoc". iLeft in "HΦ". iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Closed (v0 :: buffer)))%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
      iMod ("HΦ" $! (v0 :: buffer) with "[$Hlc $Hown]") as "[]".
    }
Qed.

Local Lemma wp_TrySend_nonblocking_alt ch v γ :
  ∀ Φ,
  is_chan ch γ V -∗
  nonblocking_send_au_alt γ V v (Φ (#true)) (Φ (#false)) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TrySend" #v #false {{ Φ }}.
Proof using W.
  wp_start as "Hunb". iNamed "Hunb". wp_auto.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamedSuffix "Hchan" "_inv".

  (* Case analysis on channel state *)
  destruct s; iNamedSuffix "phys_inv" "_inv".
  - (* chanphys.Buffered channel *)
    iNamedSuffix "offer_inv" "_inv".
    wp_auto_lc 1. unfold chan_cap_valid in *.

    (* TODO: tactics to saturate the context with facts like these? *)
    iDestruct (own_slice_len with "[$]") as "%Hlen".
    iDestruct (own_slice_wf with "[$]") as "%Hwf".
    iDestruct (own_slice_cap_wf with "[$]") as "%Hwf2".

    wp_if_destruct.
    + iApply fupd_wp.
      iRight in "HΦ". iLeft in "HΦ".  (* send_enq_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Buffered buffer))%I
        with "[Hchanrepfrag_inv]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. simpl in *. len. }
      iMod ("HΦ" $! buffer with "[$Hlc $Hown]") as "[Hocnew Hstep]".
      { iPureIntro. simpl in *. len. }
      iNamedSuffix "Hocnew" "_inv". iModIntro.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl [Hsl _]". wp_auto.
      wp_apply (wp_slice_append with "[$slice_inv $Hsl $slice_cap_inv]") as (fr) "(slice_inv & slice_cap_inv & Hsl)".
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.Buffered (buffer ++ [v])). iFrame.
        all: try (iPureIntro; simpl in *; len). }
      done.
    + iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_not_ready_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Buffered buffer))%I
        with "[Hchanrepfrag_inv]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. simpl in *. len. }
      iMod ("HΦ" $! (chanstate.Buffered buffer) with "[$Hlc $Hown]") as "[Hocnew HΦ]".
      { iPureIntro. simpl. intros ?. word. }
      iNamedSuffix "Hocnew" "_inv". iModIntro.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock
        with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.Buffered buffer). iFrame "∗#%". }
      iFrame.
  - (* chanphys.Idle *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.Idle V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
    iMod ("HΦ" $! (@chanstate.Idle V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists chanphys.Idle. iFrame "∗#%". }
    iFrame.
  - (* chanphys.SndWait *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.Idle V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
    iMod ("HΦ" $! (@chanstate.Idle V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.SndWait _). iFrame "∗#%". }
    iFrame.
  - (* chanphys.RcvWait *)
    wp_auto_lc 2. iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iApply "Hau_inv" in "HP_inv".
    iAssert (£1 ∗ £1)%I with "[$]" as "[Hlc1 Hlc2]".
    iAssert (own_chan γ V chanstate.Idle)%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iMod ("HP_inv" with "[$Hlc1 $Hown]") as "[Hocrp Hcont1_inv]". iModIntro.
    iApply fupd_wp. iLeft in "HΦ".  (* send_fast_path_au *)
    iMod ("HΦ" with "[$Hlc2 $Hocrp]") as "[Hocinv Hcont]". iModIntro.
    iNamedSuffix "Hocinv" "_inv".
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.SndDone v). iFrame "∗#".
      all: try (iPureIntro; done). }
    done.
  - (* chanphys.SndDone *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (chanstate.SndDone v0))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
    iMod ("HΦ" $! (chanstate.SndDone v0) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.SndDone _). iFrame "∗#%". }
    iFrame.
  - (* chanphys.RcvDone *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* send_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.RcvDone V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
    iMod ("HΦ" $! (@chanstate.RcvDone V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame "∗#%". }
    iFrame.
  - (* chanphys.Closed *)
    destruct buffer; iNamedSuffix "phys_inv" "_inv".
    + wp_auto_lc 1.
      simpl. iDestruct "offer_inv" as "[Hoc_inv offer_inv]".
      iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* send_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iMod ("HΦ" $! [] with "[$Hlc $Hoc_inv]") as "[]".
    + wp_auto_lc 1.
      simpl. iDestruct "offer_inv" as "Hoc_inv".
      iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* send_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iMod ("HΦ" $! (v0 :: buffer) with "[$Hlc $Hoc_inv]") as "[]".
Qed.

(** The plain nonblocking spec is now a corollary: [nonblocking_send_au] implies
    [nonblocking_send_au_alt], so there is only one spec to prove against the code. *)
Local Lemma wp_TrySend_nonblocking ch v γ :
  ∀ Φ,
  is_chan ch γ V -∗
  nonblocking_send_au γ V v (Φ (#true)) (Φ (#false)) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TrySend" #v #false {{ Φ }}.
Proof using W.
  iIntros (?) "#Hc HΦ".
  iApply (wp_TrySend_nonblocking_alt with "[$Hc]").
  by iApply nonblocking_send_au_to_alt.
Qed.

Lemma wp_TrySend ch v γ (blocking : bool) :
  ∀ Φ,
  is_chan ch γ V -∗
  (if blocking then send_au γ V v (Φ (#true)) ∧ Φ (#false)
   else (nonblocking_send_au γ V v (Φ (#true)) (Φ (#false)) ∨ nonblocking_send_au_alt γ V v (Φ (#true)) (Φ (#false))))
  -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TrySend" #v #blocking {{ Φ }}.
Proof using W.
  iIntros (?) "#? HΦ".
  destruct blocking.
  - wp_apply (wp_TrySend_blocking with "[$] [$]").
  - iDestruct "HΦ" as "[?|?]".
    + wp_apply (wp_TrySend_nonblocking with "[$] [$]").
    + wp_apply (wp_TrySend_nonblocking_alt with "[$] [$]").
Qed.

Lemma wp_Send ch v γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au γ V v (Φ #())) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "Send" #v {{ Φ }}.
Proof using W.
  wp_start as "#Hic". iRename "HΦ" into "Hau".
  iDestruct (is_chan_not_null with "[$Hic]") as "%Hnn".
  wp_auto_lc 4.
  iSpecialize ("Hau" with "[$]").

  wp_if_destruct; first done.
  wp_for. iNamed "Hau".
  wp_apply (wp_TrySend with "[$] [Hau c v]").
  iSplit.
  { iFrame. rewrite /send_au. repeat iSplit.
    - (* send_fast_path_au *)
      iLeft in "Hau". iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      destruct decide; try naive_solver.
      destruct decide; try done. wp_auto. done.
    - (* send_slow_path_au: rewrap the second phase around the loop continuation *)
      iRight in "Hau". iLeft in "Hau".
      iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hau]". iModIntro.
      iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      destruct decide; try naive_solver.
      destruct decide; try done. wp_auto. done.
    - (* send_enq_au *)
      iRight in "Hau". iRight in "Hau". iLeft in "Hau".
      iIntros (buf) "(Hlc & %Hlt & Hoc)".
      iMod ("Hau" $! buf with "[$Hlc $Hoc]") as "[$ H]"; first (iPureIntro; lia).
      iModIntro. wp_auto. destruct decide.
      { wp_auto. wp_for_post. iFrame. naive_solver. }
      destruct decide. { wp_auto. done. } done.
    - (* send_closed_au: unchanged, it does not mention the continuation *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau". iFrame.
  }
  {
    wp_auto.
    rewrite decide_True //.
    wp_auto. wp_for_post. iFrame.
  }
Qed.

(** Demo of a simple-to-understand AU: on a channel that is known to be
    buffered, only the enqueue and closed transitions can arise, so the client
    only has to give those two.  The offer arms are vacuous because
    [own_chan chanphys.Idle] / [own_chan chanphys.RcvWait] force capacity 0. *)
#[local] Lemma wp_BlockingSend ch v γ :
  sint.Z γ.(chan_cap) > 0 →
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_enq_au γ V v (Φ #()) ∧ send_closed_au γ V) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "Send" #v {{ Φ }}.
Proof using W.
  iIntros (Hcapnz Φ) "#Hunb HΦ".
  iApply (wp_Send with "[$Hunb]").
  iIntros "Hlc".
  iSpecialize ("HΦ" with "[$Hlc]").
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au: RcvWait forces capacity 0 *)
    iIntros "[Hlc Hoc]". iDestruct (own_chan_cap_valid with "Hoc") as %Hcv.
    exfalso. simpl in Hcv. lia.
  - (* send_slow_path_au: Idle forces capacity 0 *)
    iIntros "[Hlc Hoc]". iDestruct (own_chan_cap_valid with "Hoc") as %Hcv.
    exfalso. simpl in Hcv. lia.
  - iLeft in "HΦ". iFrame.
  - iRight in "HΦ". iFrame.
Qed.

Local Lemma wp_tryClose ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  close_au γ V (Φ (#true)) ∧ Φ (#false) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "tryClose" #() {{ Φ }}.
Proof using W.
  wp_start as "#Hunb". iNamed "Hunb".
  wp_auto_lc 1.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  destruct s; iNamed "phys".

  { (* chanphys.Buffered: close_buf_au *)
    iNamed "offer".
    iAssert (own_chan γ V (chanstate.Buffered buffer))%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    wp_auto.
    iApply fupd_wp. iLeft in "HΦ". rewrite /close_au.
    iDestruct "HΦ" as "[_ [HΦ _]]". rewrite /close_buf_au.
    iAssert (£1)%I with "[$]" as "Hlc".
    iMod ("HΦ" with "[$Hlc $Hown]") as "[Hgv2 HΦ]".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap Hgv2 $Hlock]").
    { unfold chan_inv_inner.
      iExists (chanphys.Closed buffer). unfold chan_phys.
      destruct buffer.
      { iFrame. iIntros "%Hcap0". exfalso; simpl in *; word. }
      { iFrame. } }
    { iFrame. }
  }

  { (* chanphys.Idle: close_idle_au *)
    iNamed "offer".
    iAssert (own_chan γ V (chanstate.Idle))%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iApply fupd_wp. iLeft in "HΦ". rewrite /close_au.
    iDestruct "HΦ" as "[HΦ _]". rewrite /close_idle_au.
    iAssert (£1)%I with "[$]" as "Hlc".
    iMod ("HΦ" with "[$Hlc $Hown]") as "[Hgv2 HΦ]".
    iModIntro. wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap Hgv2 Hoffer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.Closed []). iFrame. iIntros "Hcap". done. }
    done.
  }

  (* chanphys.SndWait / chanphys.RcvWait / chanphys.SndDone / chanphys.RcvDone: [tryClose] returns false and the
     caller spins; this is why neither slow path's second phase can see a
     closed channel. *)
  { wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndWait v). iFrame. }
    iRight in "HΦ". iFrame. }
  { wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.RcvWait). iFrame. }
    iRight in "HΦ". iFrame. }
  { wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndDone v). iFrame. }
    iRight in "HΦ". iFrame. }
  { wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame. }
    iRight in "HΦ". iFrame. }

  { (* chanphys.Closed: close_closed_au rules this out *)
    iNamed "offer". unfold chan_logical.
    iApply fupd_wp. iLeft in "HΦ". rewrite /close_au.
    iDestruct "HΦ" as "[_ [_ HΦ]]". rewrite /close_closed_au.
    iAssert (£1)%I with "[$]" as "Hlc".
    destruct buffer.
    { iDestruct "offer" as "[offer1 offer2]".
      iMod ("HΦ" $! [] with "[$Hlc offer1]") as "[]".
      iFrame "∗#". all: try (iPureIntro; done). }
    { iDestruct "offer" as "(offer1 & %offer2)".
      iMod ("HΦ" $! (v :: buffer) with "[$Hlc offer1]") as "[]".
      iFrame "∗#". all: try (iPureIntro; unfold chan_cap_valid; done). }
  }
Qed.

Lemma wp_Close ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au γ V (Φ #())) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "Close" #() {{ Φ }}.
Proof using W.
  wp_start as "#Hic". iRename "HΦ" into "Hau".
  iDestruct (is_chan_not_null with "[$Hic]") as "%Hnn".
  wp_auto_lc 4.
  iSpecialize ("Hau" with "[$]").
  wp_if_destruct; first done.
  wp_for.
  wp_apply (wp_tryClose with "[$Hic]").
  iSplit.
  { (* the AU is handed on unchanged; the loop retries if tryClose fails *)
    rewrite /close_au. repeat iSplit.
    - iLeft in "Hau". rewrite /close_idle_au.
      iIntros "[Hlc Hoc]". iMod ("Hau" with "[$Hlc $Hoc]") as "[$ HΦ]". iModIntro.
      wp_auto. destruct decide.
      { wp_auto. wp_for_post. naive_solver. }
      { destruct decide; try done. wp_auto. done. }
    - iRight in "Hau". iLeft in "Hau". rewrite /close_buf_au.
      iIntros (buf) "[Hlc Hoc]". iMod ("Hau" $! buf with "[$Hlc $Hoc]") as "[$ HΦ]". iModIntro.
      wp_auto. destruct decide.
      { wp_auto. wp_for_post. naive_solver. }
      { destruct decide; try done. wp_auto. done. }
    - iRight in "Hau". iRight in "Hau". iFrame. }
  { wp_auto. rewrite decide_True //. wp_auto. wp_for_post. iFrame. }
Qed.

End atomic_specs.
