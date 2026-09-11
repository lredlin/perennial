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

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

Collection W := sem_fn + pre_sem + sem + IntoValTyped0.

Local Lemma wp_TryReceive_blocking ch γ :
  ∀ Φ ,
  is_chan ch γ V -∗
  recv_au γ V (λ v ok, Φ (#true, #v, #ok)%V) ∧ Φ (#false, #(zero_val V), #true)%V -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TryReceive" #true {{ Φ }}.
Proof using W.
  wp_start as "Hch". iNamed "Hch".
  wp_auto_lc 9.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  (* Case analysis on channel state *)
  destruct s.
  - (* chanphys.Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      destruct buffer as [|v rest].
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        rewrite length_nil in Hl.
        replace (sint.Z slice_val.(slice.len))with (0) in * by word.
        word.
      }
      iLeft in "HΦ". iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* recv_deq_au *)
      iAssert (own_chan γ V (chanstate.Buffered (v :: rest)))%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iApply fupd_wp.
      iAssert (£1)%I with "[$]" as "Hlc".
      iMod ("HΦ" $! v rest with "[$Hlc $Hown]") as "[Hown2 Hcont]".
      iModIntro.
      have Hpos : 0 ≤ sint.Z (W64 0) by word.
      have Hlookup0 : (v :: rest) !! 0%nat = Some v by done.
      iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
      { exact Hpos. }
      { done. }
      iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::buffer)] *)
      iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
      assert (0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len)) as Hlt.
      { word. }
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index
                 with "[Hclose]"). all: try word.
      { iFrame. done. }
      iIntros "Hsl". wp_auto.
      iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
      rewrite -> decide_True; last word. wp_auto.
      wp_apply (wp_Mutex__Unlock
                 with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
      { unfold chan_inv_inner. iExists (chanphys.Buffered rest). iFrame.

        change (sint.Z (W64 0)) with 0 in *.
        (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
        simpl.
        iDestruct (own_slice_split_all (W64 1) with "Hsl")
          as "[Hhd Htail]"; first word. simpl.
        iFrame.
        iDestruct (own_slice_len with "Hhd") as %[Hlent _].
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
        iDestruct (own_slice_cap_slice (V:=V) slice_val (W64 1) (DfracOwn 1)) as "H".
        { word. }
        iApply "H" in "slice_cap". iFrame.
      }
      done.
    }
    {
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      assert (sint.Z slice_val.(slice.len) = sint.Z (W64 0)) as Heq.
      {
        word.
      }
      assert (buffer = []).
      { destruct buffer. { done. } { rewrite Heq in Hl. naive_solver. } }
      subst buffer.

      wp_apply (wp_Mutex__Unlock
                 with "[$lock state buffer slice slice_cap Hchanrepfrag $Hlock]").
      { iFrame. unfold chan_inv_inner. iFrame.  iExists (chanphys.Buffered []).
        iFrame. iPureIntro. done. }
      iRight in "HΦ". iFrame.
    }
  - iNamed "phys". wp_auto_lc 5.
    iNamed "offer".
    iDestruct (offer_idle_to_recv with "Hoffer") as ">[offer1 offer2]".
    iMod ((saved_prop.saved_pred_update (uncurry (λ (v0 : V) (ok : bool), Φ (# true, # v0, # ok)%V)
          )) with "Hpred") as "[Hpred1 Hpred2]".
    wp_apply (wp_Mutex__Unlock
               with "[$lock state v slice slice_cap buffer  offer1 Hpred1 Hchanrepfrag HΦ $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.RcvWait).
      (* Frame the invariant's own half explicitly: [own_chan] is transparent
         here, so a bare [iFrame] would push it into the parked AU's own
         [own_chan chanphys.Idle]. *)
      iFrame "offer1 HΦ state v slice slice_cap buffer Hpred1".
      iSplitR "Hchanrepfrag".
      { (* park exactly the conjunct this offer will be fired with *)
        iIntros "H". iLeft in "H". iRight in "H". iLeft in "H". iFrame. }
      iFrame "∗#%". }
    wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys". iNamed "offer".
    destruct s.
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      cbn [chan_cap_valid] in *.
      lia.
    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iApply (saved_offer_half_full_invalid with "offer2 Hoffer").

    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (saved_offer_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      congruence.

    }
    {
      unfold chan_phys. iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iDestruct (saved_offer_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      iMod ((saved_prop.saved_pred_update_halves (uncurry Φr0)
            ) with "Hpred2 Hpred") as "[Hpred1 Hpred2]".
      iCombine "Hpred1 Hpred2" as "Hp".
      wp_apply (wp_Mutex__Unlock
                 with "[$lock state v slice slice_cap buffer Hchanrepfrag   Hp  H1   $Hlock]").
      { unfold chan_inv_inner. iExists (@chanphys.Idle V). iFrame. done. }
      iRewrite -"Hpeq" in "HP".
      iRight in "HP". iFrame.
    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".

      iApply fupd_wp.
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.SndDone v0))%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#". iPureIntro. cbn [chan_cap_valid]. done. }
      iMod ("Hau" $! v0 with "[$Hlc $Hown]") as "[Hgv2 Hcont]".
      iModIntro.
      iDestruct (saved_prop.saved_pred_agree γ.(offer_parked_pred_name)
                                                 (DfracOwn (1/2)) (DfracOwn (1/2))
                                                 (uncurry (λ (v1 : V) (ok : bool), Φ (# true, # v1, # ok)%V))
                                                 (uncurry Φr0)
                                                 (v0, true)
                  with "[$Hpred2] [$Hpred]") as "#Hagree".
      iCombine "Hpred2 Hpred" as "offer". rewrite dfrac_op_own Qp.half_half.
      iDestruct (saved_offer_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      wp_apply (wp_Mutex__Unlock
                 with "[$lock state v slice slice_cap buffer H1   Hgv2 offer   $Hlock]").
      { unfold chan_inv_inner. iExists (@chanphys.Idle V). iFrame.
      }
      unfold uncurry.
      iRewrite -"Hagree" in "Hcont". done.
    }
    {
      iNamed "phys". wp_auto.
      iNamed "offer".
      iExFalso.
      iDestruct (saved_offer_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      discriminate Heq.

    }
    {
      iNamed "phys". unfold chan_phys.
      destruct buffer.
      {
        iNamed "phys". wp_auto.

        iNamed "offer". unfold chan_logical. iDestruct "offer" as "[Ho Hoffer]".
        iNamed "Hoffer". unfold chan_cap_valid in Hcapvalid.
        iExFalso.
        iSpecialize ("Hoffer" with "[%]"); first word.
        iDestruct (saved_offer_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
        discriminate Heq.
      }
      {
        iNamed "phys". wp_auto.
        iNamed "offer".
        iExFalso.

        unfold chan_cap_valid in *. lia.
      }
    }
  - (* chanphys.Idle unbuffered channel  *)
    iNamed "phys". wp_auto.
    iNamed "offer".
    (* Two transitions in one atomic step: fire the parked sender's offer arm
       (chanphys.Idle -> chanphys.SndWait v), then our own fast path (chanphys.SndWait v ->
       chanphys.RcvDone). *)
    iApply "Hau" in "HP".
    iApply fupd_wp. iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (chanstate.Idle))%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iMod ("HP" with "[$Hlc $Hown]") as "[Hgv1 Hcont1]". iModIntro.
    iApply fupd_wp. iLeft in "HΦ". iLeft in "HΦ".  (* recv_fast_path_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iMod ("HΦ" $! v with "[$Hlc $Hgv1]") as "[Hgv1 Hcont]". iModIntro.
    wp_apply (wp_Mutex__Unlock
               with "[$lock state v slice slice_cap buffer Hgv1 Hpred Hoffer Hcont1 $Hlock]").
    { unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame "∗#".
      all: try (iPureIntro; done). }
    done.
  - iNamed "phys". wp_auto.

    wp_apply (wp_Mutex__Unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists chanphys.RcvWait. iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto.

    wp_apply (wp_Mutex__Unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists (chanphys.SndDone v). iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto.

    wp_apply (wp_Mutex__Unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys".
    destruct buffer.
    { iNamed "offer".
      unfold chan_logical.
      iNamed "phys".
      wp_auto_lc 2.
      iApply fupd_wp. iLeft in "HΦ".
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      unfold chan_logical. iDestruct "offer" as "[offer H]".
      iMod ("HΦ" with "[$Hlc $offer]") as "[offer Hcont]". iModIntro.
      wp_if_destruct.
      {
        iDestruct (own_slice_len with "slice") as "[%H1 %H2]".
        simpl in H1.
        word.
      }

      wp_apply (wp_Mutex__Unlock
                 with "[$lock state  slice slice_cap buffer offer H $Hlock]").
      { unfold chan_inv_inner.  iExists (chanphys.Closed []). iFrame.
      }
      done.
    }
    {
      iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
      wp_if_destruct.
      {
        iLeft in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".
        (* recv_drain_au *)
        iAssert (own_chan γ V (chanstate.Closed (v :: buffer)))%I
          with "[Hchanrepfrag]" as "Hown".
        { iFrame. iPureIntro. done. }
        iApply fupd_wp.
        iAssert (£1)%I with "[$]" as "Hlc".
        iMod ("HΦ" $! v buffer with "[$Hlc $Hown]") as "[Hown2 Hcont]".
        iModIntro.
        have Hpos : 0 ≤ sint.Z (W64 0) by word.
        have Hlookup0 : (v :: buffer) !! 0%nat = Some v by done.
        iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
        { exact Hpos. }
        { done. }
        iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::buffer)] *)
        iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
        have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len).
        { move: Hlen_eq; simpl.  (* length (v::buffer) = S (length buffer) *)
          (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
          word. }
        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[Hclose]"). all: try word.
        { iFrame. done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        rewrite -> decide_True; last word. wp_auto.
        wp_apply (wp_Mutex__Unlock
                   with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
        { unfold chan_inv_inner. iExists (chanphys.Closed buffer). iFrame.

          have -> : sint.nat (W64 0) = 0%nat by word.
          (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
          simpl.
          iDestruct (own_slice_split_all (W64 1) with "Hsl")
            as "[Hhd Htail]"; first word. simpl.
          iFrame.
          iDestruct (own_slice_len with "Hhd") as %[Hlent _].
          iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
          iDestruct (own_slice_cap_slice (V:=V) slice_val (W64 1) (DfracOwn 1)) as "H".
          { word. }
          iApply "H" in "slice_cap". iFrame.
          destruct buffer.
          { iFrame "∗#". iIntros "%Hzero". word. }
          { iFrame. }
        }
        done.
      }
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        assert (sint.Z slice_val.(slice.len) = sint.Z (W64 0)).
        {
          word.
        }
        replace (sint.nat slice_val.(slice.len)) with 0%nat in *.
        { done.  }
        word.
      }
    }
Qed.

Local Lemma wp_TryReceive_nonblocking_alt ch γ :
  ∀ Φ ,
  is_chan ch γ V -∗
  nonblocking_recv_au_alt γ V (λ v ok, Φ (#true, #v, #ok)%V) (Φ (#false, #(zero_val V), #true)%V) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TryReceive" #false {{ Φ }}.
Proof using W.
  wp_start as "#Hch". iNamed "Hch".
  wp_auto_lc 9.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamedSuffix "Hchan" "_inv".

  (* Case analysis on channel state *)
  destruct s; iNamedSuffix "phys_inv" "_inv".
  - (* chanphys.Buffered channel *)
    iNamedSuffix "offer_inv" "_inv". wp_auto.
    iDestruct (own_slice_len with "slice_inv") as %Hlen.
    iDestruct (own_slice_cap_wf with "slice_cap_inv") as %Hwf.
    wp_if_destruct.
    + destruct buffer as [|v rest].
      { simpl in *. word. }
      iApply fupd_wp.
      iRight in "HΦ". iLeft in "HΦ".  (* recv_deq_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (chanstate.Buffered (v :: rest)))%I
        with "[Hchanrepfrag_inv]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *. word. }
      iMod ("HΦ" $! v rest with "[$Hlc $Hown]") as "[Hocnew Hcont]".
      iNamedSuffix "Hocnew" "_inv". iModIntro.
      iDestruct (own_slice_elem_acc 0 with "slice_inv") as "[Hcell slice_inv]"; [done..|].
      rewrite -> decide_True; last word. wp_auto.
      iSpecialize ("slice_inv" $! v with "Hcell").
      rewrite -> decide_True; last word. wp_auto.
      rewrite list_insert_id //.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock
                 with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.Buffered rest). iFrame "buffer_inv".
        iFrame.
        iDestruct (own_slice_split_all (W64 1) with "slice_inv")
          as "[Hhd $]"; first word.
        iDestruct (own_slice_cap_slice with "slice_cap_inv") as "$".
        all: try (iPureIntro; simpl in *; try done; try len; try word).
        all: try word.
      }
      done.
    + assert (buffer = []).
      { destruct buffer; [done | simpl in *; word]. }
      subst buffer.

      iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_not_ready_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      iAssert (own_chan γ V (@chanstate.Buffered V []))%I with "[Hchanrepfrag_inv]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *.
        try done; try word; try len. }
      iMod ("HΦ" $! (@chanstate.Buffered V []) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
      iNamedSuffix "Hocnew" "_inv". iModIntro.

      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock
                 with "[$lock $Hlock Hi]").
      { iNamed "Hi". iFrame. unfold chan_inv_inner. iFrame.  iExists (chanphys.Buffered []).
        iFrame. iPureIntro. done. }
      iFrame.
  - wp_auto_lc 2.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.Idle V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *.
      try done; try word; try len. }
    iMod ("HΦ" $! (@chanstate.Idle V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.

    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (@chanphys.Idle V).
      iFrame. iPureIntro. done. }
    iFrame.
  - (* chanphys.SndWait *)
    wp_auto_lc 2. iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iApply "Hau_inv" in "HP_inv". iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V chanstate.Idle)%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iMod ("HP_inv" with "[$Hlc $Hown]") as "[Hocsp Hcont1_inv]". iModIntro.
    iApply fupd_wp. iLeft in "HΦ".  (* recv_fast_path_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iMod ("HΦ" $! v with "[$Hlc $Hocsp]") as "[Hocinv Hcont]". iModIntro.
    iNamedSuffix "Hocinv" "_inv".
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists chanphys.RcvDone. iFrame "∗#".
      all: try (iPureIntro; done). }
    done.
  - wp_auto_lc 2.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.Idle V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *.
      try done; try word; try len. }
    iMod ("HΦ" $! (@chanstate.Idle V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". iFrame. unfold chan_inv_inner. iFrame. iExists chanphys.RcvWait.
      iFrame. iPureIntro. done. }
    iFrame.
  - wp_auto_lc 2.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (chanstate.SndDone v))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *.
      try done; try word; try len. }
    iMod ("HΦ" $! (chanstate.SndDone v) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". iFrame. unfold chan_inv_inner. iFrame. iExists (chanphys.SndDone _).
      iFrame. iPureIntro. done. }
    iFrame.
  - wp_auto_lc 2.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp.
    iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iRight in "HΦ".  (* recv_not_ready_au *)
    iAssert (£1)%I with "[$]" as "Hlc".
    iAssert (own_chan γ V (@chanstate.RcvDone V))%I with "[Hchanrepfrag_inv]" as "Hown".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid in *. simpl in *.
      try done; try word; try len. }
    iMod ("HΦ" $! (@chanstate.RcvDone V) with "[$Hlc $Hown]") as "[Hocnew HΦ]"; first (iPureIntro; simpl; done).
    iNamedSuffix "Hocnew" "_inv". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". iFrame. unfold chan_inv_inner. iFrame. iExists chanphys.RcvDone.
      iFrame. iPureIntro. done. }
    iFrame.
  - destruct buffer; iNamedSuffix "phys_inv" "_inv".
    + simpl in *. iDestruct "offer_inv" as "[Hoc_inv Hoffer_inv]".
      wp_auto_lc 2.
      iDestruct (own_slice_len with "slice_inv") as %Hlen.
      wp_if_destruct.
      { simpl in *. word. }
      iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* recv_closed_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      unfold chan_logical.
      iMod ("HΦ" with "[$Hlc $Hoc_inv]") as "[Hoc_inv Hcont]". iModIntro.

      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.Closed []). iFrame. }
      iFrame.
    + wp_auto_lc 2.
      iDestruct (own_slice_len with "slice_inv") as %Hlen.
      iDestruct (own_slice_cap_wf with "slice_cap_inv") as %cap.
      wp_if_destruct.
      2:{ simpl in *. word. }
      iApply fupd_wp.
      iRight in "HΦ". iRight in "HΦ". iLeft in "HΦ".  (* recv_drain_au *)
      iAssert (£1)%I with "[$]" as "Hlc".
      simpl. iDestruct "offer_inv" as "Hoc_inv".
      iDestruct (own_chan_cap_valid with "Hoc_inv") as %Hcv.
      iMod ("HΦ" $! v buffer with "[$Hlc $Hoc_inv]") as "[Hoc_inv Hcont]".
      iModIntro.
      rewrite -> decide_True; last word.
      iDestruct (own_slice_elem_acc 0 with "slice_inv") as "[Hcell slice_inv]"; [done..|].
      wp_auto.
      iSpecialize ("slice_inv" $! v with "Hcell").
      rewrite list_insert_id //.
      rewrite -> decide_True; last word. wp_auto.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (chanphys.Closed buffer). iFrame.
        destruct buffer; iFrame "buffer_inv"; iFrame.
        - iDestruct (own_slice_split_all (W64 1) with "slice_inv") as "[_ slice_inv]".
          { word. }
          rewrite drop_ge; last by len.
          iFrame.
          iDestruct (own_slice_cap_slice with "slice_cap_inv") as "$".
          { word. }
          iFrame. iIntros "%". simpl in *. word.
        - iDestruct (own_slice_split_all (W64 1) with "slice_inv") as "[_ slice_inv]".
          { word. }
          rewrite skipn_cons. iFrame.
          iDestruct (own_slice_cap_slice with "slice_cap_inv") as "$".
          word.
      }
      done.
Qed.

(** As on the send side, the plain nonblocking spec is a corollary of the
    [Alt] one. *)
Local Lemma wp_TryReceive_nonblocking ch γ :
  ∀ Φ ,
  is_chan ch γ V -∗
  nonblocking_recv_au γ V (λ v ok, Φ (#true, #v, #ok)%V) (Φ (#false, #(zero_val V), #true)%V) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TryReceive" #false {{ Φ }}.
Proof using W.
  iIntros (?) "#Hc HΦ".
  iApply (wp_TryReceive_nonblocking_alt with "[$Hc]").
  by iApply nonblocking_recv_au_to_alt.
Qed.

Lemma wp_TryReceive ch γ (blocking : bool) :
  ∀ (Φ : val → iProp Σ),
  is_chan ch γ V -∗
  (if blocking then recv_au γ V (λ v ok, Φ (#true, #v, #ok)%V) ∧
                    Φ (#false, #(zero_val V), #true)%V
   else (nonblocking_recv_au γ V
           (λ v ok, Φ (#true, #v, #ok)%V)
           (Φ (#false, #(zero_val V), #true)%V)
           ∨ nonblocking_recv_au_alt γ V
               (λ v ok, Φ (#true, #v, #ok)%V)
               (Φ (#false, #(zero_val V), #true)%V)
  )) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "TryReceive" #blocking {{ Φ }}.
Proof using W.
  iIntros (?) "#? HΦ".
  destruct blocking.
  - wp_apply (wp_TryReceive_blocking with "[$] [$]").
  - iDestruct "HΦ" as "[?|?]".
    + wp_apply (wp_TryReceive_nonblocking with "[$] [$]").
    + wp_apply (wp_TryReceive_nonblocking_alt with "[$] [$]").
Qed.

Lemma wp_Receive ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ recv_au γ V (λ v ok, Φ (#v, #ok)%V)) -∗
  WP ch @! (go.PointerType (channel.Channel t)) @! "Receive" #() {{ Φ }}.
Proof using W.
  wp_start as "#Hic". iRename "HΦ" into "Hau".
  iDestruct (is_chan_not_null with "[$Hic]") as "%Hnn".
  wp_auto_lc 4.
  iSpecialize ("Hau" with "[$]").

  wp_if_destruct; first done.
  wp_for. iNamed "Hau".
  wp_apply (wp_TryReceive ch γ with "[$]").
  iSplit.
  { iFrame. rewrite /recv_au. repeat iSplit.
    - (* recv_fast_path_au *)
      iLeft in "Hau". iIntros (w) "[Hlc Hoc]".
      iMod ("Hau" $! w with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      wp_for_post. done.
    - (* recv_slow_path_au: rewrap the second phase around the loop continuation *)
      iRight in "Hau". iLeft in "Hau".
      iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hau]". iModIntro.
      iIntros (w) "[Hlc Hoc]".
      iMod ("Hau" $! w with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      wp_for_post. done.
    - (* recv_deq_au *)
      iRight in "Hau". iRight in "Hau". iLeft in "Hau".
      iIntros (w rest) "[Hlc Hoc]".
      iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      wp_for_post. iFrame.
    - (* recv_drain_au *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau". iLeft in "Hau".
      iIntros (w rest) "[Hlc Hoc]".
      iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      wp_for_post. done.
    - (* recv_closed_au *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau". iRight in "Hau".
      iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ H]". iModIntro. wp_auto.
      wp_for_post. done.
  }
  wp_auto. wp_for_post. iFrame.
Qed.

End atomic_specs.
