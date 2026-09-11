Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms Require Export base.

(** * Single Producer Single Consumer (SPSC) Channel Verification

    This file provides a high-level abstraction for single-producer single-consumer
    channels built on top of the low-level channel verification. The SPSC abstraction
    provides stronger guarantees by tracking the history of sent and received values.

    Key features:
    - Producer maintains exclusive send permission with history tracking
    - Consumer maintains exclusive receive permission with history tracking
    - Ghost state tracks sent/received histories with fractional permissions
    - Invariant maintains relationship: sent = received ++ in_flight
    - Support for resource protocols P (per-value) and R (final state)
*)


Section spsc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

(** ** Ghost State Names *)

Record spsc_names := {
  chan_name : chan_names;      (* Underlying channel ghost state *)
  spsc_sent_name : gname;      (* History of sent values *)
  spsc_recv_name : gname       (* History of received values *)
}.


(* Producer and Consumer Predicates *)

(** Producer maintains (1/2) permission of sent history *)
Definition spsc_producer (γ:spsc_names) (sent:list V) : iProp Σ :=
    dghost_var γ.(spsc_sent_name) (DfracOwn (1/2)) sent.

(** Consumer maintains (1/2) permission of received history *)
Definition spsc_consumer (γ:spsc_names) (received:list V) : iProp Σ :=
    dghost_var γ.(spsc_recv_name) (DfracOwn (1/2)) received.

(** ** In-Flight Values *)

(** Values that have been sent but not yet received *)
Definition inflight (s : chanstate.t V) : list V :=
  match s with
  | chanstate.Buffered buff => buff
  | chanstate.SndWait v | chanstate.SndDone v => [v]
  | chanstate.Closed drain => drain
  | _ => []
  end.

(** ** SPSC Channel Invariant *)

(** The main SPSC channel predicate.

    Parameters:
    - P: Resource associated with each value (maintained while in-flight)
    - R: Final resource when channel is closed and drained

    The invariant maintains:
    - sent = received + inflight(channel_state)
    - P holds for all in-flight values
    - When closed, producer permission is parked to prevent further sends
    - When closed and drained, consumer gets R
*)
Definition is_spsc (γ:spsc_names) (ch:loc)
                   (P: Z -> V → iProp Σ) (R: list V → iProp Σ) : iProp Σ :=
    is_chan ch γ.(chan_name) V ∗
    inv nroot (
      ∃ s sent recv,
        "Hch"    ∷ own_chan γ.(chan_name) V s ∗
        "HsentI" ∷ dghost_var γ.(spsc_sent_name) (DfracOwn (1/2)) sent ∗
        "HrecvI" ∷ dghost_var γ.(spsc_recv_name) (DfracOwn (1/2)) recv ∗
        "%Hrel"  ∷ ⌜sent = recv ++ inflight s⌝ ∗
        (match s with
        (* P holds for all buffered values *)
        | chanstate.Buffered buff =>
            [∗ list] i ↦ v ∈ buff, P ((length recv) + i) v
        (* P holds for pending/committed values *)
        | chanstate.SndWait v | chanstate.SndDone v =>
            P (length recv) v
        (* Closed channel: park producer permission, provide R when drained *)
        | chanstate.Closed [] =>
            spsc_producer γ sent ∗ (R sent ∨ spsc_consumer γ sent)
        | chanstate.Closed drain =>
            ([∗ list] i ↦ v ∈ drain, P ((length recv) + i) v) ∗
            spsc_producer γ sent ∗
            (R sent ∨ spsc_consumer γ sent)
        | _ => True
        end)
    )%I.

(** ** Initialization *)

(** Create an SPSC channel from a basic channel *)
Lemma start_spsc ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ) γ:
  is_chan ch γ V -∗
  (own_chan γ V chanstate.Idle) ∨ (own_chan γ V (chanstate.Buffered [])) ={⊤}=∗
  (∃ γspsc, is_spsc γspsc ch P R ∗  spsc_producer γspsc []  ∗  spsc_consumer γspsc []) .
Proof.
  iIntros "#Hch Hoc".

  (* Allocate ghost variables for sent and received histories *)
  iMod (dghost_var_alloc ([] : list V)) as (γsent) "[HsentA HsentF]".
  iMod (dghost_var_alloc ([] : list V)) as (γrecv) "[HrecvA HrecvF]".

  (* Create the spsc_names record *)
  set (γspsc := {| chan_name := γ; spsc_sent_name := γsent; spsc_recv_name := γrecv |}).
  iExists (γspsc).

  (* Allocate the invariant *)
  iMod (inv_alloc nroot _ with "[Hoc HsentA HrecvA]") as "$".
  {
    iDestruct "Hoc" as "[Hoc|Hoc]".
    (* Prove the invariant holds initially *)
  {
    simpl.
    iNext. iExists chanstate.Idle, [], []. iFrame.
    iPureIntro. simpl. done.
    }
    {
       iNext. iExists (chanstate.Buffered []), [], []. iFrame.
       simpl.
       iFrame.
    iPureIntro. simpl. done.
    }
  }

  (* Construct the final result *)
  iModIntro.
  iFrame "#∗".
Qed.

(** ** Receive Operation *)

(* Open the spsc invariant and hand the arm the invariant's half of [own_chan]. *)
Local Ltac sp_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iNamed "Hi".
(* One credit strips the invariant body and the client's continuation together:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Phase two of a two-phase arm uses [sp_open], since
   the continuation was already stripped in phase one. *)
Local Ltac sp_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi Hcont" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi Hcont]";
  iNamed "Hi".
Local Ltac sp_agree := iDestruct (own_chan_agree with "Hch Himpl") as %->; simpl.
Local Ltac sp_step st h :=
  sp_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %h;
  iMod (own_chan_halves_update st with "Hch Himpl") as "[H1 H2]";
  [ simpl in h |- *; lia | ].

(* Reindex the tail of a [P (length recv + i)] list after one value is consumed. *)
Local Ltac sp_reindex l r :=
  rewrite length_app singleton_length;
  iApply (big_sepL_proper _ _ l with "Hrest");
  intros k y z; replace ((length r + 1)%nat + k) with (length r + S k) by lia; done.

Lemma spsc_rcv_au γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                      (received : list V) Φ :
  is_spsc γ ch P R -∗
  spsc_consumer γ received -∗
  (▷ ∀ v (ok:bool),
     (if ok then P (length received) v ∗ spsc_consumer γ (received ++ [v])
            else R received ∗ ⌜ v = (zero_val V) ⌝) -∗
     Φ v ok) -∗
  recv_au γ.(chan_name) V Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hspsc Hcons Hcont".
  unfold is_spsc. iDestruct "Hspsc" as "[Hchan Hinv]".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : SndWait w -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.
    sp_step (@chanstate.RcvDone V) Hcv1.
    iCombine "Hcons HrecvI" as "Hrcv_full".
    iMod (dghost_var_update (recv ++ [w]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
    iMod ("Hclose" with "[H1 HsentI HrecvI_new]") as "_".
    { iNext. iExists chanstate.RcvDone, sent, (recv ++ [w]).
      iFrame "H1 HsentI HrecvI_new".
      iPureIntro. rewrite Hrel. simpl. by rewrite app_nil_r. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "Hi Hcons_new".
  - (* recv_slow_path_au : Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". sp_openc. sp_step (@chanstate.RcvWait V) Hcv2.
    iMod ("Hclose" with "[H1 HsentI HrecvI]") as "_".
    { iNext. iExists chanstate.RcvWait, sent, recv.
      iFrame "H1 HsentI HrecvI". iPureIntro. rewrite Hrel. by simpl. }
    iModIntro. iFrame "H2". try iClear "Hi".
    (* phase two, fired once the sender has committed *)
    iIntros (w) "[Hlc Himpl]". sp_open.
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.
    sp_step (@chanstate.Idle V) Hcv3.
    iCombine "Hcons HrecvI" as "Hrcv_full".
    iMod (dghost_var_update (recv0 ++ [w]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
    iMod ("Hclose" with "[H1 HsentI HrecvI_new]") as "_".
    { iNext. iExists chanstate.Idle, sent0, (recv0 ++ [w]).
      iFrame "H1 HsentI HrecvI_new".
      iPureIntro. rewrite Hrel0. simpl. by rewrite app_nil_r. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "Hi Hcons_new".
  - (* recv_deq_au : take the head off the buffer *)
    iIntros (w rest) "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.
    sp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Buffered rest) with "Hch Himpl") as "[H1 H2]".
    { simpl in Hlen |- *. split; lia. }
    iDestruct "Hi" as "[HPv Hrest]".
    iCombine "Hcons HrecvI" as "Hrcv_full".
    iMod (dghost_var_update (recv ++ [w]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
    iMod ("Hclose" with "[H1 HsentI HrecvI_new Hrest]") as "_".
    { iNext. iExists (chanstate.Buffered rest), sent, (recv ++ [w]).
      iFrame "H1 HsentI HrecvI_new".
      iSplitR "Hrest".
      { iPureIntro. rewrite Hrel. simpl. by rewrite -app_assoc. }
      sp_reindex rest recv. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "Hcons_new".
    replace (length recv + 0%nat) with (Z.of_nat (length recv)) by lia.
    iFrame "HPv".
  - (* recv_drain_au : take the head off a closed channel's drain *)
    iIntros (w rest) "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.
    sp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iDestruct "Hi" as "(Hdrain & Hprod & Hdisj)".
    iCombine "Hcons HrecvI" as "Hrcv_full".
    iMod (dghost_var_update (recv ++ [w]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
    destruct rest as [|r rs].
    + (* last drained value *)
      iMod (own_chan_halves_update (@chanstate.Closed V []) with "Hch Himpl") as "[H1 H2]".
      { simpl in Hlen |- *. lia. }
      iDestruct "Hdrain" as "[HPv _]".
      iMod ("Hclose" with "[H1 HsentI HrecvI_new Hprod Hdisj]") as "_".
      { iNext. iExists (chanstate.Closed []), sent, (recv ++ [w]).
        iFrame "H1 HsentI HrecvI_new Hprod Hdisj".
        iPureIntro. rewrite Hrel. simpl. by rewrite app_nil_r. }
      iModIntro. iFrame "H2". iApply "Hcont". iFrame "Hcons_new".
      replace (length recv + 0%nat) with (Z.of_nat (length recv)) by lia.
      iFrame "HPv".
    + iMod (own_chan_halves_update (chanstate.Closed (r :: rs)) with "Hch Himpl")
        as "[H1 H2]".
      { simpl in Hlen |- *. split; lia. }
      iDestruct "Hdrain" as "[HPv Hrest]".
      iMod ("Hclose" with "[H1 HsentI HrecvI_new Hrest Hprod Hdisj]") as "_".
      { iNext. iExists (chanstate.Closed (r :: rs)), sent, (recv ++ [w]).
        iFrame "H1 HsentI HrecvI_new".
        iSplitR "Hrest Hprod Hdisj".
        { iPureIntro. rewrite Hrel. simpl. by rewrite -app_assoc. }
        iFrame "Hprod Hdisj". sp_reindex (r :: rs) recv. }
      iModIntro. iFrame "H2". iApply "Hcont". iFrame "Hcons_new".
      replace (length recv + 0%nat) with (Z.of_nat (length recv)) by lia.
      iFrame "HPv".
  - (* recv_closed_au : drained and closed, so hand back R *)
    iIntros "[Hlc Himpl]". sp_openc. sp_agree.
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.
    iDestruct "Hi" as "(Hprod & [HR | Hcons2])".
    + iMod ("Hclose" with "[Hch HsentI HrecvI Hprod Hcons]") as "_".
      { iNext. iExists (chanstate.Closed []), sent, recv.
        iFrame "Hch HsentI HrecvI Hprod".
        iSplitR; [ iPureIntro; done | ].
        iRight. unfold spsc_consumer. rewrite Hrel. simpl.
        rewrite app_nil_r. iFrame "Hcons". }
      iModIntro. iFrame "Himpl". iApply "Hcont".
      rewrite Hrel. simpl. rewrite app_nil_r. iFrame "HR". done.
    + (* the invariant already holds the consumer half, so ours is one too many *)
      iExFalso. unfold spsc_consumer.
      iCombine "Hcons HrecvI" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hcons2") as "[%Hvalid _]". done.
Qed.

(** SPSC receive operation with history tracking *)
Lemma wp_spsc_receive γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                      (received : list V) :
  {{{ is_spsc γ ch P R ∗ spsc_consumer γ received }}}
    chan.receive t #ch
  {{{ (v:V) (ok:bool), RET (#v, #ok);
      (if ok then P (length received) v ∗ spsc_consumer γ (received ++ [v])
            else R received ∗ ⌜ v = (zero_val V) ⌝ )%I }}}.
Proof using All.
  iIntros (Φ) "(#Hspsc & Hcons) Hcont".

  (* Extract channel info from SPSC predicate *)
  iPoseProof "Hspsc" as "[#Hch _]".
  wp_apply (chan.wp_receive with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & _ & _)".
  iApply (spsc_rcv_au with "[$Hspsc] [$Hcons]").
  iNext. iFrame.
Qed.

(** ** Send Operation *)

Lemma spsc_send_au γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                   (sent : list V) (v : V) Φ :
  is_spsc γ ch P R -∗
  spsc_producer γ sent ∗ P (length sent) v -∗
  ▷ (spsc_producer γ (sent ++ [v]) -∗ Φ) -∗
  send_au γ.(chan_name) V v Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hspsc [Hprod HP] Hcont".
  iDestruct "Hspsc" as "[Hchan Hinv]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hprod HsentI") as %->.
    sp_step (chanstate.SndDone v) Hcv1.
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".
    iMod ("Hclose" with "[H1 HsentI_new HrecvI HP]") as "_".
    { iNext. iExists (chanstate.SndDone v), (sent0 ++ [v]), recv.
      iFrame "H1 HsentI_new HrecvI".
      unfold inflight in Hrel. rewrite app_nil_r in Hrel. subst sent0.
      iFrame "HP". iPureIntro. done. }
    iModIntro. iFrame "H2". iApply "Hcont". unfold spsc_producer. iFrame "Hprod_new".
  - (* send_slow_path_au : Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hprod HsentI") as %->.
    sp_step (chanstate.SndWait v) Hcv2.
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".
    iMod ("Hclose" with "[H1 HsentI_new HrecvI HP]") as "_".
    { iNext. iExists (chanstate.SndWait v), (sent0 ++ [v]), recv.
      iFrame "H1 HsentI_new HrecvI".
      unfold inflight in Hrel. rewrite app_nil_r in Hrel. subst sent0.
      iFrame "HP". iPureIntro. done. }
    iModIntro. iFrame "H2". try iClear "Hi".
    (* phase two, fired once the receiver has committed *)
    iIntros "[Hlc Himpl]". sp_open.
    iDestruct (dghost_var_agree with "Hprod_new HsentI") as %->.
    sp_step (@chanstate.Idle V) Hcv3.
    iMod ("Hclose" with "[H1 HsentI HrecvI]") as "_".
    { iNext. iExists chanstate.Idle, sent, recv0.
      iFrame "H1 HsentI HrecvI". iPureIntro. rewrite Hrel0. by simpl. }
    iModIntro. iFrame "H2". iApply "Hcont". unfold spsc_producer. iFrame "Hprod_new".
  - (* send_enq_au : the implementation has already checked there is room *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". sp_openc.
    iDestruct (dghost_var_agree with "Hprod HsentI") as %->.
    sp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v]))
           with "Hch Himpl") as "[H1 H2]".
    { simpl. rewrite length_app /=. lia. }
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".
    iMod ("Hclose" with "[H1 HsentI_new HrecvI Hi HP]") as "_".
    { iNext. iExists (chanstate.Buffered (buf ++ [v])), (sent0 ++ [v]), recv.
      iFrame "H1 HsentI_new HrecvI".
      iSplitR.
      { iPureIntro. rewrite Hrel. simpl. by rewrite app_assoc. }
      rewrite big_sepL_app. iFrame "Hi". simpl.
      subst sent0. cbn [inflight]. rewrite length_app.
      replace (Z.of_nat (length recv + length buf))
         with (Z.of_nat (length recv) + Z.of_nat (length buf + 0)) by lia.
      iFrame "HP". }
    iModIntro. iFrame "H2". iApply "Hcont". unfold spsc_producer. iFrame "Hprod_new".
  - (* send_closed_au : at Closed the invariant holds the producer half too *)
    iIntros (drain) "[Hlc Himpl]". sp_openc. sp_agree.
    unfold spsc_producer.
    destruct drain as [|d ds].
    + iDestruct "Hi" as "(Hd & _)".
      iCombine "HsentI Hd" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.
    + iDestruct "Hi" as "(_ & Hd & _)".
      iCombine "HsentI Hd" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.
Qed.

(** SPSC send operation with history tracking *)
Lemma wp_spsc_send γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                   (sent : list V) (v : V) :
  {{{ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ P (length sent) v }}}
    chan.send t #ch #v
  {{{ RET #(); spsc_producer γ (sent ++ [v]) }}}.
Proof using All.
  iIntros (Φ) "(#Hspsc & Hprod & HP) Hcont".

  (* Extract channel info from SPSC predicate *)
  unfold is_spsc.
  iPoseProof "Hspsc" as "[Hchan _]".

  (* Use wp_Send with our atomic update *)
  wp_apply (chan.wp_send ch v γ.(chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".

  iApply (spsc_send_au with "[$Hspsc] [$Hprod $HP]").
  done.
Qed.

(** ** Close Operation *)

(* Close only has to consider Idle and Buffered: [tryClose] spins on every
   pending/committed state, so those are unreachable here. *)
Lemma spsc_close_au γ ch P R sent Φ :
  is_spsc γ ch P R -∗
  spsc_producer γ sent ∗ R sent -∗
  ▷ Φ -∗
  close_au γ.(chan_name) V Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hspsc [Hprod HP] Hcont".
  iDestruct "Hspsc" as "[Hchan #Hinv]".
  rewrite /close_au. repeat iSplit.
  - (* close_idle_au : Idle -> Closed [] *)
    iIntros "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hprod HsentI") as %->.
    sp_step (@chanstate.Closed V []) Hcv1.
    iMod ("Hclose" with "[H1 HsentI HrecvI Hprod HP]") as "_".
    { iNext. iExists (chanstate.Closed []), sent0, recv.
      iFrame "H1 HsentI HrecvI".
      iSplitR; [ iPureIntro; rewrite Hrel; by cbn [inflight] | ].
      unfold spsc_producer. iFrame "Hprod". iLeft. iFrame "HP". }
    iModIntro. iFrame "H2 Hcont".
  - (* close_buf_au : the buffered values become the drain *)
    iIntros (buf) "[Hlc Himpl]". sp_openc.
    iDestruct (dghost_var_agree with "Hprod HsentI") as %->.
    sp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    destruct buf as [|d ds].
    + iMod (own_chan_halves_update (@chanstate.Closed V []) with "Hch Himpl")
        as "[H1 H2]".
      { simpl in Hlen |- *. lia. }
      iMod ("Hclose" with "[H1 HsentI HrecvI Hprod HP]") as "_".
      { iNext. iExists (chanstate.Closed []), sent0, recv.
        iFrame "H1 HsentI HrecvI".
        iSplitR; [ iPureIntro; rewrite Hrel; by cbn [inflight] | ].
        unfold spsc_producer. iFrame "Hprod". iLeft. iFrame "HP". }
      iModIntro. iFrame "H2 Hcont".
    + iMod (own_chan_halves_update (chanstate.Closed (d :: ds)) with "Hch Himpl")
        as "[H1 H2]".
      { simpl in Hlen |- *. split; lia. }
      iMod ("Hclose" with "[H1 HsentI HrecvI Hi Hprod HP]") as "_".
      { iNext. iExists (chanstate.Closed (d :: ds)), sent0, recv.
        iFrame "H1 HsentI HrecvI".
        iSplitR; [ iPureIntro; rewrite Hrel; by cbn [inflight] | ].
        iFrame "Hi". unfold spsc_producer. iFrame "Hprod". iLeft. iFrame "HP". }
      iModIntro. iFrame "H2 Hcont".
  - (* close_closed_au : at Closed the invariant already holds the producer half *)
    iIntros (drain) "[Hlc Himpl]". sp_openc. sp_agree.
    unfold spsc_producer.
    destruct drain as [|d ds].
    + iDestruct "Hi" as "(Hgv1 & _)".
      iCombine "Hgv1 HsentI" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.
    + iDestruct "Hi" as "(_ & Hgv2 & _)".
      iCombine "Hgv2 HsentI" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.
Qed.

(** SPSC close operation *)
Lemma wp_spsc_close γ ch P R sent `[ct ↓u go.ChannelType dir t] :
  {{{  is_spsc γ ch P R ∗ spsc_producer γ sent ∗ R sent }}}
    #(functions go.close [ct]) #ch
  {{{ RET #(); True }}}.
Proof using All.
  iIntros (Φ) "( #Hspsc & Hprod & HP) Hcont".
  iPoseProof "Hspsc" as "[Hchan _]".
  iApply (chan.wp_close with "Hchan").
  iIntros "_".
  iApply (spsc_close_au with "[$Hspsc] [$Hprod $HP]").
  iModIntro.
  by iApply "Hcont".
Qed.

End spsc.
