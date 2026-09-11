From New.proof Require Export proof_prelude.
From New.proof Require Import sync errors.
From New.golang.theory Require Import chan lock.
From New.generatedproof.github_com.mit_pdos.perennial.goose.testdata.examples.channel
  Require Import unbounded.
From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel
  Require Import unbounded_au.
From New.golang Require Import theory.
Import New.code.github_com.mit_pdos.perennial.goose.testdata.examples.channel.unbounded.

Set Default Proof Using "Type".

Section unbounded_impl.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : unbounded.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(* As with the other channel examples here, nothing in this development verifies
   [unbounded]'s package initialization, so [is_pkg_init] carries no content.
   The one package-level variable this proof needs to know about,
   [errBufferClosed], is instead an explicit precondition ([errBufferClosed_init]
   below), so that the obligation stays visible rather than hiding inside
   [is_pkg_init]. *)
#[global] Instance : IsPkgInit (iProp Σ) unbounded := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) unbounded := build_get_is_pkg_init_wf.

(* [unbounded.go]'s [var errBufferClosed = errors.New(...)] holds [err]. *)
Definition is_BufferClosed (err : interface.t_ok) : iProp Σ :=
  "#HBc" ∷ (global_addr unbounded.errBufferClosed) ↦□ (interface.ok err).

(** [mr]'s one package-level variable, initialized.

    [Unbounded.Put] reads [errBufferClosed] to return it, so its spec needs
    to know the global holds a value; the identity of the error is never
    used, so the witness stays existential.

    This is a precondition rather than a component of [is_pkg_init unbounded]
    because nothing in this development verifies package initialization -
    all four [IsPkgInit] instances in init.v are [True]. Folding the fact
    into [is_pkg_init unbounded] would have made it a silent global assumption and
    broken every site that discharged the old [True] with [done]. Stating
    it here keeps it local and auditable: whoever verifies [mr]'s init
    against the framework's [wp_initialize'] machinery discharges it, and
    until then it is visibly owed. It replaces an [Admitted]
    [wp_load_errBufferClosed] whose precondition was [True] - a form that
    was not merely unproved but unprovable, since owning nothing about the
    address cannot show the load does not get stuck. *)
Definition errBufferClosed_init : iProp Σ :=
  ∃ err : interface.t_ok, is_BufferClosed err.

Global Instance errBufferClosed_init_pers : Persistent errBufferClosed_init.
Proof. apply _. Qed.

Notation V := interface.t.

Record Ub_names := {
  ubn_chan : chan_names;  (* ghost names for the raw [c chan any] *)
  ubn_ub : gname;         (* the abstract [ubstate.t] from [unbounded.v] *)
  ubn_bl : gname;         (* ghost mirror of [backlog], split 1/2 / 1/2 *)
  ubn_cl : gname;         (* ghost mirror of [closing], split 1/2 / 1/2 *)
  ubn_clsd : gname;       (* ghost mirror of [closed], split 1/2 / 1/2 *)
}.

Definition ubstate_of (closing : bool) (cs : chanstate.t V) (backlog : list V) : ubstate.t V :=
  let hd := match cs with
            | chanstate.Buffered buf => buf
            | chanstate.Closed drain => drain
            | _ => []
            end in
  if closing then ubstate.Closed (hd ++ backlog) else ubstate.Buffered (hd ++ backlog).

Definition Inv_ub (γ : Ub_names) : iProp Σ :=
  ∃ (cs : chanstate.t V) (backlog : list V) (closing closed : bool),
    "Hchan" ∷ own_chan γ.(ubn_chan) V cs ∗
    "Hub" ∷ own_ub γ.(ubn_ub) V (1/2) (ubstate_of closing cs backlog) ∗
    "Hbl" ∷ dghost_var γ.(ubn_bl) (DfracOwn (1/2)) backlog ∗
    "Hcl" ∷ dghost_var γ.(ubn_cl) (DfracOwn (1/2)) closing ∗
    "Hclsd" ∷ dghost_var γ.(ubn_clsd) (DfracOwn (1/2)) closed ∗
    "%Hclsd_iff" ∷ ⌜ closed = true ↔ ∃ drain, cs = chanstate.Closed drain ⌝ ∗
    "%Hcs_shape" ∷ ⌜ (∃ buf, cs = chanstate.Buffered buf) ∨ (∃ drain, cs = chanstate.Closed drain) ⌝ ∗
    "%Hclosed_frozen" ∷ ⌜ (∃ drain, cs = chanstate.Closed drain) → closing = true ∧ backlog = [] ⌝.

Definition mu_inv (b : loc) (γ : Ub_names) : iProp Σ :=
  ∃ (backlog_val : slice.t) (backlog_l : list V) (closing closed : bool),
    "Hbacklog_fld" ∷ b.[unbounded.Unbounded.t, "backlog"] ↦ backlog_val ∗
    "Hbacklog_sl" ∷ backlog_val ↦* backlog_l ∗
    "Hbacklog_cap" ∷ own_slice_cap V backlog_val (DfracOwn 1) ∗
    "Hclosing_fld" ∷ b.[unbounded.Unbounded.t, "closing"] ↦ closing ∗
    "Hclosed_fld" ∷ b.[unbounded.Unbounded.t, "closed"] ↦ closed ∗
    "Hbl" ∷ dghost_var γ.(ubn_bl) (DfracOwn (1/2)) backlog_l ∗
    "Hcl" ∷ dghost_var γ.(ubn_cl) (DfracOwn (1/2)) closing ∗
    "Hclsd" ∷ dghost_var γ.(ubn_clsd) (DfracOwn (1/2)) closed ∗
    (* [Close]/[Load] only ever set [closed := true] strictly after
       [closing := true] (never independently), so [closed] can't be true
       while [closing] is still false. *)
    "%Hclosing_closed" ∷ ⌜ closed = true → closing = true ⌝.

Definition is_Unbounded (b : loc) (γ : Ub_names) : iProp Σ :=
  ∃ (c_loc : loc),
    "#Hc_fld" ∷ b.[unbounded.Unbounded.t, "c"] ↦□ c_loc ∗
    "#Hchan" ∷ is_chan c_loc γ.(ubn_chan) V ∗
    "%Hcap" ∷ ⌜ chan_cap γ.(ubn_chan) = W64 1 ⌝ ∗
    "#Hlock" ∷ is_Mutex (b.[unbounded.Unbounded.t, "mu"]) (mu_inv b γ) ∗
    "#Hinv" ∷ inv nroot (Inv_ub γ).

Global Instance is_Unbounded_persistent b γ : Persistent (is_Unbounded b γ).
Proof. apply _. Qed.

Lemma wp_NewUnbounded :
  {{{ is_pkg_init unbounded }}}
    @! unbounded.NewUnbounded #()
  {{{ (b : loc) (γ : Ub_names), RET #b;
      is_Unbounded b γ ∗ own_ub γ.(ubn_ub) V (1/2) (ubstate.Buffered [])
  }}}.
Proof using W.
  wp_start.
  wp_apply chan.wp_make2; first word.
  iIntros (ch γc) "(#Hchan & %Hcap & Hoc)".
  wp_auto.
  wp_alloc b as "Hb".
  iStructNamedPrefix "Hb" "H".
  iMod (dghost_var_alloc ([] : list V)) as (γbl) "[Hbl1 Hbl2]".
  iMod (dghost_var_alloc false) as (γcl) "[Hcl1 Hcl2]".
  iMod (dghost_var_alloc false) as (γclsd) "[Hclsd1 Hclsd2]".
  iMod (ub_alloc V) as (γub) "[Hub_client Hub_inv]".
  pose (γ := {| ubn_chan := γc; ubn_ub := γub; ubn_bl := γbl; ubn_cl := γcl; ubn_clsd := γclsd |}).
  iMod (inv_alloc nroot _ (Inv_ub γ) with "[Hoc Hub_inv Hbl2 Hcl2 Hclsd2]") as "#Hinv".
  { iNext. iExists (chanstate.Buffered []), [], false, false. iFrame.
    iSplit.
    { iPureIntro. split; [done|]. intros [drain Hbad]; done. }
    iSplit.
    { iPureIntro. left. by exists []. }
    iPureIntro. intros [drain Hbad]; done. }
  iMod (init_Mutex (mu_inv b γ) with "[$Hmu] [Hbacklog Hclosing Hclosed Hbl1 Hcl1 Hclsd1]") as "#Hlock".
  { iNext. iExists slice.nil, [], false, false. iFrame.
    iSplitL "". { iApply own_slice_nil. }
    iSplitL "". { iApply own_slice_cap_nil. }
    iPureIntro. done. }
  iPersist "Hc".
  wp_auto.
  iApply ("HΦ" $! b γ).
  iSplitR "Hub_client"; last iFrame.
  iExists ch. iFrame "#". done.
Qed.

Lemma wp_Unbounded__Get (b : loc) (γ : Ub_names) :
  {{{ is_pkg_init unbounded ∗ is_Unbounded b γ }}}
    b @! (go.PointerType unbounded.Unbounded) @! "Get" #b
  {{{ (c_loc : loc), RET #c_loc; is_chan c_loc γ.(ubn_chan) V }}}.
Proof using W.
  wp_start as "#Hub". iNamed "Hub".
  wp_auto.
  iApply "HΦ". iFrame "#".
Qed.

Lemma wp_Unbounded__Close (b : loc) (γ : Ub_names) :
  ∀ Φ,
  is_Unbounded b γ ∗ is_pkg_init sync  -∗
  ub_close_au γ.(ubn_ub) V (⊤∖↑nroot) (Φ #()) -∗
  WP b @! (go.PointerType unbounded.Unbounded) @! "Close" #() {{ Φ }}.
Proof using W.
 wp_start as "#Hunb".
 iNamed "HΦ".
   wp_apply wp_with_defer as "%defer Hdefer" . simpl subst.
  wp_auto_lc 3. wp_bind.
  iDestruct "Hunb" as "[#Hunb Hsync]".
  iNamed "Hunb".
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hmu]".
  iNamed "Hmu". wp_auto.
  destruct closing.
  - (* already closing: idempotent no-op, matches [ub_close_au]'s [Closed _] branch *)
    wp_auto_lc 5.
    rewrite -fupd_wp.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing_g closed_g) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (dghost_var_agree with "Hcl Hcl_inv") as %<-.
    (* [closing] is already set, so the invariant's half sits at [Closed _] and
       the idempotent arm is the one that applies.  We lend that half to the
       client, who owns the other, and take it back unchanged. *)
    rewrite /ubstate_of /=.
    iAssert (£1)%I with "[$]" as "Hlc".
    iRight in "HΦ".
    iMod ("HΦ" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
    iMod ("Hclose" with "[Hchan_inv Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
    { iNext. iExists cs, backlog, true, closed_g. iFrame "∗%". }
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
    { iNext. iExists backlog_val, backlog_l, true, closed. iFrame. done. }
    iApply "HΦ".
  - (* first call: flipping the ghost [closing] mirror is itself the full
       linearization point for [ub_close_au] *)
    wp_auto_lc 5.
    rewrite -fupd_wp.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing_g closed_g) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (dghost_var_agree with "Hcl Hcl_inv") as %<-.
    (* [closing] is still clear, so the invariant's half sits at [Buffered _]
       and the real arm applies.  Unlike the old pattern-matching form the
       post-state is fixed by the arm itself ([Buffered buff -> Closed buff]),
       so the implementation no longer updates [own_ub] at all: firing the
       client's arm *is* the linearization point. *)
    rewrite /ubstate_of /=.
    iAssert (£1)%I with "[$]" as "Hlc".
    iLeft in "HΦ".
    iMod ("HΦ" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
    iMod (dghost_var_update_halves true with "Hcl Hcl_inv") as "[Hcl Hcl_inv]".
    iMod ("Hclose" with "[Hchan_inv Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
    { iNext. iExists cs, backlog, true, closed_g. iFrame "∗%".
      (* [closing_g] was [false] here (this is the "not yet closing" call),
         so [Hclosed_frozen_inv] forces [cs] can't already be [Closed _] —
         the new fact (with [closing] now flipped to [true]) is thus
         vacuously true. *)
      iPureIntro. intros [drain Hbad].
      exfalso. destruct (Hclosed_frozen_inv (ex_intro _ drain Hbad)) as [Hcontra _].
      discriminate. }
    iModIntro.
    wp_if_destruct.
    + (* backlog also empty: physically close the channel too. This has no
         further abstract effect: [ubstate_of] is keyed on [closing], which
         is already [true], and [Buffered buf]/[Closed buf] share the same
         head [buf] either way. *)
      iDestruct (own_slice_len with "Hbacklog_sl") as %Hbacklog_len.
      assert (backlog_l = []) as ->.
      { apply length_zero_iff_nil. word. }
      wp_apply (chan.wp_close with "[$Hchan]").
      iIntros "Hlcs".
      (* [close_au] is now a conjunction of one arm per reachable pre-state, so
         instead of one case analysis under a single view shift we discharge
         three arms separately.  [c] has capacity 1, which rules out [Idle]; the
         mutex-side [closed] flag still being clear rules out [Closed _]; only
         the [Buffered] arm does any work. *)
      rewrite /close_au. repeat iSplit.
      * (* close_idle_au: [Idle] is a capacity-0 state, but [c] has cap 1. *)
        iIntros "[Hlc Himpl]".
        iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
        exfalso. simpl in Hcv. rewrite Hcap in Hcv. word.
      * (* close_buf_au: the real transition, [Buffered buff -> Closed buff]. *)
        iIntros (buff) "[Hlc Himpl]".
        iInv "Hinv" as "Hi2" "Hclose2".
        iMod (lc_fupd_elim_later with "Hlc Hi2") as "Hi2".
        iDestruct "Hi2" as (cs2 backlog2 closing2 closed2) "Hrest2".
        iNamedSuffix "Hrest2" "_inv2".
        (* [Hclsd] (mutex side) is still [false] here: we have only stored into
           the physical [closed] field, not yet updated the ghost mirror. *)
        iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
        iDestruct (dghost_var_agree with "Hcl Hcl_inv2") as %<-.
        iDestruct (dghost_var_agree with "Hbl Hbl_inv2") as %<-.
        iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
        iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
        iMod (own_chan_halves_update (chanstate.Closed buff)
               with "Hchan_inv2 Himpl") as "[H1 H2]".
        { simpl in Hcv |- *. destruct buff; [ lia | lia ]. }
        iMod (dghost_var_update_halves true with "Hclsd Hclsd_inv2") as "[Hclsd Hclsd_inv2]".
        iMod ("Hclose2" with "[H1 Hub_inv2 Hbl_inv2 Hcl_inv2 Hclsd_inv2]") as "_".
        { iNext. iExists (chanstate.Closed buff), [], true, true. iFrame.
          iSplit.
          { iPureIntro. split; [intros _; by exists buff | done]. }
          iSplit.
          { iPureIntro. right. by exists buff. }
          iPureIntro. done. }
        iModIntro. iFrame "H2".
        wp_auto.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
        { iNext. iExists backlog_val, [], true, true. iFrame. done. }
        iApply "HΦ".
      * (* close_closed_au: [c] cannot already be closed.  [closing] was clear
           on entry to this branch, so [Hclosing_closed] gives [closed = false],
           while [Hclsd_iff] would force [closed = true] for a [Closed _] state. *)
        iIntros (drain) "[Hlc Himpl]".
        iInv "Hinv" as "Hi2" "Hclose2".
        iMod (lc_fupd_elim_later with "Hlc Hi2") as "Hi2".
        iDestruct "Hi2" as (cs2 backlog2 closing2 closed2) "Hrest2".
        iNamedSuffix "Hrest2" "_inv2".
        iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
        iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
        exfalso.
        assert (closed = true) as Hct by (apply Hclsd_iff_inv2; eauto).
        specialize (Hclosing_closed Hct). discriminate.
    + wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists backlog_val, backlog_l, true, closed. iFrame. done. }
      iApply "HΦ".
Qed.

(** [Load] never needs a caller-supplied AU: whichever of its three
    outcomes fires — move [backlog]'s head into [c], leave everything
    untouched because [c] is already full, or physically close [c] once
    [closing] is set and the backlog has drained — [own_ub]'s value
    ([hd cs ++ backlog]) is unchanged. Moving an item from [backlog] into
    [c] just relocates it within that same concatenation, and
    [Buffered []]/[Closed []] both contribute [hd = []]. *)
Lemma wp_Unbounded__Load (b : loc) (γ : Ub_names) :
  {{{ is_pkg_init unbounded ∗ is_pkg_init sync ∗ is_Unbounded b γ }}}
    b @! (go.PointerType unbounded.Unbounded) @! "Load" #()
  {{{ RET #(); True }}}.
Proof using W.
  wp_start as "#Hunb".
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst.
  wp_auto_lc 3. wp_bind.
  iNamed "Hunb".
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hmu]".
  iNamed "Hmu". wp_auto.
  wp_if_destruct.
  - (* backlog nonempty: attempt to send its head *)
    destruct backlog_l as [|hd tl].
    { iDestruct (own_slice_len with "Hbacklog_sl") as %Hlen. exfalso. simpl in Hlen. word. }
    iDestruct (own_slice_len with "Hbacklog_sl") as %Hlen0.
    wp_bind.
    destruct decide.
    all: try word.
    simpl.
    replace (sint.Z (W64 0)) with (0) by word.
    wp_auto.
    wp_apply (wp_load_slice_index (t:=go.any) (V:=V) backlog_val (0:Z) (hd :: tl) (DfracOwn 1) hd with "[$Hbacklog_sl]").
    { word. }
    { iPureIntro. done. }
    iIntros "Hbacklog_sl". wp_auto.
    wp_bind.
    wp_apply chan.wp_select_nonblocking.
    iSplit.
    + (* the lone send clause *)
      simpl.
      iSplit; last done.
      iExists V, c_loc, γ.(ubn_chan), hd, _, _, _.
      iSplit; first done.
      iFrame "Hchan".
      (* [nonblocking_send_au] is now [fast_path ∧ enq ∧ closed ∧ Φnotready],
         so each arm is discharged separately instead of by one case analysis
         under a single view shift.  [c] has capacity 1, so it is never
         [RcvWait]; and [Load] only reaches this send with a non-empty backlog,
         which [Hclosed_frozen] rules out once [c] is closed. *)
      rewrite /nonblocking_send_au.
      iSplit.
      { (* send_fast_path_au: [RcvWait] is a capacity-0 state. *)
        iIntros "[Hlc Himpl]".
        iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
        exfalso. simpl in Hcv. rewrite Hcap in Hcv. word. }
      iSplit; last first.
      { iSplit; last done.
        (* send_closed_au *)
        iIntros (drain) "[Hlc Himpl]".
        iInv "Hinv" as "Hi" "Hclose".
        iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
        iDestruct "Hi" as (cs backlog closing_g closed_g) "Hrest".
        iNamedSuffix "Hrest" "_inv".
        iDestruct (dghost_var_agree with "Hbl Hbl_inv") as %<-.
        iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
        exfalso.
        destruct (Hclosed_frozen_inv (ex_intro _ drain eq_refl)) as [_ Hbad].
        discriminate. }
      (* send_enq_au: the real transition, appending [hd] to [c]'s buffer. *)
      iIntros (buf) "(Hlc & %Hroom & Himpl)".
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
      iDestruct "Hi" as (cs backlog closing_g closed_g) "Hrest".
      iNamedSuffix "Hrest" "_inv".
      iDestruct (dghost_var_agree with "Hbl Hbl_inv") as %<-.
      iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
      assert (closed_g = false) as ->.
      { destruct closed_g; [exfalso|done].
        destruct (proj1 Hclsd_iff_inv eq_refl) as [d Hbad]. discriminate. }
      iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
      iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [hd]))
             with "Hchan_inv Himpl") as "[H1 H2]".
      { simpl in Hcv, Hroom |- *. rewrite length_app /=. lia. }
      iMod (dghost_var_update_halves tl with "Hbl Hbl_inv") as "[Hbl Hbl_inv]".
      iMod ("Hclose" with "[H1 Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
      { iNext. iExists (chanstate.Buffered (buf ++ [hd])), tl, closing_g, false.
        rewrite /ubstate_of /= -app_assoc.
        iFrame "∗%".
        iPureIntro. split; [|split].
        { split; [discriminate | intros [d Hbad]; discriminate]. }
        { left. by exists (buf ++ [hd]). }
        { intros [d Hbad]; discriminate. } }
      iModIntro. iFrame "H2".
      wp_auto.
      wp_bind.
      destruct decide.
      all: try word.
      simpl.
      replace (sint.Z (W64 0)) with (0) by word.
      wp_auto.
      wp_apply (wp_store_slice_index (V:=V) with "[$Hbacklog_sl]").
      { simpl. word. }
      iIntros "Hbacklog_sl".
      wp_auto.
      iDestruct (own_slice_len with "Hbacklog_sl") as %Hlen2.
      rewrite length_insert in Hlen2.
      iDestruct (own_slice_wf with "Hbacklog_sl") as %Hwf.
      iDestruct (own_slice_cap_wf with "Hbacklog_cap") as %Hwf2.
      iDestruct (own_slice_slice (W64 1) backlog_val.(slice.len) with "Hbacklog_sl") as "(_ & Hmid & _)".
      { word. }
      assert (0 ≤ sint.Z (W64 1) ≤ sint.Z backlog_val.(slice.len) ≤ sint.Z backlog_val.(slice.cap)) as Hcapbound.
      { word. }
      iDestruct (own_slice_cap_slice backlog_val (W64 1) (DfracOwn 1) Hcapbound with "Hbacklog_cap") as "Hcapfinal".
      destruct decide. all: try word.
      wp_auto.
      assert (drop (sint.nat (W64 1))
                (take (sint.nat backlog_val.(slice.len))
                   (<[Z.to_nat 0:=interface.nil]> (hd :: tl))) = tl) as Heq3.
      { rewrite take_ge; last (rewrite length_insert; lia).
        replace (Z.to_nat 0) with 0%nat by lia.
        replace (sint.nat (W64 1)) with 1%nat by word.
        simpl. done. }
      iAssert (slice.slice backlog_val V (W64 1) backlog_val.(slice.len) ↦* tl)%I
        with "[Hmid]" as "Hmid".
      { iExactEq "Hmid". f_equal. done. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hmid Hcapfinal Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists (slice.slice backlog_val V (W64 1) backlog_val.(slice.len)), tl, closing, closed.
        iFrame "∗". iPureIntro. exact Hclosing_closed. }
      iApply "HΦ". done.
    + (* default: channel full, nothing to do *)
    wp_auto.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists backlog_val, (hd :: tl), closing, closed. iFrame. done. }
      iApply "HΦ".
      done.
  - (* backlog empty *)
    iDestruct (own_slice_len with "Hbacklog_sl") as %Hbacklog_len.
    assert (backlog_l = []) as ->.
    { apply length_zero_iff_nil. word. }
    wp_if_destruct.
    + (* closing && !closed: physically close the channel *)
    subst. simpl.
    destruct closed.
    { wp_auto.
      wp_bind.
       wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iFrame. done.
      }
      iApply "HΦ".
      done.
    }
    wp_auto.
      wp_apply (chan.wp_close with "[$Hchan]").
      iIntros "Hlcs".
      (* Three arms again: [c] has capacity 1 so it is never [Idle], and the
         mutex-side [closed] flag is still clear so it is not already closed. *)
      rewrite /close_au.
      iSplit.
      { (* close_idle_au *)
        iIntros "[Hlc Himpl]".
        iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
        exfalso. simpl in Hcv. rewrite Hcap in Hcv. word. }
      iSplit; last first.
      { (* close_closed_au *)
        iIntros (drain) "[Hlc Himpl]".
        iInv "Hinv" as "Hi2" "Hclose2".
        iMod (lc_fupd_elim_later with "Hlc Hi2") as "Hi2".
        iDestruct "Hi2" as (cs2 backlog2 closing2 closed2) "Hrest2".
        iNamedSuffix "Hrest2" "_inv2".
        iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
        iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
        exfalso.
        assert (false = true) as Hbad by (apply Hclsd_iff_inv2; eauto).
        discriminate. }
      (* close_buf_au: the real transition. *)
      iIntros (buff) "[Hlc Himpl]".
      iInv "Hinv" as "Hi2" "Hclose2".
      iMod (lc_fupd_elim_later with "Hlc Hi2") as "Hi2".
      iDestruct "Hi2" as (cs2 backlog2 closing2 closed2) "Hrest2".
      iNamedSuffix "Hrest2" "_inv2".
      iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
      iDestruct (dghost_var_agree with "Hcl Hcl_inv2") as %<-.
      iDestruct (dghost_var_agree with "Hbl Hbl_inv2") as %<-.
      iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
      iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
      iMod (own_chan_halves_update (chanstate.Closed buff)
             with "Hchan_inv2 Himpl") as "[H1 H2]".
      { simpl in Hcv |- *. destruct buff; lia. }
      iMod (dghost_var_update_halves true with "Hclsd Hclsd_inv2") as "[Hclsd Hclsd_inv2]".
      iMod ("Hclose2" with "[H1 Hub_inv2 Hbl_inv2 Hcl_inv2 Hclsd_inv2]") as "_".
      { iNext. iExists (chanstate.Closed buff), [], true, true. iFrame.
        iSplit.
        { iPureIntro. split; [intros _; by exists buff | done]. }
        iSplit.
        { iPureIntro. right. by exists buff. }
        iPureIntro. done. }
      iModIntro. iFrame "H2".
      wp_auto.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists backlog_val, [], true, true. iFrame. done. }
      iApply "HΦ".
      done.
    + (* nothing to do *)
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists backlog_val, [], false, closed. iFrame. done. }
      iApply "HΦ".
      done.
Qed.

(* Given the global is initialized, reading it is just a load. In CPS form
   rather than a Hoare triple because the load is the last step, leaving no
   program step to strip a [▷] off a triple's postcondition. *)
Lemma wp_load_errBufferClosed :
  ∀ Φ,
  errBufferClosed_init -∗
  (∀ err : interface.t_ok, is_BufferClosed err -∗ Φ #(interface.ok err)) -∗
  WP ![go.error] #(global_addr unbounded.errBufferClosed) {{ Φ }}.
Proof using W.
  iIntros (Φ) "#Hinit HΦ".
  iDestruct "Hinit" as (err) "#HBc".
  rewrite /is_BufferClosed. iNamed "HBc".
  wp_auto.
  iApply "HΦ". rewrite /is_BufferClosed. iFrame "#".
Qed.

Lemma wp_Unbounded__Put (b : loc) (γ : Ub_names) (v : V) :
  ∀ Φ,
  is_Unbounded b γ ∗ is_pkg_init sync ∗ errBufferClosed_init -∗
  ub_send_au γ.(ubn_ub) V (⊤∖↑nroot) v (∀ errv, Φ errv) -∗
  WP b @! (go.PointerType unbounded.Unbounded) @! "Put" #v {{ Φ }}.
Proof using W.
  wp_start as "#Hunb".
  iNamed "HΦ".
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst.
  wp_auto_lc 3. wp_bind.
  iDestruct "Hunb" as "(#Hunb & Hsync & #Hmrinit)".
  iNamed "Hunb".
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hmu]".
  iNamed "Hmu". wp_auto.
  destruct closing.
  - (* already closing: matches [ub_send_au]'s [Closed _] branch, no-op *)
    wp_auto_lc 2.
    rewrite -fupd_wp.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing_g closed_g) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (dghost_var_agree with "Hcl Hcl_inv") as %<-.
    (* [closing] is set, so the invariant's half sits at [Closed _]: the no-op
       arm applies and [Put] just returns [errBufferClosed]. *)
    rewrite /ubstate_of /=.
    iAssert (£1)%I with "[$]" as "Hlc".
    iRight in "HΦ".
    iMod ("HΦ" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
    iMod ("Hclose" with "[Hchan_inv Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
    { iNext. iExists cs, backlog, true, closed_g. iFrame "∗%". }
    iModIntro.
    wp_bind.
    wp_apply (wp_load_errBufferClosed with "Hmrinit").
    iIntros (err_bc) "_".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
    { iNext. iExists backlog_val, backlog_l, true, closed. iFrame. done. }
    iApply "HΦ".
  - (* open: append v, via the fast-path send or the backlog *)
    wp_auto_lc 2.
    wp_if_destruct.
    + (* backlog empty: attempt the fast-path nonblocking send *)
      iDestruct (own_slice_len with "Hbacklog_sl") as %Hbacklog_len.
      assert (backlog_l = []) as ->.
      { apply length_zero_iff_nil. word. }
      wp_bind.
      wp_apply chan.wp_select_nonblocking.
      iSplit.
      * (* the lone send clause *)
      simpl.
        iSplit; last done.
        iExists V, c_loc, γ.(ubn_chan), v, _, _, _.
        iSplit; first done.
        iFrame "Hchan".
        (* Three arms plus the trivial not-ready witness.  [c] has capacity 1,
           so it is never [RcvWait]; [closing] is clear on this branch, so [c]
           is not closed either.  The [enq] arm fires the client's own
           [ub_send_enq_au] in the same atomic step: the buffer's linearization
           point is the channel's. *)
        rewrite /nonblocking_send_au.
        iSplit.
        { (* send_fast_path_au *)
          iIntros "[Hlc Himpl]".
          iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
          exfalso. simpl in Hcv. rewrite Hcap in Hcv. word. }
        iSplit; last first.
        { iSplit; last done.
          (* send_closed_au *)
          iIntros (drain) "[Hlc Himpl]".
          iInv "Hinv" as "Hi" "Hclose".
          iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
          iDestruct "Hi" as (cs2 backlog2 closing2 closed2) "Hrest2".
          iNamedSuffix "Hrest2" "_inv2".
          iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
          iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
          exfalso.
          assert (closed = true) as Hct by (apply Hclsd_iff_inv2; eauto).
          specialize (Hclosing_closed Hct). discriminate. }
        (* send_enq_au *)
        iIntros (buf) "(Hlc & %Hroom & Himpl)".
        iInv "Hinv" as "Hi" "Hclose".
        iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
        iDestruct "Hi" as (cs2 backlog2 closing2 closed2) "Hrest2".
        iNamedSuffix "Hrest2" "_inv2".
        iDestruct (dghost_var_agree with "Hcl Hcl_inv2") as %<-.
        iDestruct (dghost_var_agree with "Hbl Hbl_inv2") as %<-.
        iDestruct (dghost_var_agree with "Hclsd Hclsd_inv2") as %<-.
        iDestruct (own_chan_agree with "Hchan_inv2 Himpl") as %->.
        iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
        iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v]))
               with "Hchan_inv2 Himpl") as "[H1 H2]".
        { simpl in Hcv, Hroom |- *. rewrite length_app /=. lia. }
        rewrite /ubstate_of /= app_nil_r.
        iAssert (£1)%I with "[$]" as "Hlc2".
        iLeft in "HΦ".
        iMod ("HΦ" with "[$Hlc2 $Hub_inv2]") as "[Hub_inv2 HΦ]".
        iMod ("Hclose" with "[H1 Hub_inv2 Hbl_inv2 Hcl_inv2 Hclsd_inv2]") as "_".
        { iNext. iExists (chanstate.Buffered (buf ++ [v])), [], false, closed.
          rewrite /ubstate_of /= app_nil_r.
          iFrame "∗".
          assert (closed = false) as ->.
          { destruct closed; [exfalso; specialize (Hclosing_closed eq_refl); discriminate | done]. }
          iPureIntro. split; [|split].
          { split; [discriminate | intros [drain Hbad]; discriminate]. }
          { left. by exists (buf ++ [v]). }
          { intros [drain Hbad]; discriminate. } }
        iModIntro. iFrame "H2".
        wp_auto.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl Hbacklog_cap Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
        { iNext. iExists backlog_val, [], false, closed. iFrame. done. }
        iApply "HΦ".
      * (* default: channel wasn't ready, fall through to the backlog append *)
      wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros (sl_ptr) "[Hsl _]". wp_auto.
        wp_apply (wp_slice_append with "[$Hbacklog_sl $Hbacklog_cap $Hsl]").
        iIntros (backlog_val') "(Hbacklog_sl' & Hbacklog_cap' & _)".
        wp_auto.
        rewrite -fupd_wp.
        iInv "Hinv" as "Hi" "Hclose".
        iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
        iDestruct "Hi" as (cs2 backlog2 closing2 closed2) "Hrest2".
        iNamedSuffix "Hrest2" "_inv2".
        iDestruct (dghost_var_agree with "Hcl Hcl_inv2") as %<-.
        iDestruct (dghost_var_agree with "Hbl Hbl_inv2") as %<-.
        (* the client's enq arm; the backlog is empty on this branch *)
        rewrite /ubstate_of /= app_nil_r.
        iAssert (£1)%I with "[$]" as "Hlc".
        iLeft in "HΦ".
        iMod ("HΦ" with "[$Hlc $Hub_inv2]") as "[Hub_inv2 HΦ]".
        iMod (dghost_var_update_halves [v] with "Hbl Hbl_inv2") as "[Hbl Hbl_inv2]".
        iMod ("Hclose" with "[Hchan_inv2 Hub_inv2 Hbl_inv2 Hcl_inv2 Hclsd_inv2]") as "_".
        { iNext. iExists cs2, [v], false, closed2.
          rewrite /ubstate_of /=.
          iFrame "∗%".
          iPureIntro. intros [drain Hbad].
          exfalso. destruct (Hclosed_frozen_inv2 (ex_intro _ drain Hbad)) as [Hcontra _].
          discriminate. }
        iModIntro.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl' Hbacklog_cap' Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
        { iNext. iExists backlog_val', [v], false, closed. iFrame. done. }
        iApply "HΦ".
    + (* backlog nonempty: skip the send entirely, go straight to the backlog append *)
      wp_apply wp_slice_literal. iSplitR; first done. iIntros (sl_ptr) "[Hsl _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hbacklog_sl $Hbacklog_cap $Hsl]").
      iIntros (backlog_val') "(Hbacklog_sl' & Hbacklog_cap' & _)".
      wp_auto.
      rewrite -fupd_wp.
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
      iDestruct "Hi" as (cs2 backlog2 closing2 closed2) "Hrest2".
      iNamedSuffix "Hrest2" "_inv2".
      iDestruct (dghost_var_agree with "Hcl Hcl_inv2") as %<-.
      iDestruct (dghost_var_agree with "Hbl Hbl_inv2") as %<-.
      (* the client's enq arm: the invariant's half is at
         [Buffered (hd cs2 ++ backlog_l)] and the arm appends [v] to it, which
         is exactly [ubstate_of false cs2 (backlog_l ++ [v])]. *)
      rewrite /ubstate_of /=.
      iAssert (£1)%I with "[$]" as "Hlc".
      iLeft in "HΦ".
      iMod ("HΦ" with "[$Hlc $Hub_inv2]") as "[Hub_inv2 HΦ]".
      iMod (dghost_var_update_halves (backlog_l ++ [v]) with "Hbl Hbl_inv2") as "[Hbl Hbl_inv2]".
      iMod ("Hclose" with "[Hchan_inv2 Hub_inv2 Hbl_inv2 Hcl_inv2 Hclsd_inv2]") as "_".
      { iNext. iExists cs2, (backlog_l ++ [v]), false, closed2.
        rewrite /ubstate_of /= app_assoc.
        iFrame "∗%".
        iPureIntro. intros [drain Hbad].
        exfalso. destruct (Hclosed_frozen_inv2 (ex_intro _ drain Hbad)) as [Hcontra _].
        discriminate. }
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbacklog_fld Hbacklog_sl' Hbacklog_cap' Hclosing_fld Hclosed_fld Hbl Hcl Hclsd]").
      { iNext. iExists backlog_val', (backlog_l ++ [v]), false, closed. iFrame. done. }
      iApply "HΦ".
Qed.

(** Converts a caller-supplied [ub_recv_au] into a [recv_au] on the raw
    channel [γ.(ubn_chan)], so a client can receive off [Get()]'s channel
    directly via [chan.wp_receive] — no [Unbounded.mu] needed, since this
    only ever touches [own_chan]/[own_ub], both fully reachable via
    [Inv_ub] alone (see the architecture note at the top of this file). *)
Lemma ub_recv_au_to_chan_recv_au (γ : Ub_names) (Φ : V → bool → iProp Σ) :
  inv nroot (Inv_ub γ) -∗
  £1 -∗
  ub_recv_au γ.(ubn_ub) V (⊤∖↑nroot) Φ -∗
  recv_au γ.(ubn_chan) V Φ.
Proof using W.
  iIntros "#Hinv Hlc Hget".
  (* Five arms.  [Inv_ub]'s [Hcs_shape] says [c] is always [Buffered _] or
     [Closed _] -- it has capacity 1, so no rendezvous state ever arises --
     which makes the two unbuffered arms vacuous.  The remaining three line up
     one-for-one with the buffer's own arms.

     One credit suffices for all five: the arms are joined by [∧], so they share
     resources and only the chosen one is ever eliminated.  Each arm is itself
     handed a further [£1] by the channel, which strips the invariant's later;
     ours pays for the client's [ub_recv_*] arm. *)
  rewrite /recv_au.
  iSplit.
  { (* recv_fast_path_au: [SndWait] is a rendezvous state, ruled out. *)
    iIntros (w) "[Hlc1 Himpl]".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing closed) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
    exfalso. destruct Hcs_shape_inv as [[? Hbad]|[? Hbad]]; discriminate. }
  iSplit.
  { (* recv_slow_path_au: [Idle] likewise. *)
    iIntros "[Hlc1 Himpl]".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing closed) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
    exfalso. destruct Hcs_shape_inv as [[? Hbad]|[? Hbad]]; discriminate. }
  iSplit.
  { (* recv_deq_au.  [c] holds [w :: rest]; the buffer's abstract queue is
       [(w :: rest) ++ backlog], so [w] is its head too.  Whether [closing] is
       set decides which of the buffer's two dequeue arms applies. *)
    iIntros (w rest) "[Hlc1 Himpl]".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing closed) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
    assert (closed = false) as ->.
    { destruct closed; [exfalso|done].
      destruct (proj1 Hclsd_iff_inv eq_refl) as [drain Hbad]. discriminate. }
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
    iMod (own_chan_halves_update (chanstate.Buffered rest)
           with "Hchan_inv Himpl") as "[H1 H2]".
    { simpl in Hcv |- *. lia. }
    rewrite /ubstate_of /=.
    destruct closing.
    - (* closing: the queue reads [Closed (w :: rest ++ backlog)] *)
      iRight in "Hget". iLeft in "Hget".
      iMod ("Hget" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
      iMod ("Hclose" with "[H1 Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
      { iNext. iExists (chanstate.Buffered rest), backlog, true, false.
        rewrite /ubstate_of /=. iFrame.
        iPureIntro. split; [|split].
        { split; [discriminate | intros [d Hbad]; discriminate]. }
        { left. by exists rest. }
        { intros [d Hbad]; discriminate. } }
      iModIntro. iFrame "H2 HΦ".
    - (* open: the queue reads [Buffered (w :: rest ++ backlog)] *)
      iLeft in "Hget".
      iMod ("Hget" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
      iMod ("Hclose" with "[H1 Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
      { iNext. iExists (chanstate.Buffered rest), backlog, false, false.
        rewrite /ubstate_of /=. iFrame.
        iPureIntro. split; [|split].
        { split; [discriminate | intros [d Hbad]; discriminate]. }
        { left. by exists rest. }
        { intros [d Hbad]; discriminate. } }
      iModIntro. iFrame "H2 HΦ". }
  iSplit.
  { (* recv_drain_au.  [c] is closed, so [Hclosed_frozen] forces an empty
       backlog and [Hclsd_iff] forces [closed]. *)
    iIntros (w rest) "[Hlc1 Himpl]".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing closed) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
    assert (closing = true ∧ backlog = []) as [-> ->].
    { apply Hclosed_frozen_inv. eauto. }
    assert (closed = true) as ->.
    { destruct Hclsd_iff_inv as [_ Hback]. apply Hback. eauto. }
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
    iMod (own_chan_halves_update (chanstate.Closed rest)
           with "Hchan_inv Himpl") as "[H1 H2]".
    { simpl in Hcv |- *. destruct rest; lia. }
    rewrite /ubstate_of /= app_nil_r.
    iRight in "Hget". iLeft in "Hget".
    iMod ("Hget" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
    iMod ("Hclose" with "[H1 Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
    { iNext. iExists (chanstate.Closed rest), [], true, true.
      rewrite /ubstate_of /= app_nil_r. iFrame.
      iPureIntro. split; [|split].
      { split; [intros _; by exists rest | done]. }
      { right. by exists rest. }
      { intros _. done. } }
    iModIntro. iFrame "H2 HΦ". }
  { (* recv_closed_au: closed and fully drained.  The channel does not move, so
       the implementation's half goes straight back. *)
    iIntros "[Hlc1 Himpl]".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 Hi") as "Hi".
    iDestruct "Hi" as (cs backlog closing closed) "Hrest".
    iNamedSuffix "Hrest" "_inv".
    iDestruct (own_chan_agree with "Hchan_inv Himpl") as %->.
    assert (closing = true ∧ backlog = []) as [-> ->].
    { apply Hclosed_frozen_inv. eauto. }
    assert (closed = true) as ->.
    { destruct Hclsd_iff_inv as [_ Hback]. apply Hback. eauto. }
    rewrite /ubstate_of /=.
    iRight in "Hget". iRight in "Hget".
    iMod ("Hget" with "[$Hlc $Hub_inv]") as "[Hub_inv HΦ]".
    iMod ("Hclose" with "[Hchan_inv Hub_inv Hbl_inv Hcl_inv Hclsd_inv]") as "_".
    { iNext. iExists (chanstate.Closed []), [], true, true.
      rewrite /ubstate_of /=. iFrame.
      iPureIntro. split; [|split].
      { split; [intros _; by exists [] | done]. }
      { right. by exists []. }
      { intros _. done. } }
    iModIntro. iFrame "Himpl HΦ". }
Qed.

End unbounded_impl.
