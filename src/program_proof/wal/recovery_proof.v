From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.
Context `{!crashG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Theorem wp_MkLog_init d (bs: list Block) :
  {{{ 0 d↦∗ repeat block0 513 ∗
      513 d↦∗ bs ∗
      P (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0)  }}}
    MkLog #d
  {{{ γ l, RET #l; is_wal P l γ }}}.
Proof.
Admitted.

Set Nested Proofs Allowed.
Lemma diskEnd_is_get_at_least (γ: circ_names) q (z: Z):
  diskEnd_is γ q z ==∗ diskEnd_is γ q z ∗ diskEnd_at_least γ z.
Proof.
  iIntros "(%&Hfm)". by iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
Qed.

Lemma start_is_get_at_least (γ: circ_names) q (z: u64):
  start_is γ q z ==∗ start_is γ q z ∗ start_at_least γ z.
Proof.
  iIntros "Hfm". by iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
Qed.

(* XXX: this used to have a postcondition that would give you some σ' which was
   the crash of σ:

      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗

   However, I think simulating the crash to σ' should be
   done using post_crash modality at the time when we initially
   crashed. mkLog_recover is itself a no-op at the spec level. *)

Theorem wpc_mkLog_recover k E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    mkLog #d @ NotStuck; k; ⊤; E2
  {{{ γ' l, RET #l;
       is_wal_inv_pre l γ' σ ∗
       (* XXX whatever it is that background threads needs *)
       True}}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "Hcs HΦ".
  rewrite /mkLog.

  Ltac show_crash1 := eauto.

  wpc_pures; first by show_crash1.
  iNamed "Hcs".
  iNamed "Hdisk".
  wpc_bind (recoverCircular _).

  Ltac show_crash2 :=
    try (crash_case); iExists _;
    iSplitL ""; first auto;
    iFrame; iExists _; iFrame; iExists _, _; iFrame "∗ #".

  wpc_apply (wpc_recoverCircular with "[$]").
  iSplit.
  { iIntros "Hcirc". show_crash2. }


  iNext. iIntros (γcirc' c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&Hstart&Hdisk&%&%&%)".

  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.
  iMod (diskEnd_is_get_at_least with "[$]") as "(Hdisk&#Hdisk_atLeast)".
  iMod (thread_own_alloc with "Hdisk") as (γdiskEnd_avail_name) "(HdiskEnd_exactly&Hthread_end)".
  iMod (start_is_get_at_least with "[$]") as "(Hstart&#Hstart_atLeast)".
  iMod (thread_own_alloc with "Hstart") as (γstart_avail_name) "(Hstart_exactly&Hthread_start)".
  set (γ' := (set circ_name (λ _, γcirc') γ)).

  wpc_frame_compl "Hupd_slice HdiskEnd_exactly Hstart_exactly".
  { crash_case. iExists γ'.
    rewrite /is_wal_inner_durable. simpl. rewrite /is_durable_txn/is_installed_txn/is_durable//=.
    simpl. iSplitL ""; first auto. rewrite /txns_ctx.
    iFrame. iExists _; iFrame.
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (γlock ml) "Hlock".

  clear γ'.
  set (γ' :=
         (set lock_name (λ _, γlock)
              (set start_avail_name (λ _, γstart_avail_name)
                   (set diskEnd_avail_name (λ _, γdiskEnd_avail_name)
                        (set circ_name (λ _, γcirc') γ))))).
  wp_pures.
  iDestruct (updates_slice_to_frag with "[$]") as "Hupd_slice".
  wp_apply (wp_mkSliding with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }
  iIntros (lslide) "Hsliding".
  iDestruct (is_sliding_wf with "[$]") as %Hsliding_wf.
  wp_apply wp_allocStruct; first by auto.
  iIntros (st) "Hwal_state".
  wp_pures.
  iMod (alloc_lock _ _ _ _ (wal_linv st γ') with "[$] [-]").
  { rewrite /wal_linv.
    assert (int.val diskStart + length upds = int.val diskEnd) as Heq_plus.
    { etransitivity; last eassumption. rewrite /circΣ.diskEnd //=. subst. word. }
    iExists {| diskEnd := diskEnd; memLog := _ |}. iSplitL "Hwal_state Hsliding".
    { iExists {| memLogPtr := _; shutdown := _; nthread := _ |}.
      iDestruct (struct_fields_split with "Hwal_state") as "Hwal_state".
      iDestruct "Hwal_state" as "(?&?&?&?&_)".
      iFrame. iPureIntro. rewrite /locked_wf//=.
      { destruct Hwf_circ as (?&?). subst. split.
        * split; first lia. rewrite Heq_plus. word.
        * eauto.
      }
    }
    rewrite //= /diskEnd_linv/diskStart_linv -Heq_plus.
    iFrame. iFrame "Hdisk_atLeast Hstart_atLeast".
    rewrite /memLog_linv //=.

    admit.
  }
Abort.

Theorem wpc_MkLog_recover stk k E1 E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    MkLog #d @ stk; k; E1; E2
  {{{ σ' γ' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
       is_wal_inv_pre l γ' σ' }}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
Abort.

End goose_lang.
