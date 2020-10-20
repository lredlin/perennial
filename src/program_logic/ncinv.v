From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre staged_wpc.
Set Default Proof Using "Type".
Import uPred.

Definition ncinv_def `{!invG Σ, !crashG Σ} N P : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → |NC={E,E ∖ ↑N}=> ▷ P ∗ (▷ P -∗ |NC={E ∖ ↑N,E}=> True).
Definition ncinv_aux : seal (@ncinv_def). Proof. by eexists. Qed.
Definition ncinv := ncinv_aux.(unseal).
Arguments ncinv {Σ _ _} N P%bi_scope.
Definition ncinv_eq : @ncinv = @ncinv_def := ncinv_aux.(seal_eq).
Instance: Params (@ncinv) 4 := {}.

Definition crash_inv_def `{!invG Σ, !crashG Σ} N P : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → C -∗ |0={E,E ∖ ↑N}=> ▷ P ∗ (▷ P -∗ |0={E ∖ ↑N,E}=> True).
Definition crash_inv_aux : seal (@crash_inv_def). Proof. by eexists. Qed.
Definition crash_inv := crash_inv_aux.(unseal).
Arguments crash_inv {Σ _ _} N P%bi_scope.
Definition crash_inv_eq : @crash_inv = @crash_inv_def := crash_inv_aux.(seal_eq).
Instance: Params (@crash_inv) 4 := {}.

Section ci.
Context `{!crashG Σ}.
Context `{!invG Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.

  (** ** Public API of ncinvariants *)
  Global Instance ncinv_contractive N : Contractive (ncinv N).
  Proof. rewrite ncinv_eq. solve_contractive. Qed.

  Global Instance ncinv_ne N : NonExpansive (ncinv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance ncinv_proper N : Proper (equiv ==> equiv) (ncinv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance ncinv_persistent N P : Persistent (ncinv N P).
  Proof. rewrite ncinv_eq. apply _. Qed.

  Lemma ncinv_alter N P Q : ncinv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ ncinv N Q.
  Proof.
    rewrite ncinv_eq. iIntros "#HI #HPQ !>" (E H).
    iMod ("HI" $! E H) as "[HP Hclose]".
    iDestruct ("HPQ" with "HP") as "[$ HQP]".
    iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
  Qed.

  Lemma ncinv_iff N P Q : ncinv N P -∗ ▷ □ (P ↔ Q) -∗ ncinv N Q.
  Proof.
    iIntros "#HI #HPQ". iApply (ncinv_alter with "HI").
    iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  (*
  Lemma ncinv_alloc' k N E P : ▷ P -∗ |k={E}=> ncinv N P.
  Proof.
    iIntros "HP". iApply own_ncinv_to_ncinv.
    iPoseProof (own_ncinv_alloc0 N E with "HP") as "H".
    iApply (fupd_level_le with "H"). lia.
  Qed.

  Lemma ncinv_alloc N E P : ▷ P ={E}=∗ ncinv N P.
  Proof.
    iIntros "HP". iApply own_ncinv_to_ncinv.
    iApply (own_ncinv_alloc N E with "HP").
  Qed.

  Lemma ncinv_alloc_open0 N E P :
    ↑N ⊆ E → ⊢ |0={E, E∖↑N}=> ncinv N P ∗ (▷P -∗ |0={E∖↑N, E}=> True).
  Proof.
    iIntros (?). iMod own_ncinv_alloc_open0 as "[HI $]"; first done.
    iApply own_ncinv_to_ncinv. done.
  Qed.

  Lemma ncinv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> ncinv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_ncinv_alloc_open as "[HI $]"; first done.
    iApply own_ncinv_to_ncinv. done.
  Qed.
  *)

  Lemma ncinv_acc E N P :
    ↑N ⊆ E → ncinv N P -∗ |NC={E,E∖↑N}=> ▷ P ∗ (▷ P -∗ |NC={E∖↑N,E}=> True).
  Proof.
    rewrite ncinv_eq /ncinv_def.
    iIntros (?) "#Hi".
    by iMod ("Hi" $! E with "[//]") as "($&$)".
  Qed.

  Lemma ncinv_combine N1 N2 N P Q :
    N1 ## N2 →
    ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    ncinv N1 P -∗ ncinv N2 Q -∗ ncinv N (P ∗ Q).
  Proof.
    rewrite ncinv_eq. iIntros (??) "#HncinvP #HncinvQ !>"; iIntros (E ?).
    iMod ("HncinvP" with "[%]") as "[$ HcloseP]"; first set_solver.
    iMod ("HncinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
    iMod (ncfupd_intro_mask' _ (E ∖ ↑N)) as "Hclose"; first set_solver.
    iIntros "!> [HP HQ]".
    iMod "Hclose" as %_. iMod ("HcloseQ" with "HQ") as %_. by iApply "HcloseP".
  Qed.

  Lemma ncinv_combine_dup_l N P Q :
    □ (P -∗ P ∗ P) -∗
    ncinv N P -∗ ncinv N Q -∗ ncinv N (P ∗ Q).
  Proof.
    rewrite ncinv_eq. iIntros "#HPdup #HncinvP #HncinvQ !>" (E ?).
    iMod ("HncinvP" with "[//]") as "[HP HcloseP]".
    iDestruct ("HPdup" with "HP") as "[$ HP]".
    iMod ("HcloseP" with "HP") as %_.
    iMod ("HncinvQ" with "[//]") as "[$ HcloseQ]".
    iIntros "!> [HP HQ]". by iApply "HcloseQ".
  Qed.

  (** ** Proof mode integration *)
  Global Instance into_ncinv_ncinv N P : IntoInv (ncinv N P) N := {}.

  Global Instance into_acc_ncinv N P E:
    IntoAcc (X := unit) (ncinv N P)
            (↑N ⊆ E) True (ncfupd E (E ∖ ↑N)) (ncfupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _".
    iMod (ncinv_acc with "Hinv") as "($&Hcl)"; first auto.
    iModIntro. auto.
  Qed.

  (** ** Derived properties *)
  Lemma ncinv_acc_strong E N P :
    ↑N ⊆ E → ncinv N P -∗ |NC={E,E∖↑N}=> ▷ P ∗ ∀ E', ▷ P -∗ |NC={E',↑N ∪ E'}=> True.
  Proof.
    iIntros (?) "Hncinv".
    iPoseProof (ncinv_acc (↑ N) N with "Hncinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (ncfupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    iPoseProof (ncfupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.

  Lemma ncinv_acc_timeless E N P `{!Timeless P} :
    ↑N ⊆ E → ncinv N P -∗ |NC={E,E∖↑N}=> P ∗ (P -∗ |NC={E∖↑N,E}=> True).
  Proof.
    iIntros (?) "Hncinv". iMod (ncinv_acc with "Hncinv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma ncinv_split_l N P Q : ncinv N (P ∗ Q) -∗ ncinv N P.
  Proof.
    iIntros "#HI". iApply ncinv_alter; eauto.
    iIntros "!> !> [$ $] $".
  Qed.
  Lemma ncinv_split_r N P Q : ncinv N (P ∗ Q) -∗ ncinv N Q.
  Proof.
    rewrite (comm _ P Q). eapply ncinv_split_l.
  Qed.
  Lemma ncinv_split N P Q : ncinv N (P ∗ Q) -∗ ncinv N P ∗ ncinv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (ncinv_split_l with "H") as "$".
    iPoseProof (ncinv_split_r with "H") as "$".
  Qed.

  Lemma inv_to_ncinv N P : inv N P -∗ ncinv N P.
  Proof.
    iIntros "#H". rewrite ncinv_eq /ncinv_def.
    iIntros "!>" (E Hsub). iInv "H" as "HP" "Hclo".
    iModIntro. iFrame. iIntros "HP". iApply fupd_ncfupd.
    by iMod ("Hclo" with "[$]").
  Qed.

  Theorem ncinv_dup_acc (Q: iProp Σ) N E (P: iProp Σ) :
    ↑N ⊆ E →
    ncinv N P -∗
        (P -∗ P ∗ Q) -∗
        |NC={E}=> ▷ Q.
  Proof.
    iIntros (Hsub) "Hinv HPtoQ".
    iInv "Hinv" as "HP" "Hclose".
    iDestruct ("HPtoQ" with "HP") as "[HP HQ]".
    iMod ("Hclose" with "HP") as "_".
    iIntros "!> !>".
    iFrame.
  Qed.

  (* One model of an ncinv that generates a cfupd for the P at allocation *)
  Context `{!stagedG Σ}.

  Definition own_ncinv N P :=
    (∃ γ, inv N (P ∨ (C ∗ staged_done γ)))%I.

  Lemma ncinv_alloc N E P:
    ▷ P ={E}=∗ ncinv N P ∗ <disc> |C={↑N}_0=> P.
  Proof using stagedG0.
    iIntros "HP". rewrite ncinv_eq /ncinv_def.
    iMod (pending_alloc) as (γ) "Hpending".
    iMod (inv_alloc N E (P ∨ (C ∗ staged_done γ)) with "[HP]") as "#Hinv".
    { by iLeft. }
    iSplitL "".
    - iIntros "!> !>" (E' Hsub).
      iInv "Hinv" as "[H|(>Hfalse&_)]" "Hclo".
      * iModIntro. iFrame. iIntros "HP". iMod ("Hclo" with "[HP]"); eauto.
      * rewrite ncfupd_eq /ncfupd_def. iIntros (?) "HNC".
        iDestruct (NC_C with "[$] [$]") as %[].
    - iModIntro. iModIntro. iIntros "HC". iInv "Hinv" as "H" "Hclo".
      iDestruct "H" as "[HP|(_&>Hfalse)]".
      * iFrame. iMod (pending_upd_done with "Hpending") as "Hdone".
        iMod ("Hclo" with "[HC Hdone]").
        { iRight. by iFrame. }
        eauto.
      * iDestruct (pending_done with "[$] [$]") as %[].
  Qed.

  (* Another model of an ncinv that generates two cfupds, one that is persistent
     and one that is not. Essentially we can think of the persistent one as an
     invariant that holds at crash time, and the non-persistent one is what
     recovery gets after. *)

  Definition own_ncinv_cinv N P Pcrash Prec :=
    (∃ γ1 γ2, inv N ((P ∗ staged_pending 1 γ1) ∨ (C ∗ Pcrash ∗ (Prec ∨ staged_done γ2) ∗ staged_done γ1)))%I.

  Lemma ncinv_cinv_alloc N E1 E2 P Pcrash Prec :
    ↑N ⊆ E2 →
    □ (▷ P -∗ |0={E2 ∖ ↑N}=> ▷ Pcrash ∗ ▷ Prec) -∗
    ▷ P ={E1}=∗ ncinv N P ∗ (<disc> |C={E2}_0=> Prec) ∗ □ |C={E2}_0=> inv N Pcrash.
  Proof using stagedG0.
    iIntros (?) "#Hwand HP".
    rewrite ncinv_eq /ncinv_def.
    iMod (pending_alloc) as (γ1) "Hpending1".
    iMod (pending_alloc) as (γ2) "Hpending2".
    iMod (inv_alloc N _ ((P ∗ staged_pending 1 γ1) ∨
                         (C ∗ Pcrash ∗ (Prec ∨ staged_done γ2) ∗ staged_done γ1))
            with "[HP Hpending1]") as "#Hinv".
    { iLeft. iFrame. }
    iSplitL ""; [| iSplitL "Hpending2"].
    - iIntros "!> !>" (E' Hsub).
      iInv "Hinv" as "[(HP&Hpend)|(>Hfalse&_)]" "Hclo".
      * iModIntro. iFrame. iIntros "HP". iMod ("Hclo" with "[HP Hpend]"); eauto.
        iLeft. iFrame.
      * rewrite ncfupd_eq /ncfupd_def. iIntros (?) "HNC".
        iDestruct (NC_C with "[$] [$]") as %[].
    - do 2 iModIntro.
      iIntros "HC". iInv "Hinv" as "H" "Hclo".
      iDestruct "H" as "[(HP&>Hpending1)|(C&Hcrash&Hcase&Hdone1)]".
      { iMod ("Hwand" with "[$]") as "(Hcrash&Hrec)".
        iMod (pending_upd_done with "Hpending1") as "Hdone1".
        iMod (pending_upd_done with "Hpending2") as "Hdone2".
        iMod ("Hclo" with "[Hcrash Hdone1 Hdone2 HC]").
        { iRight. iFrame. }
        eauto. }
      { iDestruct "Hcase" as "[Hrec | >Hfalse]".
        * iMod (pending_upd_done with "Hpending2") as "Hdone2".
          iMod ("Hclo" with "[Hcrash Hdone1 Hdone2 HC]").
          { iRight. iFrame. }
          by iFrame.
        * iDestruct (pending_done with "[$] [$]") as %[].
      }
    - do 2 iModIntro.
      iIntros "#HC". iInv "Hinv" as "H" "Hclo".
      iDestruct "H" as "[(HP&>Hpending1)|(C&Hcrash&Hcase&>#Hdone1)]".
      { iMod ("Hwand" with "[$]") as "(Hcrash&Hrec)".
        iMod (pending_upd_done with "Hpending1") as "#Hdone1".
        iMod ("Hclo" with "[Hcrash Hrec]").
        { iRight. iFrame "∗ #". }
        iModIntro. iNext.
        iEval (rewrite inv_eq /inv_def).
        iModIntro. iIntros (E Hsub).
        iInv "Hinv" as "H" "Hclo".
        iDestruct "H" as "[(HP&>Hpending1)|(C&Hcrash&Hcase&_)]".
        { iDestruct (pending_done with "[$] [$]") as %[]. }
        iModIntro. iFrame "Hcrash". iIntros "Hcrash".
        iMod ("Hclo" with "[Hcrash Hcase]").
        { iRight. iFrame "∗ #". }
        eauto.
      }
      {
        iMod ("Hclo" with "[Hcrash Hcase]").
        { iRight. iFrame "∗ #". }
        iModIntro. iNext.
        iEval (rewrite inv_eq /inv_def).
        iModIntro. iIntros (E Hsub).
        iInv "Hinv" as "H" "Hclo".
        iDestruct "H" as "[(HP&>Hpending1)|(C&Hcrash&Hcase&_)]".
        { iDestruct (pending_done with "[$] [$]") as %[]. }
        iModIntro. iFrame "Hcrash". iIntros "Hcrash".
        iMod ("Hclo" with "[Hcrash Hcase]").
        { iRight. iFrame "∗ #". }
        eauto.
      }
  Qed.
End ci.

(*
Section test.
Context `{irisG Λ Σ}.
Example test_ncinv_open s N E1 P e Φ :
  ↑N ⊆ E1 →
  ncinv N P -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "Hinv".
  iApply ncfupd_wp.
  iInv "Hinv" as "H" "Hclo".
  iMod ("Hclo" with "[$]"). iModIntro.
Abort.
End test.
*)

