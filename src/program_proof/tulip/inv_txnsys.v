From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import dual_lookup vslice nat.
From Perennial.program_proof.tulip Require Import action base res.

(** Global transaction-system invariant. *)

Definition conflict_free (future : list action) (tmodcs : gmap nat dbmap) :=
  map_Forall (λ t m, first_commit_compatible future t m) tmodcs.

Definition conflict_past (past future : list action) (tmodas : gmap nat tcform) :=
  map_Forall (λ t m, conflict_cases past future t m) tmodas.

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

Definition wrsm_dbmap (wrsm : gmap nat (option dbmap)) :=
  omap id wrsm.

Lemma lookup_wrsm_dbmap_Some wrsm ts wrs :
  wrsm !! ts = Some (Some wrs) ->
  wrsm_dbmap wrsm !! ts = Some wrs.
Proof. intros Hwrsm. by rewrite /wrsm_dbmap lookup_omap Hwrsm /=. Qed.

Lemma wrsm_dbmap_insert_Some wrsm ts wrs :
  wrsm_dbmap (<[ts := Some wrs]> wrsm) = <[ts := wrs]> (wrsm_dbmap wrsm).
Proof. by rewrite /wrsm_dbmap (omap_insert_Some _ _ _ _ wrs). Qed.

Lemma wrsm_dbmap_insert_None wrsm ts :
  wrsm !! ts = None ->
  wrsm_dbmap (<[ts := None]> wrsm) = wrsm_dbmap wrsm.
Proof.
  intros Hnotin.
  rewrite /wrsm_dbmap omap_insert_None; last done.
  rewrite delete_notin; first done.
  by rewrite lookup_omap Hnotin /=.
Qed.

Definition cmtxn_in_past (past : list action) (resm : gmap nat txnres) :=
  map_Forall (λ t m, ActCommit t m ∈ past) (resm_to_tmods resm).

Lemma resm_to_tmods_insert_aborted resm ts :
  resm !! ts = None ∨ resm !! ts = Some ResAborted ->
  resm_to_tmods (<[ts := ResAborted]> resm) = resm_to_tmods resm.
Proof.
  intros Hresm.
  apply map_eq. intros tsx.
  rewrite 2!lookup_omap.
  destruct (decide (tsx = ts)) as [-> | Hne]; last by rewrite lookup_insert_ne.
  by destruct Hresm as [Hresm | Hresm]; rewrite lookup_insert Hresm.
Qed.

Lemma resm_to_tmods_insert_committed resm ts wrs :
  resm_to_tmods (<[ts := ResCommitted wrs]> resm) = <[ts := wrs]> (resm_to_tmods resm).
Proof.
  apply map_eq. intros tsx.
  destruct (decide (tsx = ts)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne; last done.
    by rewrite 2!lookup_omap lookup_insert_ne; last done.
  }
  rewrite lookup_insert.
  by rewrite lookup_omap lookup_insert.
Qed.

Lemma vslice_resm_to_tmods_committed_absent resm ts wrs key :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = None ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm Hwrs.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_committed_present resm ts wrs key value :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = Some value ->
  vslice (resm_to_tmods resm) key !! ts = Some value.
Proof.
  intros Hresm Hwrs.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_aborted resm ts key :
  resm !! ts = Some ResAborted ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_not_terminated resm ts key :
  resm !! ts = None ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Definition incorrect_fcc Qr form :=
  match form with
  | FCC wrs => not (Qr wrs)
  |_ => True
  end.

#[global]
Instance incorrect_fcc_decision Qr {H : ∀ m, Decision (Qr m)} form :
  Decision (incorrect_fcc Qr form).
Proof. destruct form; apply _. Defined.

Section inv.
  Context `{!heapGS Σ}.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition partitioned_tids
    γ (tids : gset nat) (tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform)
    (resm : gmap nat txnres) : iProp Σ :=
    let wcmts := dom tmodcs in
    let wabts := dom tmodas in
    let cmts := dom (resm_to_tmods resm) in
    "Hwcmts" ∷ ([∗ set] tid ∈ wcmts, own_excl_tid γ tid) ∗
    "Hwabts" ∷ ([∗ set] tid ∈ wabts, own_excl_tid γ tid) ∗
    "Hcmts"  ∷ ([∗ set] tid ∈ cmts, own_excl_tid γ tid) ∗
    "%Hfate" ∷ ⌜set_Forall (λ tid, tid ∈ dom resm ∨ tid ∈ wabts ∨ tid ∈ wcmts) tids⌝.

  Lemma elem_of_tmodcs_partitioned_tids γ tids tmodcs tmodas resm tid :
    tid ∈ dom tmodcs ->
    partitioned_tids γ tids tmodcs tmodas resm -∗
    ⌜tid ∉ dom tmodas ∧ ∀ m, resm !! tid ≠ Some (ResCommitted m)⌝.
  Proof.
    iIntros (Hin) "Hpart".
    iNamed "Hpart".
    iDestruct (big_sepS_elem_of with "Hwcmts") as "Hexcl"; first apply Hin.
    iDestruct (excl_tid_not_elem_of with "Hwabts Hexcl") as %Hnotinwa.
    iDestruct (excl_tid_not_elem_of with "Hcmts Hexcl") as %Hnotinc.
    iPureIntro.
    split; first apply Hnotinwa.
    intros m Hcmt.
    by rewrite not_elem_of_dom /resm_to_tmods lookup_omap Hcmt /= in Hnotinc.
  Qed.

  Lemma elem_of_tmodas_partitioned_tids γ tids tmodcs tmodas resm tid :
    tid ∈ dom tmodas ->
    partitioned_tids γ tids tmodcs tmodas resm -∗
    ⌜tid ∉ dom tmodcs ∧ ∀ m, resm !! tid ≠ Some (ResCommitted m)⌝.
  Proof.
    iIntros (Hin) "Hpart".
    iNamed "Hpart".
    iDestruct (big_sepS_elem_of with "Hwabts") as "Hexcl"; first apply Hin.
    iDestruct (excl_tid_not_elem_of with "Hwcmts Hexcl") as %Hnotinwc.
    iDestruct (excl_tid_not_elem_of with "Hcmts Hexcl") as %Hnotinc.
    iPureIntro.
    split; first apply Hnotinwc.
    intros m Hcmt.
    by rewrite not_elem_of_dom /resm_to_tmods lookup_omap Hcmt /= in Hnotinc.
  Qed.

  Lemma elem_of_committed_partitioned_tids γ tids tmodcs tmodas resm tid :
    (∃ m, resm !! tid = Some (ResCommitted m)) ->
    partitioned_tids γ tids tmodcs tmodas resm -∗
    ⌜tid ∉ dom tmodcs ∧ tid ∉ dom tmodas⌝.
  Proof.
    iIntros (Hm) "Hpart".
    destruct Hm as [m Hm].
    iNamed "Hpart".
    assert (Hin : tid ∈ dom (resm_to_tmods resm)).
    { by rewrite elem_of_dom /resm_to_tmods lookup_omap Hm /=. }
    iDestruct (big_sepS_elem_of with "Hcmts") as "Hexcl"; first apply Hin.
    iDestruct (excl_tid_not_elem_of with "Hwcmts Hexcl") as %Hnotinwc.
    iDestruct (excl_tid_not_elem_of with "Hwabts Hexcl") as %Hnotinwa.
    done.
  Qed.

  Definition past_action_witness γ (a : action) : iProp Σ :=
    match a with
    | ActCommit ts wrs => [∗ set] key ∈ dom wrs, is_cmtd_hist_length_lb γ key (S ts)
    | ActRead ts key => is_cmtd_hist_length_lb γ key ts
    | _ => True
    end.

  #[global]
  Instance past_action_witness_persistent γ a :
    Persistent (past_action_witness γ a).
  Proof. destruct a; apply _. Qed.

  Definition all_prepared γ ts wrs : iProp Σ :=
    is_txn_wrs γ ts wrs ∗
    [∗ set] gid ∈ ptgroups (dom wrs), is_group_prepared γ gid ts.

  Definition some_aborted γ ts : iProp Σ :=
    ∃ gid wrs, is_group_unprepared γ gid ts ∗
               is_txn_wrs γ ts wrs ∗
               ⌜gid ∈ ptgroups (dom wrs)⌝.

  Definition correct_wrs γ ts wrs : iProp Σ :=
    ∃ Q, is_txn_postcond γ ts Q ∗ ⌜Q wrs⌝.

  Definition incorrect_wrs γ ts wrs : iProp Σ :=
    ∃ Q, is_txn_postcond γ ts Q ∗ ⌜not (Q wrs)⌝.

  Definition incorrect_wrs_in_fcc γ ts form : iProp Σ :=
    match form with
    | FCC wrs => incorrect_wrs γ ts wrs
    |_ => True
    end.

  #[global]
  Instance incorrect_wrs_in_fcc_persistent γ ts form :
    Persistent (incorrect_wrs_in_fcc γ ts form).
  Proof. destruct form; apply _. Qed.

  Lemma correct_incorrect_wrs γ ts wrs :
    correct_wrs γ ts wrs -∗
    incorrect_wrs γ ts wrs -∗
    False.
  Proof.
    iIntros "(%pos & Hpos & %Hpos) (%neg & Hneg & %Hneg)".
    iDestruct (txn_postcond_agree with "Hpos Hneg") as %->.
    done.
  Qed.

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts wrs
    | ResAborted => some_aborted γ ts ∨ is_txn_canceled_wrs γ ts
    end.

  #[global]
  Instance valid_res_persistent γ ts res :
    Persistent (valid_res γ ts res).
  Proof. destruct res; apply _. Qed.
  
  Lemma all_prepared_some_aborted γ ts wrs :
    all_prepared γ ts wrs -∗
    some_aborted γ ts -∗
    False.
  Proof.
    iIntros "[Hwrs Hps] Habt".
    iDestruct "Habt" as (gid wrsa) "(Hnp & Hwrsa & %Hgid)".
    iDestruct (txn_wrs_agree with "Hwrs Hwrsa") as %->.
    iDestruct (big_sepS_elem_of with "Hps") as "Hp"; first apply Hgid.
    by iDestruct (group_prep_agree with "Hp Hnp") as %Hcontra.
  Qed.

  Lemma all_prepared_is_txn_canceled_wrs γ ts wrs :
    all_prepared γ ts wrs -∗
    is_txn_canceled_wrs γ ts -∗
    False.
  Proof.
    iIntros "[Hwrs Hps] Hccl".
    by iDestruct (txn_oneshot_wrs_agree with "Hwrs Hccl") as %Hcontra.
  Qed.

  Lemma all_prepared_valid_res_aborted γ ts wrs :
    all_prepared γ ts wrs -∗
    valid_res γ ts ResAborted -∗
    False.
  Proof.
    iIntros "Hprep [Habt | Hccl]".
    - iApply (all_prepared_some_aborted with "Hprep Habt").
    - iApply (all_prepared_is_txn_canceled_wrs with "Hprep Hccl").
  Qed.

  Definition txnsys_inv_no_ts_no_future γ ts future : iProp Σ :=
    ∃ (tids tidas : gset nat) (past : list action)
      (tmods tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform) (posts : gmap nat (dbmap -> Prop))
      (resm : gmap nat txnres) (wrsm : gmap nat (option dbmap)) (ctm : gmap nat (gset u64)),
      (* witnesses of txn linearization *)
      "Htxnsl" ∷ own_lnrz_tids γ tids ∗
      (* exclusive transaction IDs *)
      "Hexcl"  ∷ own_excl_tids γ tids ∗
      "Hpart"  ∷ partitioned_tids γ tids tmodcs tmodas resm ∗
      (* transactions predicted to commit or has committed *)
      "Htidcs" ∷ own_cmt_tmods γ tmods ∗
      (* transactions predicted to abort *)
      "Htidas" ∷ own_wabt_tids γ tidas ∗
      (* transaction post-conditions *)
      "Hpost"  ∷ own_txn_postconds γ posts ∗
      (* transaction result map *)
      "Hresm"  ∷ own_txn_resm γ resm ∗
      (* transaction write-set map *)
      "Hwrsm"  ∷ own_txn_oneshot_wrsm γ wrsm ∗
      (* transaction client tokens *)
      "Hctm"   ∷ own_txn_client_tokens γ ctm ∗
      (* key modifications *)
      "Hkmodls" ∷ ([∗ set] key ∈ keys_all, own_lnrz_kmod_half γ key (vslice tmodcs key)) ∗
      "Hkmodcs" ∷ ([∗ set] key ∈ keys_all, own_cmtd_kmod_half γ key (vslice (resm_to_tmods resm) key)) ∗
      (* safe commit/abort invariant *)
      "#Hvr"    ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* post-conditions hold on the write-set map *)
      "#Hcwrs"  ∷ ([∗ map] tid ↦ wrs ∈ (wrsm_dbmap wrsm), correct_wrs γ tid wrs) ∗
      (* post-conditions not hold on the write set for the FCC case *)
      "#Hiwrs"  ∷ ([∗ map] tid ↦ form ∈ tmodas, incorrect_wrs_in_fcc γ tid form) ∗
      (* past action witnesses *)
      "#Hpas"   ∷ ([∗ list] a ∈ past, past_action_witness γ a) ∗
      (* pure constraints on states *)
      "%Htsge"   ∷ ⌜ge_all ts tids⌝ ∗
      "%Hintids" ∷ ⌜dom tmods ⊆ tids ∧ tidas ⊆ tids⌝ ∗
      "%Htidcs"  ∷ ⌜map_Forall (λ t m, tmodcs !! t = Some m ∨
                                       resm !! t = Some (ResCommitted m)) tmods⌝ ∗
      "%Htidas"  ∷ ⌜dom tmodas = tidas⌝ ∗
      "%Hdomq"   ∷ ⌜dom posts = tids⌝ ∗
      "%Hdomw"   ∷ ⌜dom wrsm = tids⌝ ∗
      "%Hdomctm" ∷ ⌜dom ctm = tids⌝ ∗
      "%Hcmtxn"  ∷ ⌜cmtxn_in_past past resm⌝ ∗
      "%Hwrsm"   ∷ ⌜map_Forall (λ tid wrs, valid_ts tid ∧ valid_wrs wrs) (wrsm_dbmap wrsm)⌝ ∗
      "%Hnz"     ∷ ⌜nz_all (dom tmodcs)⌝ ∗
      "%Hcf"     ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"     ∷ ⌜conflict_past past future tmodas⌝.

  Definition txnsys_inv_no_future γ future : iProp Σ :=
    ∃ (ts : nat),
      (* largest assigned timestamp *)
      "Hts"     ∷ own_largest_ts γ ts ∗
      "Htxnsys" ∷ txnsys_inv_no_ts_no_future γ ts future.

  Definition txnsys_inv_with_future_no_ts γ p ts future : iProp Σ :=
    (* prophecy variable *)
    "Hproph"  ∷ own_txn_proph p future ∗
    "Htxnsys" ∷ txnsys_inv_no_ts_no_future γ ts future.

  Definition txnsys_inv γ p : iProp Σ :=
    ∃ (ts : nat) (future : list action),
      (* largest assigned timestamp *)
      "Hts"     ∷ own_largest_ts γ ts ∗
      (* prophecy variable *)
      "Hproph"  ∷ own_txn_proph p future ∗
      "Htxnsys" ∷ txnsys_inv_no_ts_no_future γ ts future.

  Lemma txnsys_inv_expose_future_extract_ts γ p :
    txnsys_inv γ p -∗
    ∃ future ts, txnsys_inv_with_future_no_ts γ p ts future ∗ own_largest_ts γ ts.
  Proof. iIntros "Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

  Lemma txnsys_inv_extract_future γ p :
    txnsys_inv γ p -∗
    ∃ future, own_txn_proph p future ∗ txnsys_inv_no_future γ future.
  Proof. iIntros "Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

  Lemma txnsys_inv_merge_future γ p future :
    own_txn_proph p future -∗
    txnsys_inv_no_future γ future -∗
    txnsys_inv γ p.
  Proof. iIntros "Hproph Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

End inv.
