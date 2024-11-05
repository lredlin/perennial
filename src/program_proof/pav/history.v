From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import client core.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition lat_pk_comm_reln (lat_pk : lat_val_ty) (lat_comm : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_comm with
  | Some (ep0, pk), Some (ep1, comm) =>
    "%Heq_ep" ∷ ⌜ ep0 = ep1 ⌝ ∗
    "#His_comm" ∷ is_comm pk comm
  | None, None => True
  | _, _ => False
  end.

Definition msva_core_aux (m : adtr_map_ty) uid (vals : list opaque_map_val_ty) : iProp Σ :=
  "%Hlt_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  (∀ (ver : w64) val,
    "%Hlook_ver" ∷ ⌜ vals !! (uint.nat ver) = Some val ⌝ -∗
    ∃ label,
    ("#His_label" ∷ is_vrf uid ver label ∗
    "%Hin_map" ∷ ⌜ m !! label = Some val ⌝)).

Definition msva_core m uid vals : iProp Σ :=
  ∃ label,
  "#Hmsv_aux" ∷ msva_core_aux m uid vals ∗
  "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
  "%Hnin_next" ∷ ⌜ m !! label = None ⌝.

Lemma msva_core_aux_snoc m uid l x :
  "#Hmsv_aux" ∷ msva_core_aux m uid (l ++ [x]) -∗
  (∃ label,
  "#Hmsv_aux" ∷ msva_core_aux m uid l ∗
  "#His_label" ∷ is_vrf uid (W64 $ length l) label ∗
  "%Hin_lat" ∷ ⌜ m !! label = Some x ⌝).
Proof.
  iNamed 1. iNamed "Hmsv_aux". rewrite app_length in Hlt_vals. list_simplifier.
  iDestruct ("Hmsv_aux" $! (W64 $ length l) with "[]") as "Hlat".
  { rewrite nat_thru_w64_id; [|lia]. iPureIntro. apply lookup_snoc. }
  iNamed "Hlat". iFrame "#%". iSplit. { iPureIntro. lia. }
  iIntros "*". iNamed 1. iSpecialize ("Hmsv_aux" with "[]").
  { iPureIntro. rewrite lookup_app_l; [exact Hlook_ver|by eapply lookup_lt_Some]. }
  iFrame "#".
Qed.

Lemma msva_core_aux_agree m uid vals0 vals1 :
  ("#Hmsv_aux0" ∷ msva_core_aux m uid vals0 ∗
  "#Hmsv_aux1" ∷ msva_core_aux m uid vals1 ∗
  "%Heq_len" ∷ ⌜ length vals0 = length vals1 ⌝) -∗
  ⌜ vals0 = vals1 ⌝.
Proof.
  revert vals1. induction vals0 as [|x0 l0 IH] using rev_ind;
    destruct vals1 as [|x1 l1 _] using rev_ind; iNamed 1.
  - done.
  - rewrite length_app/= in Heq_len. lia.
  - rewrite length_app/= in Heq_len. lia.
  - rewrite !length_app/= in Heq_len.
    iRename "Hmsv_aux0" into "HM0". iRename "Hmsv_aux1" into "HM1".
    iDestruct (msva_core_aux_snoc with "HM0") as "H". iNamedSuffix "H" "0".
    iDestruct (msva_core_aux_snoc with "HM1") as "H". iNamedSuffix "H" "1".
    assert (length l0 = length l1) as HT by lia.
    iEval (rewrite HT) in "His_label0". clear HT.
    iDestruct (is_vrf_func (_, _) with "His_label0 His_label1") as %->.
    simplify_map_eq/=. specialize (IH l1).
    iDestruct (IH with "[$Hmsv_aux0 $Hmsv_aux1]") as %->. { iPureIntro. lia. }
    naive_solver.
Qed.

Lemma msva_core_len_agree_aux m uid vals0 vals1 :
  ("#Hmsv0" ∷ msva_core m uid vals0 ∗
  "#Hmsv1" ∷ msva_core m uid vals1 ∗
  "%Hlt_len" ∷ ⌜ length vals0 < length vals1 ⌝) -∗
  False.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1". iNamed "Hmsv_aux1".
  list_elem vals1 (uint.nat (length vals0)) as val.
  iSpecialize ("Hmsv_aux1" with "[]"). { iPureIntro. exact Hval_lookup. }
  iNamed "Hmsv_aux1".
  iDestruct (is_vrf_func (_, _) with "His_label0 His_label") as %->.
  naive_solver.
Qed.

Lemma msva_core_len_agree m uid vals0 vals1 :
  ("#Hmsv0" ∷ msva_core m uid vals0 ∗
  "#Hmsv1" ∷ msva_core m uid vals1) -∗
  ⌜ length vals0 = length vals1 ⌝.
Proof.
  iNamed 1. destruct (decide (length vals0 = length vals1)) as [?|?]; [done|iExFalso].
  destruct (decide (length vals0 < length vals1)) as [?|?].
  - iApply (msva_core_len_agree_aux _ _ vals0 vals1 with "[]").
    iFrame "Hmsv0 Hmsv1". iPureIntro. lia.
  - iApply (msva_core_len_agree_aux _ _ vals1 vals0 with "[]").
    iFrame "Hmsv1 Hmsv0". iPureIntro. lia.
Qed.

Lemma msva_core_agree m uid vals0 vals1 :
  ("#Hmsv0" ∷ msva_core m uid vals0 ∗
  "#Hmsv1" ∷ msva_core m uid vals1) -∗
  ⌜ vals0 = vals1 ⌝.
Proof.
  iNamed 1. iApply msva_core_aux_agree.
  iPoseProof "Hmsv0" as "Hmsv0'". iPoseProof "Hmsv1" as "Hmsv1'".
  iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1". iFrame "#".
  iApply msva_core_len_agree. iFrame "Hmsv0' Hmsv1'".
Qed.

Definition msv_final (adtr_γ : gname) (ep uid : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (m : adtr_map_ty) (vals : list opaque_map_val_ty),
  "%Hlen_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  "#Hcomm_reln" ∷ lat_pk_comm_reln lat (last vals) ∗
  "#Hmap" ∷ mono_list_idx_own adtr_γ (uint.nat ep) m ∗
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#His_label" ∷ is_vrf uid (W64 ver) label ∗
    "%Hin_map" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#Hbound" ∷
    (∃ label,
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
    "%Hnin_map" ∷ ⌜ m !! label = None ⌝).

Lemma msv_final_agree γ ep uid lat0 lat1 :
  ("#Hmsv0" ∷ msv_final γ ep uid lat0 ∗
  "#Hmsv1" ∷ msv_final γ ep uid lat1) -∗
  ⌜ lat0 = lat1 ⌝.
Proof.
  iNamed 1. iNamedSuffix "Hmsv0" "0". iNamedSuffix "Hmsv1" "1".
  iDestruct (mono_list_idx_agree with "Hmap0 Hmap1") as %->.
  iClear "Hmap0 Hmap1".
  iDestruct (msva_core_agree with "[]") as %->; [iSplit|].
  { iNamed "Hbound0". iFrame "#%". iClear "His_label". iIntros "*". iNamed 1.
    iDestruct (big_sepL_lookup with "Hhist0") as "H"; [exact Hlook_ver|].
    iNamed "H". iEval (rewrite w64_to_nat_id) in "His_label". iFrame "#%". }
  { iNamed "Hbound1". iFrame "#%". iClear "His_label". iIntros "*". iNamed 1.
    iDestruct (big_sepL_lookup with "Hhist1") as "H"; [exact Hlook_ver|].
    iNamed "H". iEval (rewrite w64_to_nat_id) in "His_label". iFrame "#%". }
  destruct lat0 as [[??]|], lat1 as [[??]|], (last vals0) as [[??]|]; [|done..].
  iNamedSuffix "Hcomm_reln0" "0". iNamedSuffix "Hcomm_reln1" "1".
  iDestruct (is_comm_inj with "His_comm0 His_comm1") as %->. naive_solver.
Qed.

(* TODO: add inv that says every key in cli submap will have a vrf. *)
Definition know_hist_val_cliG cli_γ (uid ep : w64) (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  ∃ (vals : list opaque_map_val_ty),
  "#Hpk_comm_reln" ∷
    ([∗ list] pk_val;comm_val ∈ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist;vals,
    "%Heq_ep" ∷ ⌜ pk_val.1 = comm_val.1⌝ ∗
    "#Hcomm" ∷ is_comm pk_val.2 comm_val.2) ∗
  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷
    ([∗ list] ver ↦ '(prior, comm) ∈ vals,
    ∃ dig m_γ label,
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
    "#Hin_prior" ∷ (uid, W64 ver) ↪[m_γ]□ Some (prior, comm) ∗
    "#His_label" ∷ is_vrf uid (W64 ver) label) ∗
  "#Hbound" ∷
    (∃ (bound : w64) dig m_γ label,
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
    "%Hlt_bound" ∷ ⌜ uint.Z bound ≤ uint.Z valid ⌝ ∗
    (* next ver doesn't exist in this or later map. *)
    (("%Hgt_bound" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
    "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ None)
    ∨
    (* next ver exists in later map. *)
    (∃ comm,
    "%Hgt_bound" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
    "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ Some (bound, comm)))).

Definition know_hist_cliG cli_γ (uid : w64) (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  "%Hok_valid" ∷ ⌜ ∀ i ep pk, hist !! i = Some (ep, pk) →
    uint.Z ep ≤ uint.Z valid ⌝ ∗
  "#Hknow_vals" ∷ (∀ (ep : w64), ⌜ uint.Z ep ≤ uint.Z valid ⌝ -∗
    know_hist_val_cliG cli_γ uid ep hist valid).

Definition own_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.1 ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist cli_γ uid sl_hist hist valid : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, own_HistEntry p o) ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid.
End defs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

(* TODO: upstream. *)
Lemma list_filter_iff_strong {A} (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ i x, l !! i = Some x → (P1 x ↔ P2 x)) →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction l as [|a l IH]; [done|].
  opose proof (HPiff 0%nat a _) as ?; [done|].
  ospecialize (IH _). { intros i x ?. by ospecialize (HPiff (S i) x _). }
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True; [|by naive_solver..]. by rewrite IH.
  - rewrite !filter_cons_False; [|by naive_solver..]. by rewrite IH.
Qed.

(* TODO: upstream. *)
Lemma list_filter_all {A} (P : A → Prop)
    `{!∀ x, Decision (P x)} (l : list A) :
  (∀ i x, l !! i = Some x → P x) →
  filter P l = l.
Proof.
  intros HP. induction l as [|a l IH]; [done|].
  opose proof (HP 0%nat a _) as ?; [done|].
  ospecialize (IH _). { intros i x ?. by ospecialize (HP (S i) x _). }
  rewrite filter_cons_True; [|done]. by rewrite IH.
Qed.

Lemma hist_val_extend_valid γ uid ep hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  know_hist_val_cliG γ uid ep hist valid -∗
  know_hist_val_cliG γ uid ep hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hbound". iExists vals. iFrame "#".
  iDestruct "Hbound" as "[Hbound|Hbound]"; iNamed "Hbound"; iPureIntro; word.
Qed.

Lemma hist_extend_selfmon cli_γ uid hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid ∗
  "#His_bound" ∷ is_my_bound cli_γ uid (W64 $ length hist) new_valid) -∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hknow_hist". iSplit.
  { iIntros (??? Hlook) "!%". specialize (Hok_valid _ _ _ Hlook). word. }
  iIntros (ep ?). destruct (decide (uint.Z ep ≤ uint.Z valid)).
  { iSpecialize ("Hknow_vals" $! ep with "[]"). { iPureIntro. word. }
    iApply (hist_val_extend_valid with "Hknow_vals"). word. }
  iSpecialize ("Hknow_vals" $! valid with "[]"). { iPureIntro. lia. }
  iNamed "Hknow_vals". iExists vals. iSplit; [|iSplit].
  - rewrite (list_filter_iff_strong
      (λ x, uint.Z x.1 ≤ uint.Z ep)
      (λ x, uint.Z x.1 ≤ uint.Z valid) hist); last first.
    { intros ?[??] Hlook. ospecialize (Hok_valid _ _ _ Hlook).
      naive_solver word. }
    iFrame "#".
  - iFrame "#".
  - iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_comm_reln") as %Hlen_vals.
    rewrite list_filter_all in Hlen_vals; last first.
    { intros ?[??] Hlook. ospecialize (Hok_valid _ _ _ Hlook). simpl. word. }
    iNamed "His_bound". rewrite Hlen_vals. by iFrame "#%".
Qed.

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

Lemma hist_audit_msv cli_γ uid hist valid adtr_γ aud_ep (ep : w64) :
  uint.Z ep ≤ uint.Z valid →
  uint.Z valid < uint.Z aud_ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  "#Hmsv" ∷ msv_final adtr_γ ep uid (get_lat hist ep).
Proof.
  intros ??. iNamed 1.
  iNamed "Hknow_hist". iSpecialize ("Hknow_vals" $! ep with "[//]").
  iDestruct "His_audit" as (ms) "His_audit". iNamed "His_audit".
  list_elem ms (uint.nat ep) as m.
  iDestruct (mono_list_idx_own_get _ _ Hm_lookup with "Hadtr_maps") as "Hadtr_map".
  iFrame "Hadtr_map".
  iDestruct "Hknow_vals" as (vals) "Hknow_vals". iExists vals.
  iNamed "Hknow_vals". iSplit; [|iSplit].
  - iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_comm_reln") as %Hlen_vals.
    destruct (get_lat hist ep) as [[??]|] eqn:Hlat_pk, (last vals) as [[??]|] eqn:Hlat_comm;
      [|exfalso..|done];
      rewrite /get_lat last_lookup in Hlat_pk; rewrite last_lookup in Hlat_comm.
    + rewrite Hlen_vals in Hlat_pk.
      iDestruct (big_sepL2_lookup with "Hpk_comm_reln") as "?"; [exact Hlat_pk|exact Hlat_comm|].
      iFrame "#".
    + apply lookup_lt_Some in Hlat_pk. apply lookup_ge_None in Hlat_comm. lia.
    + apply lookup_ge_None in Hlat_pk. apply lookup_lt_Some in Hlat_comm. lia.
  - iClear "Hbound".
    iApply (big_sepL_impl with "Hhist"). iIntros (?[prior ?]) "!> %Hlook_vals". iNamed 1. iFrame "#".
    (* tedious: trace prior ep back to filtered hist to get filter bound on it. *)
    iDestruct (big_sepL2_lookup_2_some with "Hpk_comm_reln") as %[[??] Hlook_hist]; [exact Hlook_vals|].
    iDestruct (big_sepL2_lookup with "Hpk_comm_reln") as "Htmp"; [exact Hlook_hist|exact Hlook_vals|].
    iNamed "Htmp". opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup. eauto using Hlook_hist. }
    simpl in *. list_elem ms (uint.nat prior) as mprior.
    iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_prior $His_label]") as "Htmp".
    { iPureIntro. exact Hmprior_lookup. }
    iNamed "Htmp". iPureIntro.
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    by eapply lookup_weaken.
  - iClear "Hhist". iNamed "Hbound". iFrame "#".
    list_elem ms (uint.nat bound) as mbound.
    iDestruct "Hbound" as "[Hbound|Hbound]"; iNamed "Hbound".
    + iSpecialize ("Hmap_transf" with "[$Hsubmap $Hin_bound $His_label]").
      { iPureIntro. exact Hmbound_lookup. }
      iNamed "Hmap_transf". iPureIntro.
      opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      by eapply lookup_weaken_None.
    + iSpecialize ("Hmap_transf" with "[$Hsubmap $Hin_bound $His_label]").
      { iPureIntro. exact Hmbound_lookup. }
      iNamed "Hmap_transf". iPureIntro.
      destruct (decide $ is_Some $ m !! label) as [[? Hlook_mkey]|]; last first.
      { by eapply eq_None_not_Some. }
      opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
      opose proof ((proj2 Hinv_adtr) _ _ _ _ _ Hm_lookup Hlook_mkey) as ?. word.
Qed.

End derived.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_put_hist cli_γ uid sl_hist hist ptr_e e :
  match last hist with
  | None => True
  | Some lat => uint.Z lat.1 < uint.Z e.1
  end →
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist ∗
    "Hown_entry" ∷ own_HistEntry ptr_e e ∗
    "#His_key" ∷ is_my_key cli_γ uid (W64 $ length hist) e.1 e.2
  }}}
  SliceAppend ptrT (slice_val sl_hist) #ptr_e
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist' (hist ++ [e]) ∗
    "Hown_entry" ∷ own_HistEntry ptr_e e
  }}}.
Proof. Admitted.

Lemma wp_GetHist cli_γ uid sl_hist hist (ep : w64) :
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist
  }}}
  GetHist (slice_val sl_hist) #ep
  {{{
    (is_reg : bool) sl_pk pk, RET (#is_reg, slice_val sl_pk);
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match get_lat hist ep with
        | None => is_reg = false
        | Some lat => is_reg = true ∧ pk = lat.2
        end ⌝
  }}}.
Proof. Admitted.

End wps.
