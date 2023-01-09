From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_apply_proof.

Context `{!heapGS Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

(* Clerk specs *)
Lemma wp_Clerk__ApplyAsBackup γ γsrv ck args_ptr (epoch index:u64) opsfull op op_sl op_bytes :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch opsfull ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch opsfull ∗
        "%Hghost_op_σ" ∷ ⌜∃ γ, last opsfull = Some (rw_op op, γ)⌝ ∗
        "%Hghost_op_op" ∷ ⌜has_op_encoding op_bytes op⌝ ∗
        "%Hσ_index" ∷ ⌜length (get_rwops opsfull) = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op_bytes)
  }}}
    Clerk__ApplyAsBackup #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch opsfull
                             else True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_apply (ApplyAsBackupArgs.wp_Encode with "[]").
  {
    instantiate (1:=(ApplyAsBackupArgs.mkC _ _ _)).
    iExists _; iFrame "#".
  }
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_host_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[$ _]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold SetState_spec.
    destruct Hghost_op_σ as [? Hghost_op_σ].
    iExists _, _, _, _.
    iSplitR; first done.
    iFrame "#%".
    iSplit.
    { (* No error from RPC, Apply was accepted *)
      iIntros "#Hacc_lb".
      iIntros (?) "%Henc_rep Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.

      (* FIXME: separate lemma *)
      wp_call.
      rewrite Henc_rep.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iModIntro.
      iFrame "#".
    }
    { (* Apply was rejected by the server (e.g. stale epoch number) *)
      iIntros (err) "%Herr_nz".
      iIntros.
      wp_pures.
      wp_load.
      wp_call.
      rewrite H.
      wp_apply (wp_ReadInt with "[$]").
      iIntros.
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iFrame.
      iModIntro.
      destruct (decide _).
      {
        exfalso. done.
      }
      {
        done.
      }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      destruct (decide (_)).
      { exfalso. done. }
      { done. }
    }
    { exfalso. done. }
  }
Qed.


Lemma accept_helper opsfull opsfull_old op (γ:gname) :
  (prefix opsfull opsfull_old ∨ prefix opsfull_old opsfull) →
  last opsfull = Some (rw_op op, γ) →
  length (get_rwops opsfull) = length (get_rwops opsfull_old) + 1 →
  get_rwops opsfull_old ++ [op] = get_rwops opsfull ∧
  prefix opsfull_old opsfull.
Proof.
Admitted.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv args opsfull op Q Φ Ψ :
  is_Server s γ γsrv -∗
  ApplyAsBackupArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  ApplyAsBackup_core_spec γ γsrv args opsfull op Q Ψ -∗
  WP pb.Server__ApplyAsBackup #s #args_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre HΦ HΨ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  wp_pures.

  (* for loop to wait for previous op to be applied *)
  wp_bind (For _ _ _).
  wp_forBreak_cond.
  wp_pures.

  iNamed "Hown".

  wp_loadField.
  wp_bind (If (_ > _) _ _).
  wp_apply (wp_wand with "[Hargs_index HnextIndex Hargs_epoch Hepoch]").
  {
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    {
      wp_loadField.
      wp_loadField.
      wp_pures.
      iModIntro.
      instantiate (1:=(λ v, ("%Hisbool" ∷ ⌜v = #true ∨ v = #false⌝ ∗ _))%I).
      simpl.
      iSplitR.
      { iPureIntro. destruct bool_decide; naive_solver. }
      iNamedAccu.
    }
    {
      iFrame.
      iPureIntro.
      by right.
    }
  }
  iIntros (?).
  iNamed 1.
  wp_bind (If v _ #false).
  wp_apply (wp_wand with "[Hsealed]").
  {
    wp_pures.
    destruct Hisbool as [-> | ->].
    {
      wp_pures.
      wp_loadField.
      wp_pures.
      instantiate (1:=(λ w, ("%Hisboolw" ∷ ⌜w = #true ∨ w = #false⌝ ∗ _))%I).
      simpl.
      iModIntro.
      iSplitR.
      { iPureIntro. destruct sealed; naive_solver. }
      iNamedAccu.
    }
    {
      wp_pures.
      iSplitR.
      { iPureIntro. naive_solver. }
      by iFrame.
    }
  }

  iIntros (?).
  iNamed 1.
  wp_pures.
  destruct Hisboolw as [-> | ->].
  { (* loop again *)
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapGet with "HopAppliedConds_map").
    iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
    wp_pures.
    wp_if_destruct.
    { (* no condvar exists, let's make one *)
      wp_loadField.
      wp_apply (wp_newCond with "[$HmuInv]").
      apply map_get_false in Hlookup as [Hlookup _].
      clear dependent cond.
      iIntros (cond) "#Hiscond".
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapInsert with "HopAppliedConds_map").
      { done. }
      iIntros "HopAppliedConds_map".
      wp_pures.
      iLeft.

      (* PERF *)
      (* iFrame. is much slower than listing the specific hypotheses to frame *)
      iFrame "Hargs_op Hargs_op_sl Hargs_epoch Hargs_index HΨ HΦ Hlocked".
      iSplitR; first done.
      iModIntro.
      iApply to_named.
      repeat (iExists _).

      (* Q: what about a tactic that looks for names in the goal, and iFrames those in order? *)
      (* PERF. The three iFrames is faster than one. *)
      (* time iFrame "∗#%". *)
      time (iFrame "∗"; iFrame "#"; iFrame "%").

      unfold typed_map.map_insert.
      iDestruct (big_sepM_insert with "[$HopAppliedConds_conds]") as "$".
      { done. }
      { iFrame "#". }
    }
    { (* condvar exists, let's wait *)
      apply map_get_true in Hlookup.
      iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[His_cond _]".
      { done. }
      wp_apply (wp_condWait with "[-HΦ HΨ Hargs_op Hargs_op_sl Hargs_index Hargs_epoch]").
      {
        iFrame "His_cond".
        iFrame "HmuInv Hlocked".
        repeat (iExists _).
        (* time iFrame "∗#%". *)
        time (iFrame "∗"; iFrame "#"; iFrame "%").
      }
      iIntros "[Hlocked Hown]".
      wp_pures.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iFrame.
    }
  }
  (* done looping *)
  wp_pures.
  iModIntro.
  iRight.
  iSplitR; first done.
  wp_pures.

  iNamed "HΨ".
  wp_loadField.
  wp_if_destruct.
  { (* return error: sealed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      repeat (iExists _).
      iNext.
      (* time iFrame "∗#%". *)
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_apply (wp_Server__isEpochStale with "Hepoch").
  iIntros "Hepoch".
  wp_if_destruct.
  { (* return error: stale *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "Hlocked HmuInv".
      iNext.
      repeat (iExists _).
      (* time iFrame "∗ # %". *)
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iRight in "HΨ".
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }
  replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
  wp_loadField.
  wp_loadField.
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* return error: out-of-order; TODO: we never actually need to return this
       error, if something is out of order that means we already applied it *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "Hlocked HmuInv".
      iNext.
      repeat (iExists _).
      time (iFrame "∗"; iFrame "#"; iFrame "%").
      (* time iFrame "∗ # %". *)
    }
    wp_pures.
    iApply "HΦ".
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_loadField.

  iAssert (_) with "HisSm" as "HisSm2".
  iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm2".
  iNamed "HisSm2".

  iDestruct "Heph_prop_lb" as "#Heph_prop_lb".
  iAssert ((|NC={⊤,⊤}=> ∃ (new_opsfull_ephemeral:list (GhostOpType * gname)),
           ⌜new_opsfull_ephemeral = opsfull ∨ new_opsfull_ephemeral = opsfull_ephemeral⌝ ∗
           wpc_nval ⊤
             (own_StateMachine args.(ApplyAsBackupArgs.epoch) ops false
                (own_Server_ghost γ γsrv γeph) ∗
                ((own_ephemeral_proposal γeph args.(ApplyAsBackupArgs.epoch) new_opsfull_ephemeral ∗
                is_ephemeral_proposal_lb γeph args.(ApplyAsBackupArgs.epoch) opsfull)) )

           )%I) with "[Heph Hstate Hlc]" as "HH".
  {
  (* Want to establish:
     is_ephemeral_proposal_lb γeph args.(ApplyAsBackupArgs.epoch) opsfull
     This requires us to know that opsfull_ephemeral ⪯ opsfull.
     We will establish this using accP.
   *)
    destruct isPrimary.
    { (* case: is primary. *)
      iAssert (_) with "HprimaryOnly" as "Hprim2".
      iEval (rewrite /is_possible_Primary /tc_opaque) in "Hprim2".
      iExists opsfull_ephemeral.
      iSplitR.
      { iPureIntro. by right. }
      iMod ("HaccP" with "Hlc [Heph] Hstate") as "$"; last first.
      {
        (* PERF *)
        (* time done. *) (* takes 5 seconds*)
        (* time (iModIntro; done). *) (* takes 0.2 seconds, still a lot longer than below *)
        time (iModIntro; iApply True_intro; iAccu). }.
      iIntros (???) "Hghost".
      iNamed "Hghost".
      iNamed "Hprim2".
      iDestruct (ghost_propose_lb_valid with "Htok_used_witness Hprim Hprop_lb") as %Hvalid.
      iSplitL "Hghost Hprim".
      { iModIntro. iExists _. iFrame "∗#%". }
      iModIntro.
      iFrame "Heph".
      iApply (own_mono with "Heph_lb").
      apply singleton_mono.
      apply mono_list_lb_mono.
      done.
    }
    { (* case: not primary *)
      iDestruct (own_valid_2 with "Heph_prop_lb Hprop_lb") as %Hcomp.
      rewrite singleton_op singleton_valid in Hcomp.
      rewrite csum.Cinr_valid in Hcomp.
      apply mono_list_lb_op_valid_L in Hcomp.
      destruct Hcomp as [Hprefix|Hprefix].
      2:{ (* case: opsfull_ephemeral ⪯ opsfull; no need to do any update at all *)
        iExists _.
        iSplitR.
        { iPureIntro. by right. }
        iDestruct (own_mono _ _ {[ args.(ApplyAsBackupArgs.epoch) := ◯ML (opsfull_ephemeral: list (leibnizO _)) ]} with "Heph") as "#Heph_lb2".
        { apply singleton_mono.
          apply mono_list_included.
        }
        iFrame.
        iApply wpc_nval_intro.
        iModIntro. iNext.
        iFrame.
        iApply (own_mono with "Heph_lb2").
        apply singleton_mono.
        apply mono_list_lb_mono.
        done.
      }
      {
        iExists opsfull.
        iMod (own_update with "Heph") as "Heph".
        {
          apply singleton_update.
          apply mono_list_update.
          exact Hprefix.
        }
        iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Heph_lb".
        {
          apply singleton_mono.
          apply mono_list_included.
        }
        iModIntro.
        iSplitR.
        { iPureIntro. by left.  }
        iApply wpc_nval_intro.
        iNext.
        iFrame "∗#".
      }
    }
  }

  iMod "HH" as (?) "[%Hnew_eph HH]".
  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }
  wp_loadField.
  wp_pures.
  iIntros "(Hstate & Heph & #Heph_lb2)".

  iMod (readonly_alloc_1 with "Hargs_op_sl") as "Hargs_op_sl".

  wp_apply ("HapplySpec" with "[$Hstate $Hargs_op_sl]").
  { (* prove protocol step *)
    iSplitL ""; first done.
    iIntros "Hghost".
    iNamed "Hghost".

    (* deal with implicitly accepting RO ops here *)
    rewrite Hre.
    iDestruct (ghost_accept_helper2 with "Hprop_lb Hghost") as "[Hghost %Hcomp]".
    epose proof (accept_helper _ _ _ _ Hcomp Hghost_op_σ) as H.
    eassert _ as H2; last apply H in H2.
    {
      rewrite Hσ_index.
      rewrite -Hre.
      rewrite Hσ_nextIndex.
      word.
    }
    destruct H2 as [HnewOp Hprefix].
    clear H.

    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
    { done. }
    { by apply prefix_length. }
    iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
    { by apply prefix_length. }

    iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb2".
    instantiate (1:=(is_epoch_lb γsrv epoch ∗ is_accepted_lb γsrv epoch opsfull)%I).
    iModIntro.

    iSplitL.
    { iExists _; iFrame "Hghost".
      iFrame "Hprim".
      iFrame "#".
      done.
    }

    replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
    iFrame "#".
  }
  iIntros (reply q waitFn) "(Hreply & Hstate & HwaitSpec)".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HopAppliedConds_map").
  iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
  wp_pures.
  wp_bind (If _ _ _).
  wp_apply (wp_wand with "[HopAppliedConds_map HopAppliedConds HnextIndex]").
  {
    wp_if_destruct.
    { (* map lookup succeeded, signal the condvar *)
      apply map_get_true in Hlookup.
      iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[Hiscond _]".
      { done. }
      wp_apply (wp_condSignal with "Hiscond").
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapDelete with "HopAppliedConds_map").
      iIntros "HopAppliedConds_map".
      simpl.
      iAssert (∃ newOpAppliedConds,
                  is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                  [∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu
              )%I with "[HopAppliedConds_map]" as "H".
      {
        iExists _; iFrame.
        unfold map_del.
        iDestruct (big_sepM_delete with "HopAppliedConds_conds") as "[_ $]".
        { done. }
      }
      (* FIXME: iNamedAccu and iAccu turn the strings into "^@^@^@^@^@..." *)
      instantiate (1:=(λ _, _)%I).
      instantiate (1:=
                  (
        "HopAppliedConds" ∷ s ↦[Server :: "opAppliedConds"] #opAppliedConds_loc ∗
        "HnextIndex" ∷ s ↦[Server :: "nextIndex"] #_ ∗
        "H" ∷ ∃ newOpAppliedConds, (is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                ([∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu))
                )%I
      ).
      iAccu.
    }
    { (* FIXME: What are those weird ^@? *)
      simpl.
      iModIntro.
      iFrame.
      iExists _; iFrame "∗#".
    }
  }
  iIntros (?).
  iNamed 1.
  iDestruct "H" as (?) "[HopAppliedConds_map #HopAppliedConds_conds2]".
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[-HΨ HΦ HwaitSpec Hargs_epoch]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    repeat (iExists _).
    replace ([op]) with ([(op, Q).1]) by done.
    time iFrame "∗#".
    (* time (iFrame "∗"; iFrame "#"). *) (* PERF Not a big difference here because no % *)
    iSplitR.
    {
      iModIntro.
      destruct isPrimary.
      { done. }
      destruct Hnew_eph as [-> | ->].
      { iFrame "#". }
      { iFrame "#". }
    }
    iPureIntro.
    rewrite app_length.
    rewrite Hσ_nextIndex.
    simpl.
    word.
  }
  wp_pures.
  wp_apply "HwaitSpec".
  iIntros "#Hlb".
  wp_pures.

  (* possibly update durableNextIndex *)
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iClear "Hs_epoch_lb HopAppliedConds_conds HdurableNextIndex_is_cond HroOpsToPropose_is_cond".
  iClear "HcommittedNextRoIndex_is_cond Hdurable_lb Heph_prop_lb Hcommit_lb HprimaryOnly HisSm".
  (* FIXME: why doesn't Hdurable_lb get automatically get destructed into Hdurable_lb2? *)

  wp_pures.
  wp_bind  ((if: (if: _ then _ else _) then _ else _)%E).
  wp_apply (wp_wand with "[Hown Hargs_epoch]").
  {
    instantiate (1:= λ _, pb_definitions.own_Server s γ γsrv γeph own_StateMachine mu).
    iNamed "Hown".
    wp_bind (if: struct.loadF _ _ _ = _ then _ else _)%E.
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    {
      wp_loadField.
      wp_if_destruct.
      { (* case: increase durableNextIndex *)
        iDestruct "Hlb" as "[_ Hlb]".
        replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
        wp_storeField.
        wp_loadField.
        wp_apply (wp_condBroadcast with "[]"); first iFrame "#".
        wp_pures.
        wp_loadField.
        wp_loadField.
        wp_bind ((if: #_ = #_ then _ else _)%E).
        wp_if_destruct.
        {
          wp_loadField.
          wp_loadField.
          wp_pures.
          wp_if_destruct.
          {
            wp_loadField.
            wp_apply (wp_condSignal with "[]"); first iFrame "#".
            repeat iExists _.
            (* time iFrame "Hlb ∗ #%". *) (* 11.484 secs *)
            time (iFrame "Hlb ∗ #"; iFrame "%"). (* 8.154 secs *)
            iPureIntro. word.
          }
          {
            repeat iExists _.
            iFrame "∗ Hlb #"; iFrame "%".
            iPureIntro.
            word.
          }
        }
        wp_pures.
        repeat iExists _.
        iFrame "∗ Hlb #"; iFrame "%".
        iPureIntro.
        word.
      }
      {
        repeat iExists _.
        (* time (iFrame "∗#%"). *) (* 11.501 secs *)
        time (iFrame "∗#"; iFrame "%"). (* 7.514 secs*)
        (* time (iFrame "∗"; iFrame "#"; iFrame "%"). *) (* secs *)
        iPureIntro.
        word.
      }
    }
    wp_pures.
    {
      iModIntro.
      repeat iExists _.
      iFrame "∗#"; iFrame "%".
    }
  }

  iIntros (?) "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$HmuInv $Hlocked $Hown]").
  wp_pures.

  iLeft in "HΨ".
  iApply "HΦ".
  iApply "HΨ".
  replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
  iDestruct "Hlb" as "(_ & $)".
  done.
Qed.

End pb_apply_proof.
