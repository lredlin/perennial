From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants ghost_map.
From Perennial.program_logic Require Import weakestpre.

Require Export New.code.sync.
From New.proof Require Import proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Import sync.atomic.
From New.proof Require Import tok_set.

From Perennial Require Import base.

Set Default Proof Using "Type".

Class syncG Σ := {
    #[global] wg_tokG :: tok_setG Σ;
    #[global] wg_totalG :: ghost_varG Σ w32
  }.

Definition syncΣ := #[tok_setΣ; ghost_varΣ w32].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance race_pkg_is_init : IsPkgInit race := ltac2:(build_pkg_init ()).

#[global]
Program Instance pkg_is_init : IsPkgInit sync := ltac2:(build_pkg_init ()).

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hinv" ∷ inv nroot (
        ∃ b : bool,
          (m ↦s[ sync.Mutex :: "state" ]{# 1/4} b) ∗
                  if b then True else
                    m ↦s[sync.Mutex :: "state"]{# 3/4} b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[sync.Mutex :: "state"]{# 3/4} true.

Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %[Hbad _].
  exfalso.
  rewrite go_type_size_unseal in Hbad. naive_solver.
  (* FIXME: don't want to unseal go_type_size_unseal *)
Qed.

Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_Mutex m).
Proof. apply _. Qed.

Lemma struct_val_aux_cons decls f t fvs :
  (struct.val_aux (structT $ (f,t) :: decls) fvs) =
  (default (zero_val t) (alist_lookup_f f fvs), (struct.val_aux (structT decls) fvs))%V.
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma struct_val_aux_nil fvs :
  (struct.val_aux (structT $ []) fvs) = #().
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma flatten_struct_tt :
  flatten_struct (# ()%V) = [].
Proof. rewrite to_val_unseal //=. Qed.

Theorem init_Mutex R E m : is_pkg_init sync -∗ m ↦ (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "#Hi Hl HR".
  simpl.
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".
  simpl.
  iFrame "#".
  iMod (inv_alloc nroot _ (_) with "[Hstate HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hstate".
    iDestruct "Hstate" as "[$$]".
  }
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    m @ sync @ "Mutex'ptr" @ "Lock" #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  wp_start as "H". iNamed "H".
  iLöb as "IH".
  wp_method_call. wp_call.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
    by iApply "IH".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    { done. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    m @ sync @ "Mutex'ptr" @ "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His & Hlocked & HR)".
  iNamed "His".
  wp_bind (CmpXchg _ _ _).
  iInv nroot as (b) "[>Hl _]".

  unfold own_Mutex.
  iCombine "Hl Hlocked" gives %[_ [=]]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
  { econstructor. }
  { econstructor. }
  iIntros "!# Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_auto; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

Definition is_Locker (i : interface.t) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} (interface.get #"Lock" #i) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} (interface.get #"Unlock" #i) #() {{{ RET #(); True }}})
.

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_Mutex m R -∗
  is_Locker (interface.mk sync "Mutex'ptr"%go #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#[? ?]".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_auto.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_pkg_init sync }}}
    sync @ "NewCond" #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_auto.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  iNamed "Hl".
  iPersist "HL".
  iFrame "#". done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Signal" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef Hc]".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    c @ sync @ "Cond'ptr" @ "Broadcast" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    c @ sync @ "Cond'ptr" @ "Wait" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(#Hcond & #Hlock & HR)".
  iNamed "Hcond".
  wp_method_call. wp_call.
  iNamed "Hlock".
  wp_auto.
  wp_apply ("H_Unlock" with "[$]").
  wp_apply ("H_Lock" with "[$]") as "?".
  iApply "HΦ". done.
Qed.

Definition is_sema (x : loc) γ N : iProp Σ :=
  inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).

Definition own_sema γ (v : w32) : iProp Σ :=
  ghost_var γ (1/2) v.

Lemma wp_runtime_Semacquire (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semacquire" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_for.
  wp_bind (! _)%E.
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  unshelve iApply (wp_typed_Load with "[$Hs]"); try tc_solve.
  { done. }
  iNext.
  iIntros "Hs".
  iMod ("Hclose" with "[$]") as "_".
  iModIntro.
  wp_auto.
  destruct bool_decide eqn:Hnz.
  { (* keep looping *)
    wp_auto.
    wp_for_post.
    iFrame.
  }

  (* try to acquire *)
  rewrite bool_decide_eq_false in Hnz.
  wp_auto.
  wp_bind (CmpXchg _ _ _).
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  destruct (decide (v = v0)).
  {
    subst. iMod "HΦ" as (?) "[Hv2 HΦ]".
    iCombine "Hv Hv2" as "Hv" gives %[_ <-].
    iMod (ghost_var_update with "Hv") as "[Hv Hv2]".
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iNext. iIntros "Hs".
    iMod ("HΦ" with "[] [$]") as "HΦ".
    { iPureIntro.
      (* FIXME: word *)
      assert (uint.nat v0 ≠ O).
      { intros ?. apply Hnz. word. }
      word.
    }
    iModIntro.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    done.
  }
  { (* cmpxchg will fail *)
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve.
    { done. }
    { naive_solver. }
    iNext. iIntros "Hs".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

Lemma wp_runtime_SemacquireWaitGroup (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_SemacquireWaitGroup" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_apply (wp_runtime_Semacquire with "[$]").
  iFrame.
Qed.

Lemma wp_runtime_Semrelease (sema : loc) γ N (_u1 : bool) (_u2 : w64):
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (own_sema γ (word.add v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semrelease" #sema #_u1 #_u2 {{ Φ }}.
Proof.
Admitted.

Local Definition enc (low high : w32) : w64 :=
  word.add (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

Local Ltac local_word :=
  try apply word.unsigned_inj;
  repeat try (
      rewrite !word.unsigned_sru // ||
      rewrite word.unsigned_add ||
      rewrite word.unsigned_slu // ||
      rewrite !Z.shiftr_div_pow2 // ||
      rewrite Z.shiftl_mul_pow2 //
    );
  word
.

Local Lemma enc_get_high (low high : w32) :
  W32 (uint.Z (word.sru (enc low high) (W64 32))) = high.
Proof.
  local_word.
Qed.

Local Lemma enc_get_low (low high : w32) :
  W32 (uint.Z (enc low high)) = low.
Proof.
  local_word.
Qed.

Local Lemma enc_add_high (low high delta : w32) :
  word.add (enc low high) (word.slu (W64 (uint.Z delta)) (W64 32)) =
  enc low (word.add high delta).
Proof.
  local_word.
Qed.

Local Lemma enc_add_low (low high delta : w32) :
  uint.Z (word.add low delta) = uint.Z low + uint.Z delta →
  word.add (enc low high) (W64 (uint.Z delta)) =
  enc (word.add low delta) high.
Proof.
  intros. local_word.
Qed.

Local Lemma enc_inj (low high low' high' : w32) :
  enc low high = enc low' high' →
  low = low' ∧ high = high'.
Proof.
  intros Heq.
  split.
  - erewrite <-(enc_get_low low high).
    rewrite Heq enc_get_low //.
  - erewrite <-(enc_get_high low high).
    rewrite Heq enc_get_high //.
Qed.

Local Lemma enc_0 :
  W64 0 = enc (W32 0) (W32 0).
Proof. reflexivity. Qed.

Record WaitGroup_names := {
    counter_gn : gname ;
    sema_gn : gname ;
    waiter_gn : gname ;
    zerostate_gn : gname ;
  }.

Implicit Type γ : WaitGroup_names.

(* FIXME: opaque *)
Definition own_WaitGroup_waiters γ (possible_waiters : w32) : iProp Σ :=
  own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (uint.nat possible_waiters).

(* FIXME: opaque *)
Definition own_WaitGroup_wait_token γ : iProp Σ :=
  own_toks γ.(waiter_gn) 1.

Local Definition is_WaitGroup_inv wg γ N : iProp Σ :=
  inv (N.@"wg") (∃ (counter waiters sema possible_waiters : w32) unfinished_waiters,
  "Hsema" ∷ own_sema γ.(sema_gn) sema ∗
  "Hsema_zerotoks" ∷  own_toks γ.(zerostate_gn) (uint.nat sema) ∗

  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ waiters ≠ W32 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  (* When Add's caller has [own_waiters 0], this resource implies that there are no waiters. *)
  "Hwait_toks" ∷  own_toks γ.(waiter_gn) (uint.nat waiters) ∗
  "Hunfinished_wait_toks" ∷ own_toks γ.(waiter_gn) unfinished_waiters ∗

  "Hzeroauth" ∷ own_tok_auth γ.(zerostate_gn) unfinished_waiters ∗

  (* keeping this to maintain that the number of waiters does not overflow. *)
  "Hwaiters_bounded" ∷ own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (uint.nat possible_waiters) ∗

  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ O → waiters = W32 0 ∧ counter = W32 0 ⌝ ∗
  "%Hunfinished_bound" ∷ ⌜ Z.of_nat unfinished_waiters < 2^32 ⌝
  )%I.

(* FIXME: opaque *)
Definition is_WaitGroup wg γ N : iProp Σ :=
  "#Hsem" ∷ is_sema (struct.field_ref_f sync.WaitGroup "sema" wg) γ.(sema_gn) (N.@"sema") ∗
  "#Hinv" ∷ is_WaitGroup_inv wg γ N.

#[local]
Instance if_sumbool_timeless {PROP : bi} (P Q : PROP) {_:Timeless P} {_:Timeless Q} A B
  (x : sumbool A B) :
  Timeless (if x then P else Q).
Proof. apply _. Qed.

(* Prepare to Wait() *)
Lemma alloc_wait_token wg γ N (w : w32) :
  uint.Z (word.add w (W32 1)) = uint.Z w + 1 →
  is_WaitGroup wg γ N -∗
  own_WaitGroup_waiters γ w ={↑N}=∗ own_WaitGroup_waiters γ (word.add w (W32 1)) ∗ own_WaitGroup_wait_token γ.
Proof.
  intros. iIntros "[_ #Hinv] H".
  iInv "Hinv" as ">Hi". iNamed "Hi".
  iCombine "Hwaiters_bounded H" gives %[_ ->].
  iCombine "Hwaiters_bounded H" as "H". rewrite dfrac_op_own Qp.half_half.
  iMod (own_tok_auth_plus 1 with "H") as "[H Htok]".
  iModIntro. rewrite <- (Z2Nat.inj_add _ 1) by word. rewrite -H.
  iDestruct "H" as "[H1 H2]". iSplitR "Htok H2"; by iFrame.
Qed.

Lemma waiters_none_token_false γ :
  own_WaitGroup_waiters γ (W32 0) -∗ own_WaitGroup_wait_token γ -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %H. word.
Qed.

(* FIXME: Opaque *)
Definition own_WaitGroup γ (counter : w32) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.

Lemma start_WaitGroup N wg_ptr :
  wg_ptr ↦ (default_val sync.WaitGroup.t) ={⊤}=∗
  ∃ γ,
  is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ (W32 0) ∗ own_WaitGroup_waiters γ (W32 0).
Proof.
  iIntros "H".
  iDestruct (struct_fields_split with "H") as "H".
  iNamed "H". simpl.

  iMod (ghost_var_alloc (W32 0)) as "[%counter_gn [Hctr1 Hctr2]]".
  iMod (ghost_var_alloc (W32 0)) as "[%sema_gn [Hs1 Hs2]]".
  iMod (own_tok_auth_alloc) as "[%waiter_gn [Hwaiters Hw2]]".
  iMod (own_tok_auth_alloc) as "[%zerostate_gn Hzerostate]".

  iExists {| sema_gn := sema_gn; counter_gn := counter_gn; zerostate_gn := zerostate_gn; waiter_gn := waiter_gn |}.
  iFrame "∗#".
  unfold is_WaitGroup.
  iMod (inv_alloc with "[Hsema Hs2]") as "$".
  { iFrame. }
  iDestruct "Hstate" as "[Hstate Hstate2]".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 zerostate_gn) as "?".
  iMod (inv_alloc with "[-]") as "$".
  { iNext. repeat iExists (W32 0). iFrame. done. }
  done.
Qed.

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (uint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (uint.Z delta')) (W64 32).
Proof.
  intros ->. local_word.
Qed.

Lemma atomic_Uint64_inj a b c a' b' c' :
  atomic.Uint64.mk a b c = atomic.Uint64.mk a' b' c' →
  c = c'.
Proof.
  inversion 1.
  done.
Qed.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ N :
  let delta' := (W32 (uint.Z delta)) in
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) -∗
               own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Add" #delta {{ Φ }}.
Proof.
  intros delta'.
  wp_start as "#His".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto.
  wp_apply wp_Uint64__Add.
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iNamed "His".
  iInv "Hinv" as ">Hi" "Hclose".
  iNamed "Hi".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iCombine "Hctr Hwg" as "Hctr" gives %[_ ->].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    iDestruct "HnoWaiters" as "[%|HnoWaiter]"; first by exfalso.
    iCombine "HnoWaiter Hwait_toks" gives %Hbad.
    exfalso. apply Hw. word.
  }
  iCombine "Hptsto Hptsto2" as "Hptsto".
  iExists _. iFrame.
  rewrite (wg_delta_to_w32 delta') // enc_add_high.
  iMod (ghost_var_update (word.add oldc delta') with "Hctr") as "[Hctr Hctr_in]".
  iIntros "Hwg".
  destruct unfinished_waiters.
  2:{
    iExFalso. destruct (Hunfinished_zero ltac:(done)) as [-> ->].
    iDestruct "HnoWaiters" as "[%|HnoWaiters]"; first done.
    iCombine "HnoWaiters Hunfinished_wait_toks" gives %Hbad. word.
  }
  subst.
  destruct (decide (word.add oldc delta' = W32 0 ∧ waiters ≠ W32 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwaiters_bounded Hsema Hsema_zerotoks Hwg Hzeroauth Hwait_toks Hunfinished_wait_toks Hctr]").
    {
      iNext.
      iDestruct "Hwg" as "[Hwg Hwg2]".
      iExists _, _, _, _, O; iFrame "Hwg ∗".
      rewrite decide_False; last intuition.
      iFrame. done.
    }
    iMod ("HΦ" with "[$] [$]").
    iModIntro.
    wp_auto.
    rewrite enc_get_high enc_get_low.

    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      (* FIXME: word should do these. *)
      rewrite word.signed_add in Hbad.
      replace (sint.Z (W32 0)) with 0 in * by reflexivity.
      rewrite word.swrap_inrange in Hbad; lia.
    }
    wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_auto.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_auto.
        destruct bool_decide eqn:Heq1.
        + wp_auto.
          replace (W32 (uint.Z delta)) with delta' by reflexivity.
          rewrite bool_decide_eq_true in Heq1.
          destruct bool_decide eqn:Heq2.
          * exfalso. rewrite bool_decide_eq_true in Heq2.
            { (* FIXME: word. *)
              assert (sint.Z oldc = 0).
              {
                word_cleanup.
                rewrite word.signed_add /word.swrap in Heq2_signed.
                word.
              }
              apply Heq0. intuition. exfalso. apply H2.
              { apply word.signed_inj. rewrite H //. }
              word.
            }
          * wp_auto. iFrame. done.
        + wp_auto. iFrame. done.
    }
    iIntros (?) "[% H]". iNamed "H".
    subst.
    wp_auto.
    destruct (bool_decide) eqn:Heq1.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    rewrite bool_decide_eq_false in Heq1.
    wp_auto.
    rewrite bool_decide_true.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    apply not_and_l in HnoWake, HnotInWakingState.
    destruct HnoWake as [|].
    2:{ by apply dec_stable. }
    destruct HnotInWakingState as [|].
    2:{ by apply dec_stable. }
    apply Znot_gt_le in Heq1.
    exfalso.
    (* FIXME: word *)
    apply H. clear H. apply word.signed_inj.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    intuition.
    apply Z.le_antisymm.
    { word. }
    { word_cleanup.
      rewrite word.signed_add /word.swrap in H2 |- *.
      word. }
  }

  (* will have to wake *)
  iDestruct "Hwg" as "[Hwg Hwg2]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hwaiters_bounded Hsema Hsema_zerotoks Hwg2 Hzeroauth Hwait_toks Hunfinished_wait_toks Hctr]") as "_".
  {
    iNext.
    iExists _, _, _, _, O; iFrame "Hwg2 ∗".
    rewrite decide_True; last intuition.
    done.
  }
  iMod ("HΦ" with "[$] [$]") as "HΦ".
  iModIntro.
  wp_auto. rewrite enc_get_high enc_get_low.

  destruct bool_decide eqn:Hbad.
  {
    exfalso.
    rewrite bool_decide_eq_true in Hbad.
    (* FIXME: word should do these. *)
    rewrite word.signed_add in Hbad.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    rewrite word.swrap_inrange in Hbad; lia.
  }
  wp_auto.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_auto.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_auto.
      destruct bool_decide eqn:Heq1.
      + wp_auto.
        replace (W32 (uint.Z delta)) with delta' by reflexivity.
        rewrite bool_decide_eq_true in Heq1.
        destruct bool_decide eqn:Heq2.
        * exfalso. rewrite bool_decide_eq_true in Heq2.
          { (* FIXME: word. *)
            assert (sint.Z oldc = 0).
            {
              word_cleanup.
              rewrite word.signed_add /word.swrap in Heq2_signed.
              word.
            }
            apply Heq0. intuition. exfalso. apply H4.
            { apply word.signed_inj. rewrite H //. }
            word.
          }
        * wp_auto. iFrame. done.
      + wp_auto. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. word. }
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. }
  wp_auto.
  wp_apply wp_Uint64__Load.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  iModIntro.
  wp_auto.
  rewrite bool_decide_true //.

  (* want to get a bunch of unfinisheds. *)
  wp_auto.
  wp_apply wp_Uint64__Store.
  iInv "Hinv" as ">Hi" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  clear Hunfinished_zero sema.
  iNamed "Hi".
  iClear "Hptsto2".
  iCombine "Hwg Hptsto"  gives %[_ Heq].
  apply atomic_Uint64_inj in Heq.
  apply enc_inj in Heq as [<- <-].
  iCombine "Hwg Hptsto" as "Hwg".
  iExists _. iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  destruct (unfinished_waiters) eqn:Huf.
  2:{ exfalso. specialize (Hunfinished_zero ltac:(word)). intuition. }
  clear Hunfinished_zero.
  iClear "Hunfinished_wait_toks".
  iCombine "Hzeroauth Hsema_zerotoks" gives %Hs.
  replace (sema) with (W32 0) by word.
  clear Huf Hs unfinished_waiters sema.
  iMod (own_tok_auth_plus (uint.nat waiters) with "[$Hzeroauth]") as "[Hzeroauth Hzerotoks]".
  iEval (rewrite enc_0) in "Hwg".
  iDestruct "Hwg" as "[Hwg Hwg2]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod (own_toks_0 γ.(waiter_gn)) as "Hwait_toks'".
  iMod ("Hclose" with "[Hwaiters_bounded Hwg Hwg2 Hzeroauth Hwait_toks Hwait_toks' Hctr Hsema Hsema_zerotoks]") as "_".
  { iNext. iFrame "Hwg ∗". iPureIntro. split; [done | word]. }
  iModIntro.
  wp_auto.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : w32),
        "w" ∷ w_ptr ↦ wrem ∗
        "Hzerotoks" ∷ own_toks γ.(zerostate_gn) (uint.nat wrem)
    )%I with "[$]" as "HloopInv".

  wp_for.
  iNamed "HloopInv".
  wp_auto.
  destruct bool_decide eqn:Hwrem.
  { (* no more waiters to wake up. *)
    rewrite decide_False; last naive_solver.
    rewrite decide_True //.
    wp_auto. iFrame.
  }

  (* wake up another waiter *)
  rewrite bool_decide_eq_false in Hwrem.
  rewrite decide_True //.
  wp_auto.
  wp_apply (wp_runtime_Semrelease with "[$]").
  iInv "Hinv" as ">Hi" "Hclose".
  iNamed "Hi".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame "Hsema".
  iIntros "Hsema".
  iMod "Hmask" as "_".
  replace (uint.nat wrem)%nat with (1+(uint.nat (word.sub wrem (W32 1))))%nat.
  2:{ (* FIXME: word *) apply w32_val_neq in Hwrem. word. }
  iDestruct (own_toks_plus with "Hzerotoks") as "[Hzerotok Hzerotoks]".
  iCombine "Hsema_zerotoks Hzerotok" as "Hsema_zerotok".
  iCombine "Hzeroauth Hsema_zerotok" gives %Hbound.

  iMod ("Hclose" with "[-w defer delta v state wg Hzerotoks HΦ]").
  {
    iFrame "Hsema ∗ %".
    replace (uint.nat (word.add sema (W32 1))) with ((uint.nat sema) + 1)%nat by word.
    iFrame.
  }
  iModIntro. wp_auto. wp_for_post. iFrame.
Qed.

Lemma wp_WaitGroup__Done (wg : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc - 1 < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) -∗
               own_WaitGroup γ (word.sub oldc (W32 1)) ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Done" #() {{ Φ }}.
Proof.
  wp_start as "#His".
  wp_auto.
  wp_apply (wp_WaitGroup__Add with "[$]").
  iMod "HΦ". iNamed "HΦ".
  replace (W32 (uint.Z (W64 (-1)))) with (W32 (-1)) by done.
  replace (sint.Z (W32 (-1))) with (-1) by done.
  iModIntro. iFrame "Hwg HnoWaiters". iSplitR.
  { word. }
  iIntros "Hw Hctr".
  iMod ("HΦ" with "[$] [Hctr]") as "HΦ".
  { iExactEq "Hctr". repeat f_equal. word. }
  iModIntro. wp_auto. iApply "HΦ".
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) (delta : w64) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N ∗ own_WaitGroup_wait_token γ -∗
  (|={⊤∖↑N, ∅}=>
     ∃ oldc,
       own_WaitGroup γ oldc ∗ (⌜ sint.Z oldc = 0 ⌝ → own_WaitGroup γ oldc ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token γ -∗ Φ #())
  ) -∗
  WP wg @ sync @ "WaitGroup'ptr" @ "Wait" #() {{ Φ }}.
Proof.
  wp_start as "(#Hwg & HR_in)". iNamed "Hwg".
  wp_auto.
  wp_for_core. (* TODO: need to set later credits *)
  wp_auto.
  rewrite decide_True //. wp_auto.
  wp_apply (wp_Uint64__Load).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamed "Hi".
  destruct (decide (counter = W32 0)).
  { (* counter is zero, so can return. *)
    subst.

    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iModIntro.
    iCombine "Hwg Hctr" gives %[_ ->].
    iExists _.
    iFrame.
    iIntros "Hptsto".
    iMod ("HΦ" with "[//] [$]") as "HΦ".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwaiters_bounded Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hzeroauth Hwg Hsema Hsema_zerotoks]").
    { by iFrame. }
    iModIntro.
    wp_auto. rewrite enc_get_high enc_get_low bool_decide_true //=.
    wp_auto.
    wp_for_post.
    by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".

  iCombine "HR_in Hwait_toks" as "Hwait_toks'".
  iCombine "Hwaiters_bounded Hwait_toks'" gives %HwaitersLe.
  iDestruct (own_toks_plus with "Hwait_toks'") as "[HR_in Hwait_toks]".
  iMod ("Hclose" with "[Hwaiters_bounded Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hzeroauth Hctr Hsema Hsema_zerotoks]").
  { by iFrame. }
  iModIntro.
  wp_auto.
  rewrite enc_get_high enc_get_low bool_decide_false //.
  wp_auto.
  replace (1%Z) with (uint.Z (W32 1)) by reflexivity.
  rewrite -> enc_add_low by word.
  wp_apply (wp_Uint64__CompareAndSwap).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamed "Hi".
  setoid_rewrite bool_decide_decide.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists (enc waiters0 counter0).
  destruct (decide (_ = _)) as [Heq|Hneq].
  {
    apply enc_inj in Heq as [-> ->].
    rewrite decide_False.
    2:{ naive_solver. }
    iCombine "Hptsto Hptsto2" as "$".
    iSplitR; first done.
    iIntros "[Hptsto Hptsto2]".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwaiters_bounded HR_in Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hsema Hsema_zerotoks Hzeroauth Hctr]") as "_".
    {
      iNext. repeat iExists _. iFrame "Hptsto ∗".
      iCombine "HR_in Hwait_toks" as "Hwait_toks".
      replace (uint.nat (word.add waiters (W32 1))) with (1 + uint.nat waiters)%nat by word.
      simpl. iFrame.
      iSplitL.
      { by destruct decide. }
      iPureIntro. split; last done.
      intros Hun. exfalso. naive_solver.
    }
    iModIntro.
    wp_auto.

    clear sema n unfinished_waiters Hunfinished_zero Hunfinished_bound unfinished_waiters0 Hunfinished_zero0 Hunfinished_bound0.

    wp_apply (wp_runtime_SemacquireWaitGroup with "[$]").
    iInv "Hinv" as ">Hi" "Hclose".
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame "Hsema".
    iIntros "%Hsem Hsema".
    destruct (uint.nat sema) eqn:Hsema.
    { exfalso. lia. }
    replace (S n) with (1 + n)%nat by done.
    iDestruct (own_toks_plus with "Hsema_zerotoks") as "[Hzerotok Hsema_zerotoks]".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwaiters_bounded Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hsema Hsema_zerotoks Hzeroauth Hctr]") as "_".
    {
      iNext. iFrame.
      replace (uint.nat (word.sub sema (W32 1))) with n by word.
      iFrame. done.
    }
    iModIntro.
    wp_auto.
    wp_apply (wp_Uint64__Load).
    iInv "Hinv" as ">Hi" "Hclose".
    iClear "v w state". clear v_ptr counter w_ptr waiters state_ptr HwaitersLe.
    clear unfinished_waiters sema n Hsema Hsem Hunfinished_zero Hunfinished_bound.
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _. iFrame "Hptsto".
    iCombine "Hzeroauth Hzerotok" gives %Hunfinished_pos.
    specialize (Hunfinished_zero ltac:(lia)) as [-> ->].
    iIntros "Hptsto".
    iMod "Hmask" as "_".

    (* now, deallocate Htok. *)
    destruct unfinished_waiters; first by (exfalso; lia).
    iMod (own_tok_auth_delete_S with "Hzeroauth Hzerotok") as "Hzeroauth".
    replace (S _) with (1 + unfinished_waiters)%nat by done.
    iDestruct (own_toks_plus with "Hunfinished_wait_toks") as "[HR Hunfinished_wait_toks]".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iCombine "Hwg Hctr" gives %[_ ->].
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask".
    iMod ("Hclose" with "[Hwaiters_bounded Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hsema Hsema_zerotoks Hzeroauth Hctr]") as "_".
    { iFrame. iPureIntro. split; [done | word]. }
    iModIntro.
    wp_auto.
    wp_for_post.
    iApply "HΦ". done.
  }
  {
    iFrame "Hptsto".
    iSplitR; first done.
    iIntros "Hptsto".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwaiters_bounded Hptsto Hptsto2 Hwait_toks Hunfinished_wait_toks Hsema Hsema_zerotoks Hzeroauth Hctr]") as "_".
    { iFrame. done. }
    iModIntro. wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
