From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.goose_lang Require Export std.
From New.proof Require Import github_com.goose_lang.primitive std.std_core sync.

Set Default Proof Using "Type".

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!std.GlobalAddrs}.

#[global]
Program Instance : IsPkgInit std :=
  ltac2:(build_pkg_init ()).

Lemma wp_Assert (cond : bool) :
  {{{ is_pkg_init std ∗ ⌜cond = true⌝ }}}
    std @ "Assert" #cond
  {{{ RET #(); True }}}.
Proof.
  wp_start as "%". subst.
  wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_BytesEqual s1 s2 (xs1 xs2: list w8) dq1 dq2 :
  {{{ is_pkg_init std ∗ s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}}
    std @ "BytesEqual" #s1 #s2
  {{{ RET #(bool_decide (xs1 = xs2)); s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}}.
Proof.
  wp_start as "[Hs1 Hs2]".
  wp_auto.
  iDestruct (own_slice_len with "Hs1") as "%".
  iDestruct (own_slice_len with "Hs2") as "%".
  wp_if_destruct; try wp_auto.
  {
    assert (length xs1 = length xs2) by word.
    iAssert (∃ (i: w64),
                "i" ∷ i_ptr ↦ i ∗
                "%Hi" ∷ ⌜∀ (n: nat), (n < uint.nat i)%nat → xs1 !! n = xs2 !! n⌝
            )%I with "[$i]" as "IH".
    {
      iPureIntro. intros. word.
    }
    wp_for "IH".
    wp_if_destruct; try wp_auto.
    - list_elem xs1 i as x1_i.
      wp_apply (wp_load_slice_elem with "[$Hs1]") as "Hs1"; first by eauto.
      wp_auto. wp_pure; first by word.
      list_elem xs2 i as x2_i.
      wp_apply (wp_load_slice_elem with "[$Hs2]") as "Hs2"; first by eauto. wp_auto.
      destruct (bool_decide_reflect (x1_i = x2_i)); subst; wp_auto.
      + wp_for_post.
        iFrame.
        iPureIntro; intros.
        destruct (decide (n < uint.nat i)); eauto with lia.
        assert (n = uint.nat i) by word; subst.
        congruence.
      + wp_for_post.
        rewrite -> bool_decide_eq_false_2 by congruence.
        iApply "HΦ"; iFrame.
    - rewrite bool_decide_eq_true_2.
      { iApply "HΦ"; iFrame. }
      eapply list_eq_same_length; eauto.
      { word. }
      intros ???? Hget1 Hget2.
      rewrite -> Hi in Hget1 by lia.
      congruence.
  }
  rewrite bool_decide_eq_false_2.
  { iApply "HΦ". iFrame. }
  intros ?%(f_equal length).
  word.
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    std @ "SumNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_"; wp_auto.
  wp_apply wp_SumNoOverflow. wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    std @ "SumAssumeNoOverflow" #x #y
  {{{ RET #(word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_"; wp_auto.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros "%". wp_auto. iApply "HΦ". done.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l ↦s[std.JoinHandle :: "mu"]□ mu_l ∗
  "#cond" ∷ l ↦s[std.JoinHandle :: "cond"]□ cond_l ∗
  "#Hcond" ∷ is_Cond cond_l (interface.mk Mutex_type_id #mu_l) ∗
  "#Hlock" ∷ is_Mutex mu_l
     (∃ (done_b: bool),
         "done_b" ∷ l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ is_pkg_init std }}}
    std @ "newJoinHandle" #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_alloc mu as "?".
  wp_auto.
  wp_apply (wp_NewCond with "[#]") as "%cond #His_cond". wp_auto.
  wp_alloc jh_l as "jh".
  iApply struct_fields_split in "jh". simpl. iNamed "jh".
  iPersist "Hmu Hcond".
  iMod (init_Mutex (∃ (done_b: bool),
         "done_b" ∷ jh_l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
         with "[$] [$]") as "Hlock".
  wp_auto.
  iApply "HΦ".
  rewrite /is_JoinHandle.
  iFrame "His_cond #". iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_pkg_init std ∗ is_JoinHandle l P ∗ P }}}
    l @ std @ "JoinHandle'ptr" @ "finish" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hhandle P]".
  iNamed "Hhandle".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Cond__Signal with "[$Hcond]"). wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iFrame "done_b P". }
  wp_auto. iApply "HΦ".
  done.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f : func.t) :
  {{{ is_pkg_init std ∗
        (∀ Φ, ▷(P -∗ Φ #()) -∗ WP #f #() {{ Φ }}) }}}
  std @ "Spawn" #f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "Hwp".
  wp_auto.
  wp_apply (wp_newJoinHandle P) as "%l #Hhandle".
  wp_auto. iPersist "f h".
  wp_apply (wp_fork with "[Hwp]"); wp_auto.
  - (* NOTE: it's important not to do a pure reduction here since it would
    produce a substitution into the lambda *)
    wp_apply "Hwp".
    iIntros "HP".
    wp_auto.
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]"). wp_auto.
    done.
  - iApply "HΦ".
    iFrame "#".
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_pkg_init std ∗ is_JoinHandle l P }}}
    l @ std @ "JoinHandle'ptr" @ "Join" #()
  {{{ RET #(); P }}}.
Proof.
  wp_start as "Hjh". iNamed "Hjh".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
  wp_auto.

  iAssert (∃ (done_b: bool),
           "locked" ∷ own_Mutex mu_l ∗
           "done" ∷ l ↦s[std.JoinHandle::"done"] done_b ∗
           "HP" ∷ (if done_b then P else True))%I
          with "[$Hlocked $done_b $HP]" as "HI".
  wp_for "HI".
  destruct done_b0; wp_auto.
  - wp_for_post.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done]").
    wp_auto. iApply "HΦ". done.
  - wp_apply (wp_Cond__Wait with "[$Hcond locked done HP]") as "H".
    { iSplit.
      - iApply (Mutex_is_Locker with "[] Hlock"). iPkgInit.
      - iFrame. }
    iDestruct "H" as "[Hlocked Hlinv]". iNamed "Hlinv".
    wp_auto. wp_for_post. iFrame.
Qed.

End wps.
