From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang.lib Require Import control.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.

(** A proof principle for if e { do_stuff(); } where do_stuff() is optional and
does something irrelevant to the proof using resources R. Allows to re-use the
proof for both branches, carrying on with resources R. *)
Theorem wp_If_optional stk E (R: iProp Σ) (b: bool) e :
  (∀ (Φ': val → iProp Σ), R -∗ ▷ (R -∗ Φ' #()) -∗ WP e @ stk; E {{ Φ' }}) -∗
  ∀ Φ, R -∗ ▷ (R -∗ Φ #()) -∗ WP If #b e #() @ stk; E {{ Φ }}.
Proof.
  iIntros "Hwp" (Φ) "HR HΦ".
  wp_if_destruct.
  - wp_apply ("Hwp" with "[$HR]").
    iFrame.
  - iApply ("HΦ" with "HR").
Qed.

Theorem wp_If_join stk E (R: iProp Σ) (b: bool) e1 e2 :
  R -∗
  ∀ Φ, (▷ (R -∗ Φ #()) -∗ WP e1 @ stk; E {{ Φ }}) ∧
       (▷ (R -∗ Φ #()) -∗ WP e2 @ stk; E {{ Φ }}) -∗
       ▷ (R -∗ Φ #()) -∗ WP if: #b then e1 else e2 @ stk; E {{ Φ }}.
Proof.
  iIntros "R" (Φ) "Hwp HΦ".
  wp_if_destruct.
  - iDestruct "Hwp" as "[He1 _]".
    wp_apply "He1".
    iFrame.
  - iDestruct "Hwp" as "[_ He2]".
    wp_apply "He2".
    iFrame.
Qed.

(* similar to above but with persistence modalities coming from hoare triple notation *)
Theorem wp_If_join_triples stk E (R: iProp Σ) (b: bool) e1 e2 :
  {{{ R }}} e1 @ stk; E {{{ RET #(); R }}} -∗
  {{{ R }}} e2 @ stk; E {{{ RET #(); R }}} -∗
  {{{ R }}} if: #b then e1 else e2 @ stk; E {{{ RET #(); R }}}.
Proof.
  iIntros "#He1 #He2".
  iIntros "!>" (Φ) "HR HΦ".
  wp_if_destruct.
  - wp_apply ("He1" with "[$HR]").
    iFrame.
  - wp_apply ("He2" with "[$HR]").
    iFrame.
Qed.

Theorem wp_Assume stk E (cond: bool) :
  {{{ True }}}
    Assume #cond @ stk; E
  {{{ RET #(); ⌜cond = true⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - iApply ("HΦ" with "[//]").
  - wp_pures.
    iLöb as "IH".
    wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

Theorem wp_Assert stk E (cond: bool) :
  cond = true ->
  {{{ True }}}
    Assert #cond @ stk; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  wp_call.
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
