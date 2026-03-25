From New.proof Require Import proof_prelude.
From New.proof Require Export std.
From New.generatedproof Require Export strings.
From Perennial Require Import base.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : strings.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

(* Tests for go_string interpreting, these were generated from go
   directly
*)
Example test_escape_newline              : ("\n"%go : go_string) = [W8 10] := eq_refl.
Example test_escape_newline_len : length ("\n"%go : go_string) = 1%nat := eq_refl.

Example test_escape_tab                  : ("\t"%go : go_string) = [W8 9] := eq_refl.
Example test_escape_tab_len : length ("\t"%go : go_string) = 1%nat := eq_refl.

Example test_escape_cr                   : ("\r"%go : go_string) = [W8 13] := eq_refl.
Example test_escape_cr_len : length ("\r"%go : go_string) = 1%nat := eq_refl.

Example test_escape_backslash            : ("\\"%go : go_string) = [W8 92] := eq_refl.
Example test_escape_backslash_len : length ("\\"%go : go_string) = 1%nat := eq_refl.

Example test_escape_dquote               : (""""%go : go_string) = [W8 34] := eq_refl.
Example test_escape_dquote_len : length (""""%go : go_string) = 1%nat := eq_refl.

Example test_escape_bell                 : ("\a"%go : go_string) = [W8 7] := eq_refl.
Example test_escape_bell_len : length ("\a"%go : go_string) = 1%nat := eq_refl.

Example test_escape_backspace            : ("\b"%go : go_string) = [W8 8] := eq_refl.
Example test_escape_backspace_len : length ("\b"%go : go_string) = 1%nat := eq_refl.

Example test_escape_formfeed             : ("\f"%go : go_string) = [W8 12] := eq_refl.
Example test_escape_formfeed_len : length ("\f"%go : go_string) = 1%nat := eq_refl.

Example test_escape_vtab                 : ("\v"%go : go_string) = [W8 11] := eq_refl.
Example test_escape_vtab_len : length ("\v"%go : go_string) = 1%nat := eq_refl.

Example test_escape_mixed                : ("foo\nbar"%go : go_string) = [W8 102; W8 111; W8 111; W8 10; W8 98; W8 97; W8 114] := eq_refl.
Example test_escape_mixed_len : length ("foo\nbar"%go : go_string) = 7%nat := eq_refl.

Example test_escape_multiple             : ("\t\n\r"%go : go_string) = [W8 9; W8 10; W8 13] := eq_refl.
Example test_escape_multiple_len : length ("\t\n\r"%go : go_string) = 3%nat := eq_refl.

Example test_escape_in_middle            : ("a\tb"%go : go_string) = [W8 97; W8 9; W8 98] := eq_refl.
Example test_escape_in_middle_len : length ("a\tb"%go : go_string) = 3%nat := eq_refl.

Example test_escape_at_end               : ("foo\n"%go : go_string) = [W8 102; W8 111; W8 111; W8 10] := eq_refl.
Example test_escape_at_end_len : length ("foo\n"%go : go_string) = 4%nat := eq_refl.

Example test_escape_at_start             : ("\nfoo"%go : go_string) = [W8 10; W8 102; W8 111; W8 111] := eq_refl.
Example test_escape_at_start_len : length ("\nfoo"%go : go_string) = 4%nat := eq_refl.

Example test_escape_consecutive          : ("\n\n\n"%go : go_string) = [W8 10; W8 10; W8 10] := eq_refl.
Example test_escape_consecutive_len : length ("\n\n\n"%go : go_string) = 3%nat := eq_refl.

Example test_escape_plain                : ("hello"%go : go_string) = [W8 104; W8 101; W8 108; W8 108; W8 111] := eq_refl.
Example test_escape_plain_len : length ("hello"%go : go_string) = 5%nat := eq_refl.

Example test_escape_empty                : (""%go : go_string) = [] := eq_refl.
Example test_escape_empty_len : length (""%go : go_string) = 0%nat := eq_refl.

Example test_escape_dquote_mixed         : ("AB"""%go : go_string) = [W8 65; W8 66; W8 34] := eq_refl.

Example test_escape_all : ("\a\b\f\n\r\t\v\\"""%go : go_string) = [W8 7; W8 8; W8 12; W8 10; W8 13; W8 9; W8 11; W8 92; W8 34] := eq_refl.
Example test_escape_all_len : length ("\a\b\f\n\r\t\v\\"""%go : go_string) = 9%nat := eq_refl.

Lemma wp_asciiSpace_init :
  {{{ True }}}
    strings.asciiSpace'init #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop strings get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    strings.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init strings }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply wp_asciiSpace_init.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
