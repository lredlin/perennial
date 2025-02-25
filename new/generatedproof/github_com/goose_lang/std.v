(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.goose_lang.primitive.
Require Export New.code.github_com.goose_lang.std.
Require Export New.golang.theory.

Module std.
Axiom falso : False.
Module JoinHandle.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  mu' : loc;
  done' : bool;
  cond' : loc;
}.
End def.
End JoinHandle.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_JoinHandle `{ffi_syntax}: Settable _ :=
  settable! JoinHandle.mk < JoinHandle.mu'; JoinHandle.done'; JoinHandle.cond' >.
Global Instance into_val_JoinHandle `{ffi_syntax} : IntoVal JoinHandle.t.
Admitted.

Global Instance into_val_typed_JoinHandle `{ffi_syntax} : IntoValTyped JoinHandle.t std.JoinHandle :=
{|
  default_val := JoinHandle.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_JoinHandle_mu `{ffi_syntax} : IntoValStructField "mu" std.JoinHandle JoinHandle.mu'.
Admitted.

Global Instance into_val_struct_field_JoinHandle_done `{ffi_syntax} : IntoValStructField "done" std.JoinHandle JoinHandle.done'.
Admitted.

Global Instance into_val_struct_field_JoinHandle_cond `{ffi_syntax} : IntoValStructField "cond" std.JoinHandle JoinHandle.cond'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_JoinHandle `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} mu' done' cond':
  PureWp True
    (struct.make std.JoinHandle (alist_val [
      "mu" ::= #mu';
      "done" ::= #done';
      "cond" ::= #cond'
    ]))%V
    #(JoinHandle.mk mu' done' cond').
Admitted.


Global Instance JoinHandle_struct_fields_split dq l (v : JoinHandle.t) :
  StructFieldsSplit dq l v (
    "Hmu" ∷ l ↦s[std.JoinHandle :: "mu"]{dq} v.(JoinHandle.mu') ∗
    "Hdone" ∷ l ↦s[std.JoinHandle :: "done"]{dq} v.(JoinHandle.done') ∗
    "Hcond" ∷ l ↦s[std.JoinHandle :: "cond"]{dq} v.(JoinHandle.cond')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions std.pkg_name' var_addrs std.functions' std.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_Assert :
  WpFuncCall std.pkg_name' "Assert" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_BytesEqual :
  WpFuncCall std.pkg_name' "BytesEqual" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_BytesClone :
  WpFuncCall std.pkg_name' "BytesClone" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SliceSplit :
  WpFuncCall std.pkg_name' "SliceSplit" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SumNoOverflow :
  WpFuncCall std.pkg_name' "SumNoOverflow" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_SumAssumeNoOverflow :
  WpFuncCall std.pkg_name' "SumAssumeNoOverflow" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_newJoinHandle :
  WpFuncCall std.pkg_name' "newJoinHandle" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Spawn :
  WpFuncCall std.pkg_name' "Spawn" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Multipar :
  WpFuncCall std.pkg_name' "Multipar" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Skip :
  WpFuncCall std.pkg_name' "Skip" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_JoinHandle'ptr_Join :
  WpMethodCall std.pkg_name' "JoinHandle'ptr" "Join" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JoinHandle'ptr_finish :
  WpMethodCall std.pkg_name' "JoinHandle'ptr" "finish" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End std.
