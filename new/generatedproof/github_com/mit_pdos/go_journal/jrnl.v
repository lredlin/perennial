(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.disk_prelude.
Require Export New.generatedproof.github_com.mit_pdos.go_journal.addr.
Require Export New.generatedproof.github_com.mit_pdos.go_journal.buf.
Require Export New.generatedproof.github_com.mit_pdos.go_journal.obj.
Require Export New.generatedproof.github_com.mit_pdos.go_journal.util.
Require Export New.golang.theory.

Require Export New.code.github_com.mit_pdos.go_journal.jrnl.

Set Default Proof Using "Type".

Module jrnl.

(* type jrnl.Op *)
Module Op.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  log' : loc;
  bufs' : loc;
}.
End def.
End Op.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Op : Settable Op.t :=
  settable! Op.mk < Op.log'; Op.bufs' >.
Global Instance into_val_Op : IntoVal Op.t :=
  {| to_val_def v :=
    struct.val_aux jrnl.Op [
    "log" ::= #(Op.log' v);
    "bufs" ::= #(Op.bufs' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Op : IntoValTyped Op.t jrnl.Op :=
{|
  default_val := Op.mk (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Op_log : IntoValStructField "log" jrnl.Op Op.log'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Op_bufs : IntoValStructField "bufs" jrnl.Op Op.bufs'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Op log' bufs':
  PureWp True
    (struct.make #jrnl.Op (alist_val [
      "log" ::= #log';
      "bufs" ::= #bufs'
    ]))%struct
    #(Op.mk log' bufs').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Op_struct_fields_split dq l (v : Op.t) :
  StructFieldsSplit dq l v (
    "Hlog" ∷ l ↦s[jrnl.Op :: "log"]{dq} v.(Op.log') ∗
    "Hbufs" ∷ l ↦s[jrnl.Op :: "bufs"]{dq} v.(Op.bufs')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (Op.log' v)) jrnl.Op "log"%go.

  solve_field_ref_f.
Qed.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined jrnl :=
{|
  is_pkg_defined := is_global_definitions jrnl var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

Global Instance wp_func_call_Begin :
  WpFuncCall jrnl "Begin" _ (is_pkg_defined jrnl) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Op'ptr_CommitWait :
  WpMethodCall jrnl "Op'ptr" "CommitWait" _ (is_pkg_defined jrnl) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Op'ptr_NDirty :
  WpMethodCall jrnl "Op'ptr" "NDirty" _ (is_pkg_defined jrnl) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Op'ptr_OverWrite :
  WpMethodCall jrnl "Op'ptr" "OverWrite" _ (is_pkg_defined jrnl) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Op'ptr_ReadBuf :
  WpMethodCall jrnl "Op'ptr" "ReadBuf" _ (is_pkg_defined jrnl) :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End jrnl.
