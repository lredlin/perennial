Require Export New.manualproof.sync.
(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import sync.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.sync.
Require Export New.proof.proof_prelude.
Module sync.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions sync.pkg_name' var_addrs sync.functions' sync.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_NewCond :
  WpFuncCall sync.pkg_name' "NewCond" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

End defs.
End sync.
