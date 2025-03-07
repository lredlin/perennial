(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

Require Export New.code.google_golang_org.grpc.codes.
Module codes.
Axiom falso : False.

Module Code.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End Code.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined codes :=
{|
  is_pkg_defined := is_global_definitions codes var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End codes.
