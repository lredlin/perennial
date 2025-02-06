Require Export New.manualproof.github_com.mit_pdos.gokv.grove_ffi.
(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import github_com.mit_pdos.gokv.grove_ffi.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.proof.grove_prelude.
Module grove_ffi.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions grove_ffi.pkg_name' var_addrs grove_ffi.functions' grove_ffi.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_FileWrite :
  WpFuncCall grove_ffi.pkg_name' "FileWrite" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_FileRead :
  WpFuncCall grove_ffi.pkg_name' "FileRead" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_FileAppend :
  WpFuncCall grove_ffi.pkg_name' "FileAppend" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Listen :
  WpFuncCall grove_ffi.pkg_name' "Listen" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Accept :
  WpFuncCall grove_ffi.pkg_name' "Accept" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Connect :
  WpFuncCall grove_ffi.pkg_name' "Connect" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Send :
  WpFuncCall grove_ffi.pkg_name' "Send" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Receive :
  WpFuncCall grove_ffi.pkg_name' "Receive" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_GetTimeRange :
  WpFuncCall grove_ffi.pkg_name' "GetTimeRange" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_GetTSC :
  WpFuncCall grove_ffi.pkg_name' "GetTSC" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

End defs.
End grove_ffi.
