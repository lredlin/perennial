From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.disk_ffi.impl.
#[global]
Existing Instances disk.disk_op disk.disk_model.
Coercion Var' (s: string) := Var s.
