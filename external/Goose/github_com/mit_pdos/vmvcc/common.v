(* autogenerated from github.com/mit-pdos/vmvcc/common *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition RET_SUCCESS : expr := #0.

Definition RET_NONEXIST : expr := #1.

Definition RET_RETRY : expr := #200.

Definition RET_UNSERIALIZABLE : expr := #400.

End code.
