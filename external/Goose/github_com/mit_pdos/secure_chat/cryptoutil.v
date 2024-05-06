(* autogenerated from github.com/mit-pdos/secure-chat/cryptoutil *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.secure_chat.cryptoffi.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Hasher: ty := slice.T byteT.

Definition HasherWrite: val :=
  rec: "HasherWrite" "h" "data" :=
    "h" <-[slice.T byteT] (SliceAppendSlice byteT (![slice.T byteT] "h") "data");;
    #().

Definition HasherWriteSl: val :=
  rec: "HasherWriteSl" "h" "data" :=
    ForSlice (slice.T byteT) <> "hash" "data"
      (HasherWrite "h" "hash");;
    #().

Definition HasherSum: val :=
  rec: "HasherSum" "h" "b" :=
    let: "hash" := cryptoffi.Hash "h" in
    let: "b1" := ref_to (slice.T byteT) "b" in
    "b1" <-[slice.T byteT] (SliceAppendSlice byteT (![slice.T byteT] "b1") "hash");;
    ![slice.T byteT] "b1".

End code.
