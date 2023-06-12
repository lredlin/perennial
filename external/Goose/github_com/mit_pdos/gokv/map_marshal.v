(* autogenerated from github.com/mit-pdos/gokv/map_marshal *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition EncodeMapU64ToU64: val :=
  rec: "EncodeMapU64ToU64" "kvs" :=
    let: "enc" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (MapLen "kvs");;
    MapIter "kvs" (λ: "k" "v",
      "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") "k";;
      "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") "v");;
    ![slice.T byteT] "enc".

Definition DecodeMapU64ToU64: val :=
  rec: "DecodeMapU64ToU64" "enc_in" :=
    let: "enc" := ref_to (slice.T byteT) "enc_in" in
    let: "kvs" := NewMap uint64T uint64T #() in
    let: ("numEntries", "enc2") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "enc2";;
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < "numEntries"); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      let: "key" := ref (zero_val uint64T) in
      let: "val" := ref (zero_val uint64T) in
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      "key" <-[uint64T] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      "val" <-[uint64T] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      MapInsert "kvs" (![uint64T] "key") (![uint64T] "val");;
      Continue);;
    ("kvs", ![slice.T byteT] "enc").

Definition EncodeMapU64ToBytes: val :=
  rec: "EncodeMapU64ToBytes" "kvs" :=
    let: "enc" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (MapLen "kvs");;
    MapIter "kvs" (λ: "k" "v",
      "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") "k";;
      "enc" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "enc") (slice.len "v");;
      "enc" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "enc") "v");;
    ![slice.T byteT] "enc".

Definition DecodeMapU64ToBytes: val :=
  rec: "DecodeMapU64ToBytes" "enc_in" :=
    let: "enc" := ref_to (slice.T byteT) "enc_in" in
    let: "kvs" := NewMap uint64T (slice.T byteT) #() in
    let: ("numEntries", "enc2") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "enc2";;
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < "numEntries"); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      let: ("key", "enc3") := marshal.ReadInt (![slice.T byteT] "enc") in
      let: ("valLen", "enc4") := marshal.ReadInt "enc3" in
      let: ("val", "enc5") := marshal.ReadBytesCopy "enc4" "valLen" in
      "enc" <-[slice.T byteT] "enc5";;
      MapInsert "kvs" "key" "val";;
      Continue);;
    ("kvs", ![slice.T byteT] "enc").

End code.
