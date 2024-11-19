(* autogenerated from github.com/mit-pdos/tulip/txn *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.gcoord.
From Goose Require github_com.mit_pdos.tulip.tulip.
From Perennial.goose_lang.trusted Require Import github_com.mit_pdos.tulip.trusted_proph.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Txn := struct.decl [
  "ts" :: uint64T;
  "wrs" :: mapT (mapT (struct.t tulip.Value));
  "ptgs" :: slice.T uint64T;
  "gcoords" :: mapT ptrT;
  "proph" :: ProphIdT
].

Definition GetTS: val :=
  rec: "GetTS" <> :=
    #0.

Definition Txn__begin: val :=
  rec: "Txn__begin" "txn" :=
    struct.storeF Txn "ts" "txn" (GetTS #());;
    #().

Definition Txn__resetwrs: val :=
  rec: "Txn__resetwrs" "txn" :=
    let: "wrs" := NewMap uint64T (mapT (struct.t tulip.Value)) #() in
    MapIter (struct.loadF Txn "wrs" "txn") (λ: "gid" <>,
      MapInsert "wrs" "gid" (NewMap stringT (struct.t tulip.Value) #()));;
    struct.storeF Txn "wrs" "txn" "wrs";;
    #().

Definition KeyToGroup: val :=
  rec: "KeyToGroup" "key" :=
    #0.

Definition Txn__setwrs: val :=
  rec: "Txn__setwrs" "txn" "key" "value" :=
    let: "gid" := KeyToGroup "key" in
    let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
    MapInsert "pwrs" "key" "value";;
    #().

Definition Txn__getwrs: val :=
  rec: "Txn__getwrs" "txn" "key" :=
    let: "gid" := KeyToGroup "key" in
    let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
    let: ("v", "ok") := MapGet "pwrs" "key" in
    ("v", "ok").

Definition Txn__resetptgs: val :=
  rec: "Txn__resetptgs" "txn" :=
    struct.storeF Txn "ptgs" "txn" (SliceTake (struct.loadF Txn "ptgs" "txn") #0);;
    #().

Definition Txn__setptgs: val :=
  rec: "Txn__setptgs" "txn" :=
    let: "ptgs" := ref_to (slice.T uint64T) (struct.loadF Txn "ptgs" "txn") in
    MapIter (struct.loadF Txn "wrs" "txn") (λ: "gid" "pwrs",
      (if: (MapLen "pwrs") ≠ #0
      then "ptgs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "ptgs") "gid")
      else #()));;
    struct.storeF Txn "ptgs" "txn" (![slice.T uint64T] "ptgs");;
    #().

Definition Txn__reset: val :=
  rec: "Txn__reset" "txn" :=
    Txn__resetwrs "txn";;
    Txn__resetptgs "txn";;
    #().

Definition Txn__prepare: val :=
  rec: "Txn__prepare" "txn" :=
    Txn__setptgs "txn";;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    let: "ptgs" := struct.loadF Txn "ptgs" "txn" in
    let: "mu" := newMutex #() in
    let: "cv" := NewCond "mu" in
    let: "np" := ref_to uint64T #0 in
    let: "st" := ref_to uint64T tulip.TXN_PREPARED in
    ForSlice uint64T <> "gid" "ptgs"
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
      Fork (let: ("stg", "ok") := gcoord.GroupCoordinator__Prepare "gcoord" "ts" "ptgs" "pwrs" in
            (if: "ok"
            then
              Mutex__Lock "mu";;
              (if: "stg" = tulip.TXN_PREPARED
              then "np" <-[uint64T] ((![uint64T] "np") + #1)
              else "st" <-[uint64T] "stg");;
              Mutex__Unlock "mu";;
              Cond__Signal "cv"
            else #())));;
    Mutex__Lock "mu";;
    Skip;;
    (for: (λ: <>, ((![uint64T] "st") = tulip.TXN_PREPARED) && ((![uint64T] "np") ≠ (slice.len "ptgs"))); (λ: <>, Skip) := λ: <>,
      Cond__Wait "cv";;
      Continue);;
    let: "status" := ![uint64T] "st" in
    Mutex__Unlock "mu";;
    "status".

Definition Txn__commit: val :=
  rec: "Txn__commit" "txn" :=
    trusted_proph.ResolveCommit (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") (struct.loadF Txn "wrs" "txn");;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
      Fork (gcoord.GroupCoordinator__Commit "gcoord" "ts" "pwrs"));;
    #().

Definition Txn__abort: val :=
  rec: "Txn__abort" "txn" :=
    trusted_proph.ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    let: "ts" := struct.loadF Txn "ts" "txn" in
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      Fork (gcoord.GroupCoordinator__Abort "gcoord" "ts"));;
    #().

Definition Txn__cancel: val :=
  rec: "Txn__cancel" "txn" :=
    trusted_proph.ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    Txn__reset "txn";;
    #().

Definition Txn__Read: val :=
  rec: "Txn__Read" "txn" "key" :=
    let: ("vlocal", "ok") := Txn__getwrs "txn" "key" in
    (if: "ok"
    then "vlocal"
    else
      let: "gid" := KeyToGroup "key" in
      let: "gcoord" := Fst (MapGet (struct.loadF Txn "gcoords" "txn") "gid") in
      let: "v" := gcoord.GroupCoordinator__Read "gcoord" (struct.loadF Txn "ts" "txn") "key" in
      trusted_proph.ResolveRead (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") "key";;
      "v").

Definition Txn__Write: val :=
  rec: "Txn__Write" "txn" "key" "value" :=
    let: "v" := struct.mk tulip.Value [
      "Present" ::= #true;
      "Content" ::= "value"
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

Definition Txn__Delete: val :=
  rec: "Txn__Delete" "txn" "key" :=
    let: "v" := struct.mk tulip.Value [
      "Present" ::= #false
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

Definition Txn__Run: val :=
  rec: "Txn__Run" "txn" "body" :=
    Txn__begin "txn";;
    let: "cmt" := "body" "txn" in
    (if: (~ "cmt")
    then
      Txn__cancel "txn";;
      #false
    else
      let: "status" := Txn__prepare "txn" in
      (if: "status" = tulip.TXN_COMMITTED
      then
        Txn__reset "txn";;
        #true
      else
        (if: "status" = tulip.TXN_ABORTED
        then
          Txn__abort "txn";;
          #false
        else
          Txn__commit "txn";;
          #true))).
