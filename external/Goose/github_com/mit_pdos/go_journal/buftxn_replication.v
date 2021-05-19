(* autogenerated from github.com/mit-pdos/go-journal/buftxn_replication *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.jrnl.
From Goose Require github_com.mit_pdos.go_journal.common.
From Goose Require github_com.mit_pdos.go_journal.obj.
From Goose Require github_com.mit_pdos.go_journal.util.

Definition RepBlock := struct.decl [
  "txn" :: struct.ptrT txn.Txn;
  "m" :: lockRefT;
  "a0" :: struct.t addr.Addr;
  "a1" :: struct.t addr.Addr
].

Definition Open: val :=
  rec: "Open" "txn" "a" :=
    struct.new RepBlock [
      "txn" ::= "txn";
      "m" ::= lock.new #();
      "a0" ::= addr.MkAddr "a" #0;
      "a1" ::= addr.MkAddr ("a" + #1) #0
    ].

(* can fail in principle if CommitWait fails,
   but that's really impossible since it's an empty transaction *)
Definition RepBlock__Read: val :=
  rec: "RepBlock__Read" "rb" :=
    lock.acquire (struct.loadF RepBlock "m" "rb");;
    let: "tx" := buftxn.Begin (struct.loadF RepBlock "txn" "rb") in
    let: "buf" := buftxn.BufTxn__ReadBuf "tx" (struct.loadF RepBlock "a0" "rb") (#8 * disk.BlockSize) in
    let: "b" := util.CloneByteSlice (struct.loadF buf.Buf "Data" "buf") in
    let: "ok" := buftxn.BufTxn__CommitWait "tx" #true in
    lock.release (struct.loadF RepBlock "m" "rb");;
    ("b", "ok").

Definition RepBlock__Write: val :=
  rec: "RepBlock__Write" "rb" "b" :=
    lock.acquire (struct.loadF RepBlock "m" "rb");;
    let: "tx" := buftxn.Begin (struct.loadF RepBlock "txn" "rb") in
    buftxn.BufTxn__OverWrite "tx" (struct.loadF RepBlock "a0" "rb") (#8 * disk.BlockSize) "b";;
    buftxn.BufTxn__OverWrite "tx" (struct.loadF RepBlock "a1" "rb") (#8 * disk.BlockSize) "b";;
    let: "ok" := buftxn.BufTxn__CommitWait "tx" #true in
    lock.release (struct.loadF RepBlock "m" "rb");;
    "ok".