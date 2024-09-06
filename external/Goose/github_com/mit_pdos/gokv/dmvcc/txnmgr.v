(* autogenerated from github.com/mit-pdos/gokv/dmvcc/txnmgr *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

(* clerk.go *)

Definition Clerk := struct.decl [
].

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "p" :: ProphIdT;
  "nextTid" :: uint64T
].

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "p" := NewProph #() in
    let: "txnMgr" := struct.new Server [
      "p" ::= "p";
      "nextTid" ::= #1
    ] in
    struct.storeF Server "mu" "txnMgr" (lock.new #());;
    "txnMgr".

Definition Server__New: val :=
  rec: "Server__New" "txnMgr" :=
    lock.acquire (struct.loadF Server "mu" "txnMgr");;
    let: "tid" := struct.loadF Server "nextTid" "txnMgr" in
    struct.storeF Server "nextTid" "txnMgr" ((struct.loadF Server "nextTid" "txnMgr") + #1);;
    lock.release (struct.loadF Server "mu" "txnMgr");;
    "tid".

End code.
