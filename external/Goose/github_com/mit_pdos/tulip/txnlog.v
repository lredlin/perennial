(* autogenerated from github.com/mit-pdos/tulip/txnlog *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.paxos.
From Goose Require github_com.mit_pdos.tulip.tulip.
From Goose Require github_com.mit_pdos.tulip.util.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Cmd := struct.decl [
  "Kind" :: uint64T;
  "Timestamp" :: uint64T;
  "PartialWrites" :: slice.T (struct.t tulip.WriteEntry)
].

Definition TxnLog := struct.decl [
  "px" :: ptrT
].

Definition TXNLOG_ABORT : expr := #0.

Definition TXNLOG_COMMIT : expr := #1.

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @lsn (uint64): @lsn = 0 indicates failure; otherwise, this indicates the
   logical index this command is supposed to be placed at.

   @term (uint64): The @term this command is supposed to have.

   Notes:
   1) Passing @lsn and @term to @WaitUntilSafe allows us to determine whether
   the command we just submitted actually get safely replicated (and wait until
   that happens up to some timeout).

   2) Although @term is redundant in that we can always detect failure by
   comparing the content of the command to some application state (e.g., a reply
   table), it can be seen as a performance optimization that would allow us to
   know earlier that our command has not been safely replicated (and hence
   resubmit). Another upside of having it would be that this allows the check to
   be done in a general way, without relying on the content. *)
Definition TxnLog__SubmitCommit: val :=
  rec: "TxnLog__SubmitCommit" "log" "ts" "pwrs" :=
    let: "bs" := NewSliceWithCap byteT #0 #64 in
    let: "bs1" := marshal.WriteInt "bs" TXNLOG_COMMIT in
    let: "bs2" := marshal.WriteInt "bs1" "ts" in
    let: "data" := util.EncodeKVMapFromSlice "bs2" "pwrs" in
    let: ("lsn", "term") := paxos.Paxos__Submit (struct.loadF TxnLog "px" "log") (StringFromBytes "data") in
    ("lsn", "term").

(* Arguments and return values: see description of @SubmitPrepare. *)
Definition TxnLog__SubmitAbort: val :=
  rec: "TxnLog__SubmitAbort" "log" "ts" :=
    let: "bs" := NewSliceWithCap byteT #0 #8 in
    let: "bs1" := marshal.WriteInt "bs" TXNLOG_ABORT in
    let: "data" := marshal.WriteInt "bs1" "ts" in
    let: ("lsn", "term") := paxos.Paxos__Submit (struct.loadF TxnLog "px" "log") (StringFromBytes "data") in
    ("lsn", "term").

(* Arguments:
   @lsn: LSN of the command whose replication to wait for.

   @term: Expected term of the command.

   Return values:
   @replicated (bool): If @true, then the command at @lsn has term @term;
   otherwise, we know nothing, but the upper layer is suggested to resubmit the
   command.

   TODO: maybe this is a bad interface since now the users would have to make
   another call. *)
Definition TxnLog__WaitUntilSafe: val :=
  rec: "TxnLog__WaitUntilSafe" "log" "lsn" "term" :=
    paxos.Paxos__WaitUntilSafe (struct.loadF TxnLog "px" "log") "lsn" "term".

(* Argument:
   @lsn: Logical index of the queried command. *)
Definition TxnLog__Lookup: val :=
  rec: "TxnLog__Lookup" "log" "lsn" :=
    let: ("s", "ok") := paxos.Paxos__Lookup (struct.loadF TxnLog "px" "log") "lsn" in
    (if: (~ "ok")
    then
      (struct.mk Cmd [
       ], #false)
    else
      let: "bs" := StringToBytes "s" in
      let: ("kind", "bs1") := marshal.ReadInt "bs" in
      (if: "kind" = TXNLOG_COMMIT
      then
        let: ("ts", "bs2") := marshal.ReadInt "bs1" in
        let: ("pwrs", <>) := util.DecodeKVMapIntoSlice "bs2" in
        let: "cmd" := struct.mk Cmd [
          "Kind" ::= TXNLOG_COMMIT;
          "Timestamp" ::= "ts";
          "PartialWrites" ::= "pwrs"
        ] in
        ("cmd", #true)
      else
        (if: "kind" = TXNLOG_ABORT
        then
          let: ("ts", <>) := marshal.ReadInt "bs1" in
          let: "cmd" := struct.mk Cmd [
            "Kind" ::= TXNLOG_ABORT;
            "Timestamp" ::= "ts"
          ] in
          ("cmd", #true)
        else
          (struct.mk Cmd [
           ], #false)))).

Definition TxnLog__DumpState: val :=
  rec: "TxnLog__DumpState" "log" :=
    paxos.Paxos__DumpState (struct.loadF TxnLog "px" "log");;
    #().

Definition TxnLog__ForceElection: val :=
  rec: "TxnLog__ForceElection" "log" :=
    paxos.Paxos__ForceElection (struct.loadF TxnLog "px" "log");;
    #().

Definition Start: val :=
  rec: "Start" "nidme" "addrm" "fname" :=
    let: "px" := paxos.Start "nidme" "addrm" "fname" in
    let: "txnlog" := struct.new TxnLog [
      "px" ::= "px"
    ] in
    "txnlog".
