(* autogenerated from github.com/mit-pdos/rsm/distx *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.

Section code.
Context `{ext_ty: ext_types}.

Definition Value := struct.decl [
  "b" :: boolT;
  "s" :: stringT
].

Definition WriteEntry := struct.decl [
  "k" :: stringT;
  "v" :: struct.t Value
].

Definition N_SHARDS : expr := #2.

(* @ts
   Starting timestamp of this version, and also ending timestamp of the next
   version. Lifetime is a half-open interval: [ts of this, ts of next).

   @val
   Value of this version. *)
Definition Version := struct.decl [
  "ts" :: uint64T;
  "val" :: struct.t Value
].

Definition Tuple__Own: val :=
  rec: "Tuple__Own" "tuple" "tid" :=
    #false.

Definition Tuple__ReadVersion: val :=
  rec: "Tuple__ReadVersion" "tuple" "tid" :=
    (struct.mk Value [
     ], #false).

Definition Tuple__Extend: val :=
  rec: "Tuple__Extend" "tuple" "tid" :=
    #false.

Definition Tuple__AppendVersion: val :=
  rec: "Tuple__AppendVersion" "tuple" "tid" "val" :=
    #().

Definition Tuple__KillVersion: val :=
  rec: "Tuple__KillVersion" "tuple" "tid" :=
    #().

Definition Tuple__Free: val :=
  rec: "Tuple__Free" "tuple" :=
    #().

(* @owned
   Write lock of this tuple. Acquired before committing.

   @tslast
   Timestamp of the last reader or last writer + 1.

   @vers
   Versions. *)
Definition Tuple := struct.decl [
  "latch" :: ptrT;
  "owned" :: boolT;
  "tslast" :: uint64T;
  "vers" :: slice.T (struct.t Version)
].

Definition Index := struct.decl [
].

Definition Index__GetTuple: val :=
  rec: "Index__GetTuple" "idx" "key" :=
    struct.new Tuple [
    ].

Definition Cmd := struct.decl [
  "kind" :: uint64T;
  "ts" :: uint64T;
  "pwrs" :: slice.T (struct.t WriteEntry);
  "key" :: stringT
].

Definition TxnLog := struct.decl [
].

(* Arguments:
   @ts: Transaction timestamp.

   @wrs: Transaction write set.

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
Definition TxnLog__SubmitPrepare: val :=
  rec: "TxnLog__SubmitPrepare" "log" "ts" "pwrs" :=
    (#0, #0).

(* Arguments:
   @ts: Transaction timestamp.

   @key: Key to be read.

   Return values: see description of @SubmitPrepare. *)
Definition TxnLog__SubmitRead: val :=
  rec: "TxnLog__SubmitRead" "log" "ts" "key" :=
    (#0, #0).

(* Arguments and return values: see description of @SubmitPrepare. *)
Definition TxnLog__SubmitCommit: val :=
  rec: "TxnLog__SubmitCommit" "log" "ts" :=
    (#0, #0).

(* Arguments and return values: see description of @SubmitPrepare. *)
Definition TxnLog__SubmitAbort: val :=
  rec: "TxnLog__SubmitAbort" "log" "ts" :=
    (#0, #0).

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
    #false.

(* Argument:
   @lsn: Logical index of the queried command. *)
Definition TxnLog__Lookup: val :=
  rec: "TxnLog__Lookup" "log" "lsn" :=
    (struct.mk Cmd [
     ], #false).

Definition Replica := struct.decl [
  "mu" :: ptrT;
  "rid" :: uint64T;
  "txnlog" :: ptrT;
  "lsna" :: uint64T;
  "prepm" :: mapT (slice.T (struct.t WriteEntry));
  "txntbl" :: mapT boolT;
  "idx" :: ptrT
].

Definition Replica__WaitUntilApplied: val :=
  rec: "Replica__WaitUntilApplied" "rp" "lsn" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      lock.acquire (struct.loadF Replica "mu" "rp");;
      let: "lsna" := struct.loadF Replica "lsna" "rp" in
      lock.release (struct.loadF Replica "mu" "rp");;
      (if: "lsn" ≤ "lsna"
      then Break
      else
        time.Sleep (#1 * #1000000);;
        Continue));;
    #().

Definition TXN_RUNNING : expr := #0.

Definition TXN_PREPARED : expr := #1.

Definition TXN_COMMITTED : expr := #2.

Definition TXN_ABORTED : expr := #3.

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @status: Transaction status. *)
Definition Replica__queryTxnStatus: val :=
  rec: "Replica__queryTxnStatus" "rp" "ts" :=
    let: ("cmted", "terminated") := MapGet (struct.loadF Replica "txntbl" "rp") "ts" in
    (if: "terminated"
    then
      (if: "cmted"
      then TXN_COMMITTED
      else TXN_ABORTED)
    else
      let: (<>, "preped") := MapGet (struct.loadF Replica "prepm" "rp") "ts" in
      (if: "preped"
      then TXN_PREPARED
      else TXN_RUNNING)).

Definition Replica__QueryTxnStatus: val :=
  rec: "Replica__QueryTxnStatus" "rp" "ts" :=
    lock.acquire (struct.loadF Replica "mu" "rp");;
    let: "status" := Replica__queryTxnStatus "rp" "ts" in
    lock.release (struct.loadF Replica "mu" "rp");;
    "status".

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @terminated: Whether txn @ts has terminated (committed or aborted). *)
Definition Replica__queryTxnTermination: val :=
  rec: "Replica__queryTxnTermination" "rp" "ts" :=
    let: (<>, "terminated") := MapGet (struct.loadF Replica "txntbl" "rp") "ts" in
    "terminated".

Definition Replica__QueryTxnTermination: val :=
  rec: "Replica__QueryTxnTermination" "rp" "ts" :=
    lock.acquire (struct.loadF Replica "mu" "rp");;
    let: "terminated" := Replica__queryTxnTermination "rp" "ts" in
    lock.release (struct.loadF Replica "mu" "rp");;
    "terminated".

(* Arguments:
   @ts: Transaction timestamp.

   @wrs: Transaction write set.

   Return values:
   @status: Transaction status.

   @ok: If @true, @status is meaningful; otherwise, ignore @status. A @false
   indicates this replica might not be the leader, so the upper layer is
   suggested to retry with a different replica. *)
Definition Replica__Prepare: val :=
  rec: "Replica__Prepare" "rp" "ts" "pwrs" :=
    let: "status" := Replica__QueryTxnStatus "rp" "ts" in
    (if: "status" ≠ TXN_RUNNING
    then ("status", #true)
    else
      let: ("lsn", "term") := TxnLog__SubmitPrepare (struct.loadF Replica "txnlog" "rp") "ts" "pwrs" in
      (if: "lsn" = #0
      then (#0, #false)
      else
        let: "safe" := TxnLog__WaitUntilSafe (struct.loadF Replica "txnlog" "rp") "lsn" "term" in
        (if: (~ "safe")
        then (#0, #false)
        else
          Replica__WaitUntilApplied "rp" "lsn";;
          let: "ret" := Replica__QueryTxnStatus "rp" "ts" in
          ("ret", #true)))).

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @ok: If @true, this transaction is committed. *)
Definition Replica__Commit: val :=
  rec: "Replica__Commit" "rp" "ts" :=
    let: "committed" := Replica__QueryTxnTermination "rp" "ts" in
    (if: "committed"
    then #true
    else
      let: ("lsn", "term") := TxnLog__SubmitCommit (struct.loadF Replica "txnlog" "rp") "ts" in
      (if: "lsn" = #0
      then #false
      else
        let: "safe" := TxnLog__WaitUntilSafe (struct.loadF Replica "txnlog" "rp") "lsn" "term" in
        (if: (~ "safe")
        then #false
        else #true))).

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @ok: If @true, this transaction is aborted. *)
Definition Replica__Abort: val :=
  rec: "Replica__Abort" "rp" "ts" :=
    let: "aborted" := Replica__QueryTxnTermination "rp" "ts" in
    (if: "aborted"
    then #true
    else
      let: ("lsn", "term") := TxnLog__SubmitAbort (struct.loadF Replica "txnlog" "rp") "ts" in
      (if: "lsn" = #0
      then #false
      else
        let: "safe" := TxnLog__WaitUntilSafe (struct.loadF Replica "txnlog" "rp") "lsn" "term" in
        (if: (~ "safe")
        then #false
        else #true))).

(* Arguments:
   @ts: Transaction timestamp.

   @key: Key to be read.

   Return values:
   @value: Value of the key.

   @ok: @value is meaningful iff @ok is true. *)
Definition Replica__Read: val :=
  rec: "Replica__Read" "rp" "ts" "key" :=
    let: "terminated" := Replica__QueryTxnTermination "rp" "ts" in
    (if: "terminated"
    then
      (struct.mk Value [
       ], #false)
    else
      let: ("lsn", "term") := TxnLog__SubmitRead (struct.loadF Replica "txnlog" "rp") "ts" "key" in
      (if: "lsn" = #0
      then
        (struct.mk Value [
         ], #false)
      else
        let: "safe" := TxnLog__WaitUntilSafe (struct.loadF Replica "txnlog" "rp") "lsn" "term" in
        (if: (~ "safe")
        then
          (struct.mk Value [
           ], #false)
        else
          Replica__WaitUntilApplied "rp" "lsn";;
          let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") "key" in
          let: ("v", "ok") := Tuple__ReadVersion "tpl" "ts" in
          ("v", "ok")))).

Definition Replica__applyRead: val :=
  rec: "Replica__applyRead" "rp" "ts" "key" :=
    let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") "key" in
    Tuple__Extend "tpl" "ts";;
    #().

Definition Replica__validate: val :=
  rec: "Replica__validate" "rp" "ts" "pwrs" :=
    let: "pos" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "pos") < (slice.len "pwrs")); (λ: <>, Skip) := λ: <>,
      let: "ent" := SliceGet (struct.t WriteEntry) "pwrs" (![uint64T] "pos") in
      let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") (struct.get WriteEntry "k" "ent") in
      let: "ret" := Tuple__Own "tpl" "ts" in
      (if: (~ "ret")
      then Break
      else
        "pos" <-[uint64T] ((![uint64T] "pos") + #1);;
        Continue));;
    (if: (![uint64T] "pos") < (slice.len "pwrs")
    then
      let: "i" := ref_to uint64T #0 in
      Skip;;
      (for: (λ: <>, (![uint64T] "i") < (![uint64T] "pos")); (λ: <>, Skip) := λ: <>,
        let: "ent" := SliceGet (struct.t WriteEntry) "pwrs" (![uint64T] "i") in
        let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") (struct.get WriteEntry "k" "ent") in
        Tuple__Free "tpl";;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue);;
      #false
    else #true).

Definition Replica__applyPrepare: val :=
  rec: "Replica__applyPrepare" "rp" "ts" "pwrs" :=
    let: "status" := Replica__queryTxnStatus "rp" "ts" in
    (if: "status" ≠ TXN_RUNNING
    then #()
    else
      let: "ok" := Replica__validate "rp" "ts" "pwrs" in
      (if: (~ "ok")
      then
        MapInsert (struct.loadF Replica "txntbl" "rp") "ts" #false;;
        #()
      else
        MapInsert (struct.loadF Replica "prepm" "rp") "ts" "pwrs";;
        #())).

Definition Replica__multiwrite: val :=
  rec: "Replica__multiwrite" "rp" "ts" "pwrs" :=
    ForSlice (struct.t WriteEntry) <> "ent" "pwrs"
      (let: "key" := struct.get WriteEntry "k" "ent" in
      let: "value" := struct.get WriteEntry "v" "ent" in
      let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") "key" in
      (if: struct.get Value "b" "value"
      then Tuple__AppendVersion "tpl" "ts" (struct.get Value "s" "value")
      else Tuple__KillVersion "tpl" "ts");;
      Tuple__Free "tpl");;
    #().

Definition Replica__applyCommit: val :=
  rec: "Replica__applyCommit" "rp" "ts" :=
    let: "committed" := Replica__queryTxnTermination "rp" "ts" in
    (if: "committed"
    then #()
    else
      let: "pwrs" := Fst (MapGet (struct.loadF Replica "prepm" "rp") "ts") in
      Replica__multiwrite "rp" "ts" "pwrs";;
      MapDelete (struct.loadF Replica "prepm" "rp") "ts";;
      MapInsert (struct.loadF Replica "txntbl" "rp") "ts" #true;;
      #()).

Definition Replica__abort: val :=
  rec: "Replica__abort" "rp" "pwrs" :=
    ForSlice (struct.t WriteEntry) <> "ent" "pwrs"
      (let: "key" := struct.get WriteEntry "k" "ent" in
      let: "tpl" := Index__GetTuple (struct.loadF Replica "idx" "rp") "key" in
      Tuple__Free "tpl");;
    #().

Definition Replica__applyAbort: val :=
  rec: "Replica__applyAbort" "rp" "ts" :=
    let: "aborted" := Replica__queryTxnTermination "rp" "ts" in
    (if: "aborted"
    then #()
    else
      let: ("pwrs", "prepared") := MapGet (struct.loadF Replica "prepm" "rp") "ts" in
      (if: "prepared"
      then
        Replica__abort "rp" "pwrs";;
        MapDelete (struct.loadF Replica "prepm" "rp") "ts"
      else #());;
      MapInsert (struct.loadF Replica "txntbl" "rp") "ts" #false;;
      #()).

Definition Replica__apply: val :=
  rec: "Replica__apply" "rp" "cmd" :=
    (if: (struct.get Cmd "kind" "cmd") = #0
    then
      Replica__applyRead "rp" (struct.get Cmd "ts" "cmd") (struct.get Cmd "key" "cmd");;
      #()
    else
      (if: (struct.get Cmd "kind" "cmd") = #1
      then
        Replica__applyPrepare "rp" (struct.get Cmd "ts" "cmd") (struct.get Cmd "pwrs" "cmd");;
        #()
      else
        (if: (struct.get Cmd "kind" "cmd") = #2
        then
          Replica__applyCommit "rp" (struct.get Cmd "ts" "cmd");;
          #()
        else
          Replica__applyAbort "rp" (struct.get Cmd "ts" "cmd");;
          #()))).

Definition Replica__Start: val :=
  rec: "Replica__Start" "rp" :=
    lock.acquire (struct.loadF Replica "mu" "rp");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "lsn" := std.SumAssumeNoOverflow (struct.loadF Replica "lsna" "rp") #1 in
      let: ("cmd", "ok") := TxnLog__Lookup (struct.loadF Replica "txnlog" "rp") "lsn" in
      (if: (~ "ok")
      then
        lock.release (struct.loadF Replica "mu" "rp");;
        time.Sleep (#1 * #1000000);;
        lock.acquire (struct.loadF Replica "mu" "rp");;
        Continue
      else
        Replica__apply "rp" "cmd";;
        struct.storeF Replica "lsna" "rp" "lsn";;
        Continue));;
    #().

Definition ReplicaGroup := struct.decl [
  "leader" :: uint64T;
  "rps" :: slice.T ptrT
].

Definition ReplicaGroup__changeLeader: val :=
  rec: "ReplicaGroup__changeLeader" "rg" :=
    #().

Definition slicem: val :=
  rec: "slicem" "m" :=
    slice.nil.

(* Arguments:
   @ts: Transaction timestamp.
   @key: Key to be read.

   Return values:
   @value: Value of @key at timestamp @ts. *)
Definition ReplicaGroup__Read: val :=
  rec: "ReplicaGroup__Read" "rg" "ts" "key" :=
    let: "value" := ref (zero_val (struct.t Value)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rp" := SliceGet ptrT (struct.loadF ReplicaGroup "rps" "rg") (struct.loadF ReplicaGroup "leader" "rg") in
      let: ("v", "ok") := Replica__Read "rp" "ts" "key" in
      (if: "ok"
      then
        "value" <-[struct.t Value] "v";;
        Break
      else
        ReplicaGroup__changeLeader "rg";;
        Continue));;
    ![struct.t Value] "value".

(* Arguments:
   @ts: Transaction timestamp.

   Return values:
   @status: Transactin status. *)
Definition ReplicaGroup__Prepare: val :=
  rec: "ReplicaGroup__Prepare" "rg" "ts" "pwrs" :=
    let: "status" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rp" := SliceGet ptrT (struct.loadF ReplicaGroup "rps" "rg") (struct.loadF ReplicaGroup "leader" "rg") in
      let: ("s", "ok") := Replica__Prepare "rp" "ts" "pwrs" in
      (if: "ok"
      then
        "status" <-[uint64T] "s";;
        Break
      else
        ReplicaGroup__changeLeader "rg";;
        Continue));;
    ![uint64T] "status".

Definition ReplicaGroup__Commit: val :=
  rec: "ReplicaGroup__Commit" "rg" "ts" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rp" := SliceGet ptrT (struct.loadF ReplicaGroup "rps" "rg") (struct.loadF ReplicaGroup "leader" "rg") in
      let: "ok" := Replica__Commit "rp" "ts" in
      (if: "ok"
      then Break
      else
        ReplicaGroup__changeLeader "rg";;
        Continue));;
    #().

Definition ReplicaGroup__Abort: val :=
  rec: "ReplicaGroup__Abort" "rg" "ts" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rp" := SliceGet ptrT (struct.loadF ReplicaGroup "rps" "rg") (struct.loadF ReplicaGroup "leader" "rg") in
      let: "ok" := Replica__Abort "rp" "ts" in
      (if: "ok"
      then Break
      else
        ReplicaGroup__changeLeader "rg";;
        Continue));;
    #().

Definition Txn := struct.decl [
  "ts" :: uint64T;
  "rgs" :: mapT ptrT;
  "wrs" :: mapT (mapT (struct.t Value));
  "ptgs" :: slice.T uint64T;
  "proph" :: ProphIdT
].

Notation ProphId := ProphIdT (only parsing).

Definition ResolveRead: val :=
  rec: "ResolveRead" "p" "tid" "key" :=
    #().

Definition ResolveAbort: val :=
  rec: "ResolveAbort" "p" "tid" :=
    #().

Definition ResolveCommit: val :=
  rec: "ResolveCommit" "p" "tid" "wrs" :=
    #().

Definition GetTS: val :=
  rec: "GetTS" <> :=
    #0.

Definition Txn__begin: val :=
  rec: "Txn__begin" "txn" :=
    struct.storeF Txn "ts" "txn" (GetTS #());;
    #().

Definition Txn__resetwrs: val :=
  rec: "Txn__resetwrs" "txn" :=
    let: "wrs" := NewMap uint64T (mapT (struct.t Value)) #() in
    MapIter (struct.loadF Txn "wrs" "txn") (λ: "gid" <>,
      MapInsert "wrs" "gid" (NewMap stringT (struct.t Value) #()));;
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

(* Main proof for this simplified program. *)
Definition Txn__prepare: val :=
  rec: "Txn__prepare" "txn" :=
    let: "status" := ref_to uint64T TXN_PREPARED in
    Txn__setptgs "txn";;
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (slice.len (struct.loadF Txn "ptgs" "txn"))); (λ: <>, Skip) := λ: <>,
      let: "gid" := SliceGet uint64T (struct.loadF Txn "ptgs" "txn") (![uint64T] "i") in
      let: "rg" := Fst (MapGet (struct.loadF Txn "rgs" "txn") "gid") in
      let: "pwrs" := Fst (MapGet (struct.loadF Txn "wrs" "txn") "gid") in
      "status" <-[uint64T] (ReplicaGroup__Prepare "rg" (struct.loadF Txn "ts" "txn") (slicem "pwrs"));;
      (if: (![uint64T] "status") ≠ TXN_PREPARED
      then Break
      else
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![uint64T] "status".

Definition Txn__commit: val :=
  rec: "Txn__commit" "txn" :=
    ResolveCommit (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") (struct.loadF Txn "wrs" "txn");;
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "rg" := Fst (MapGet (struct.loadF Txn "rgs" "txn") "gid") in
      ReplicaGroup__Commit "rg" (struct.loadF Txn "ts" "txn"));;
    Txn__reset "txn";;
    #().

Definition Txn__abort: val :=
  rec: "Txn__abort" "txn" :=
    ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    ForSlice uint64T <> "gid" (struct.loadF Txn "ptgs" "txn")
      (let: "rg" := Fst (MapGet (struct.loadF Txn "rgs" "txn") "gid") in
      ReplicaGroup__Abort "rg" (struct.loadF Txn "ts" "txn"));;
    Txn__reset "txn";;
    #().

Definition Txn__cancel: val :=
  rec: "Txn__cancel" "txn" :=
    ResolveAbort (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn");;
    Txn__reset "txn";;
    #().

Definition Txn__Read: val :=
  rec: "Txn__Read" "txn" "key" :=
    let: ("vlocal", "ok") := Txn__getwrs "txn" "key" in
    (if: "ok"
    then "vlocal"
    else
      let: "gid" := KeyToGroup "key" in
      let: "rg" := Fst (MapGet (struct.loadF Txn "rgs" "txn") "gid") in
      let: "v" := ReplicaGroup__Read "rg" (struct.loadF Txn "ts" "txn") "key" in
      ResolveRead (struct.loadF Txn "proph" "txn") (struct.loadF Txn "ts" "txn") "key";;
      "v").

Definition Txn__Write: val :=
  rec: "Txn__Write" "txn" "key" "value" :=
    let: "v" := struct.mk Value [
      "b" ::= #true;
      "s" ::= "value"
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

Definition Txn__Delete: val :=
  rec: "Txn__Delete" "txn" "key" :=
    let: "v" := struct.mk Value [
      "b" ::= #false
    ] in
    Txn__setwrs "txn" "key" "v";;
    #().

(* Main proof for this simplifed program. *)
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
      (if: "status" = TXN_COMMITTED
      then
        Txn__reset "txn";;
        #true
      else
        (if: "status" = TXN_ABORTED
        then
          Txn__abort "txn";;
          #false
        else
          Txn__commit "txn";;
          #true))).

Definition NewTxn: val :=
  rec: "NewTxn" <> :=
    struct.new Txn [
    ].

(* Example *)
Definition swap: val :=
  rec: "swap" "txn" :=
    let: "x" := Txn__Read "txn" #(str"0") in
    let: "y" := Txn__Read "txn" #(str"1") in
    Txn__Write "txn" #(str"0") (struct.get Value "s" "y");;
    Txn__Write "txn" #(str"1") (struct.get Value "s" "x");;
    #true.

Definition AtomicSwap: val :=
  rec: "AtomicSwap" <> :=
    let: "txn" := NewTxn #() in
    let: "committed" := Txn__Run "txn" swap in
    "committed".

End code.
