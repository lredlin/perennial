(* autogenerated from github.com/mit-pdos/tulip/paxos *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.message.
From Goose Require github_com.mit_pdos.tulip.params.
From Goose Require github_com.mit_pdos.tulip.quorum.
From Goose Require github_com.mit_pdos.tulip.util.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Paxos := struct.decl [
  "peers" :: slice.T uint64T;
  "addrpeers" :: mapT uint64T;
  "me" :: uint64T;
  "sc" :: uint64T;
  "nidme" :: uint64T;
  "mu" :: ptrT;
  "hb" :: boolT;
  "termc" :: uint64T;
  "terml" :: uint64T;
  "log" :: slice.T stringT;
  "lsnc" :: uint64T;
  "iscand" :: boolT;
  "isleader" :: boolT;
  "termp" :: uint64T;
  "entsp" :: slice.T stringT;
  "respp" :: mapT boolT;
  "lsnpeers" :: mapT uint64T;
  "conns" :: mapT grove_ffi.Connection
].

Definition MAX_NODES : expr := #16.

Definition Paxos__Submit: val :=
  rec: "Paxos__Submit" "px" "v" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    (if: (~ (struct.loadF Paxos "isleader" "px"))
    then
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      (#0, #0)
    else
      let: "lsn" := slice.len (struct.loadF Paxos "log" "px") in
      struct.storeF Paxos "log" "px" (SliceAppend stringT (struct.loadF Paxos "log" "px") "v");;
      let: "term" := struct.loadF Paxos "termc" "px" in
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      ("lsn", "term")).

Definition Paxos__Lookup: val :=
  rec: "Paxos__Lookup" "px" "lsn" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    (if: (struct.loadF Paxos "lsnc" "px") ≤ "lsn"
    then
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      (#(str""), #false)
    else
      let: "v" := SliceGet stringT (struct.loadF Paxos "log" "px") "lsn" in
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      ("v", #true)).

(* Return values:
   1. @term: New term in which this node attempts to be the leader.
   2. @lsn: LSN after which log entries whose committedness is yet known, and
   hence the content need to be resolved through the leader-election phase. *)
Definition Paxos__nominate: val :=
  rec: "Paxos__nominate" "px" :=
    let: "term" := util.NextAligned (struct.loadF Paxos "termc" "px") MAX_NODES (struct.loadF Paxos "nidme" "px") in
    struct.storeF Paxos "termc" "px" "term";;
    struct.storeF Paxos "isleader" "px" #false;;
    let: "lsn" := struct.loadF Paxos "lsnc" "px" in
    let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsn") in
    SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsn");;
    struct.storeF Paxos "iscand" "px" #true;;
    struct.storeF Paxos "termp" "px" (struct.loadF Paxos "terml" "px");;
    struct.storeF Paxos "entsp" "px" "ents";;
    struct.storeF Paxos "respp" "px" (NewMap uint64T boolT #());;
    MapInsert (struct.loadF Paxos "respp" "px") (struct.loadF Paxos "nidme" "px") #true;;
    ("term", "lsn").

Definition Paxos__stepdown: val :=
  rec: "Paxos__stepdown" "px" "term" :=
    struct.storeF Paxos "termc" "px" "term";;
    struct.storeF Paxos "iscand" "px" #false;;
    struct.storeF Paxos "isleader" "px" #false;;
    #().

(* Argument:
   1. @lsn: LSN after which log entries whose committedness is yet known, and
   hence the content need to be resolved through the leader-election phase.

   Return values:
   1. @terml: Log term of this node (which is also the largest accepted term
   before @px.termc).
   2. @ents: All entries after @lsn. *)
Definition Paxos__prepare: val :=
  rec: "Paxos__prepare" "px" "lsn" :=
    (if: (slice.len (struct.loadF Paxos "log" "px")) ≤ "lsn"
    then (struct.loadF Paxos "terml" "px", NewSlice stringT #0)
    else
      let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsn") in
      SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsn");;
      (struct.loadF Paxos "terml" "px", "ents")).

Definition Paxos__collect: val :=
  rec: "Paxos__collect" "px" "nid" "term" "ents" :=
    let: (<>, "recved") := MapGet (struct.loadF Paxos "respp" "px") "nid" in
    (if: "recved"
    then #()
    else
      (if: "term" < (struct.loadF Paxos "termp" "px")
      then
        MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
        #()
      else
        (if: ("term" = (struct.loadF Paxos "termp" "px")) && ((slice.len "ents") ≤ (slice.len (struct.loadF Paxos "entsp" "px")))
        then
          MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
          #()
        else
          struct.storeF Paxos "termp" "px" "term";;
          struct.storeF Paxos "entsp" "px" "ents";;
          MapInsert (struct.loadF Paxos "respp" "px") "nid" #true;;
          #()))).

Definition Paxos__cquorum: val :=
  rec: "Paxos__cquorum" "px" "n" :=
    (quorum.ClassicQuorum (struct.loadF Paxos "sc" "px")) ≤ "n".

Definition Paxos__ascend: val :=
  rec: "Paxos__ascend" "px" :=
    (if: (~ (Paxos__cquorum "px" (MapLen (struct.loadF Paxos "respp" "px"))))
    then #()
    else
      struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (SliceTake (struct.loadF Paxos "log" "px") (struct.loadF Paxos "lsnc" "px")) (struct.loadF Paxos "entsp" "px"));;
      struct.storeF Paxos "terml" "px" (struct.loadF Paxos "termc" "px");;
      struct.storeF Paxos "iscand" "px" #false;;
      struct.storeF Paxos "isleader" "px" #true;;
      struct.storeF Paxos "lsnpeers" "px" (NewMap uint64T uint64T #());;
      #()).

Definition Paxos__obtain: val :=
  rec: "Paxos__obtain" "px" "nid" :=
    let: ("lsne", "ok") := MapGet (struct.loadF Paxos "lsnpeers" "px") "nid" in
    (if: (~ "ok")
    then (slice.len (struct.loadF Paxos "log" "px"), NewSlice stringT #0)
    else
      let: "ents" := NewSlice stringT ((slice.len (struct.loadF Paxos "log" "px")) - "lsne") in
      SliceCopy stringT "ents" (SliceSkip stringT (struct.loadF Paxos "log" "px") "lsne");;
      ("lsne", "ents")).

(* Arguments:
   1. @lsn: LSN at which @ents start.
   2. @term: Term to which @ents belong.
   3. @ents: Log entries.

   Return values:
   1. @lsna: LSN up to which log consistency at term @term is established. *)
Definition Paxos__accept: val :=
  rec: "Paxos__accept" "px" "lsn" "term" "ents" :=
    (if: "term" ≠ (struct.loadF Paxos "terml" "px")
    then
      (if: (struct.loadF Paxos "lsnc" "px") ≠ "lsn"
      then struct.loadF Paxos "lsnc" "px"
      else
        struct.storeF Paxos "log" "px" (SliceTake (struct.loadF Paxos "log" "px") "lsn");;
        struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (struct.loadF Paxos "log" "px") "ents");;
        struct.storeF Paxos "terml" "px" "term";;
        let: "lsna" := slice.len (struct.loadF Paxos "log" "px") in
        "lsna")
    else
      let: "nents" := slice.len (struct.loadF Paxos "log" "px") in
      (if: ("nents" < "lsn") || (("lsn" + (slice.len "ents")) ≤ "nents")
      then "nents"
      else
        struct.storeF Paxos "log" "px" (SliceTake (struct.loadF Paxos "log" "px") "lsn");;
        struct.storeF Paxos "log" "px" (SliceAppendSlice stringT (struct.loadF Paxos "log" "px") "ents");;
        let: "lsna" := slice.len (struct.loadF Paxos "log" "px") in
        "lsna")).

Definition Paxos__commit: val :=
  rec: "Paxos__commit" "px" "lsn" :=
    (if: "lsn" ≤ (struct.loadF Paxos "lsnc" "px")
    then #()
    else
      (if: (slice.len (struct.loadF Paxos "log" "px")) < "lsn"
      then
        struct.storeF Paxos "lsnc" "px" (slice.len (struct.loadF Paxos "log" "px"));;
        #()
      else
        struct.storeF Paxos "lsnc" "px" "lsn";;
        #())).

(* @learn monotonically increase the commit LSN @px.lsnc in term @term to @lsn. *)
Definition Paxos__learn: val :=
  rec: "Paxos__learn" "px" "lsn" "term" :=
    (if: "term" ≠ (struct.loadF Paxos "terml" "px")
    then #()
    else
      Paxos__commit "px" "lsn";;
      #()).

Definition Paxos__forward: val :=
  rec: "Paxos__forward" "px" "nid" "lsn" :=
    let: ("lsnpeer", "ok") := MapGet (struct.loadF Paxos "lsnpeers" "px") "nid" in
    (if: (~ "ok") || ("lsnpeer" < "lsn")
    then
      MapInsert (struct.loadF Paxos "lsnpeers" "px") "nid" "lsn";;
      #()
    else #()).

Definition Paxos__push: val :=
  rec: "Paxos__push" "px" :=
    (if: (~ (Paxos__cquorum "px" ((MapLen (struct.loadF Paxos "lsnpeers" "px")) + #1)))
    then (#0, #false)
    else
      let: "lsns" := ref_to (slice.T uint64T) (NewSliceWithCap uint64T #0 (struct.loadF Paxos "sc" "px")) in
      MapIter (struct.loadF Paxos "lsnpeers" "px") (λ: <> "lsn",
        "lsns" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "lsns") "lsn"));;
      util.Sort (![slice.T uint64T] "lsns");;
      let: "lsn" := SliceGet uint64T (![slice.T uint64T] "lsns") ((slice.len (![slice.T uint64T] "lsns")) - ((struct.loadF Paxos "sc" "px") `quot` #2)) in
      ("lsn", #true)).

Definition Paxos__gttermc: val :=
  rec: "Paxos__gttermc" "px" "term" :=
    "term" < (struct.loadF Paxos "termc" "px").

Definition Paxos__lttermc: val :=
  rec: "Paxos__lttermc" "px" "term" :=
    (struct.loadF Paxos "termc" "px") < "term".

Definition Paxos__latest: val :=
  rec: "Paxos__latest" "px" :=
    (struct.loadF Paxos "termc" "px") = (struct.loadF Paxos "terml" "px").

Definition Paxos__gettermc: val :=
  rec: "Paxos__gettermc" "px" :=
    struct.loadF Paxos "termc" "px".

Definition Paxos__getlsnc: val :=
  rec: "Paxos__getlsnc" "px" :=
    struct.loadF Paxos "lsnc" "px".

Definition Paxos__nominated: val :=
  rec: "Paxos__nominated" "px" :=
    struct.loadF Paxos "iscand" "px".

Definition Paxos__leading: val :=
  rec: "Paxos__leading" "px" :=
    struct.loadF Paxos "isleader" "px".

Definition Paxos__heartbeat: val :=
  rec: "Paxos__heartbeat" "px" :=
    struct.storeF Paxos "hb" "px" #true;;
    #().

Definition Paxos__heartbeated: val :=
  rec: "Paxos__heartbeated" "px" :=
    struct.loadF Paxos "hb" "px".

Definition Paxos__GetConnection: val :=
  rec: "Paxos__GetConnection" "px" "nid" :=
    Mutex__Lock (struct.loadF Paxos "mu" "px");;
    let: ("conn", "ok") := MapGet (struct.loadF Paxos "conns" "px") "nid" in
    Mutex__Unlock (struct.loadF Paxos "mu" "px");;
    ("conn", "ok").

Definition Paxos__Connect: val :=
  rec: "Paxos__Connect" "px" "nid" :=
    let: "addr" := Fst (MapGet (struct.loadF Paxos "addrpeers" "px") "nid") in
    let: "ret" := grove_ffi.Connect "addr" in
    (if: (~ (struct.get grove_ffi.ConnectRet "Err" "ret"))
    then
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      MapInsert (struct.loadF Paxos "conns" "px") "nid" (struct.get grove_ffi.ConnectRet "Connection" "ret");;
      Mutex__Unlock (struct.loadF Paxos "mu" "px");;
      #true
    else #false).

Definition Paxos__Send: val :=
  rec: "Paxos__Send" "px" "nid" "data" :=
    let: ("conn", "ok") := Paxos__GetConnection "px" "nid" in
    (if: (~ "ok")
    then Paxos__Connect "px" "nid"
    else #());;
    let: "err" := grove_ffi.Send "conn" "data" in
    (if: "err"
    then
      Paxos__Connect "px" "nid";;
      #()
    else #()).

Definition Paxos__LeaderSession: val :=
  rec: "Paxos__LeaderSession" "px" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      time.Sleep params.NS_BATCH_INTERVAL;;
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      (if: (~ (Paxos__leading "px"))
      then
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue
      else
        ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
          (let: "nid" := "nidloop" in
          let: ("lsne", "ents") := Paxos__obtain "px" "nid" in
          let: "termc" := Paxos__gettermc "px" in
          let: "lsnc" := Paxos__getlsnc "px" in
          Fork (let: "data" := message.EncodePaxosAppendEntriesRequest "termc" "lsnc" "lsne" "ents" in
                Paxos__Send "px" "nid" "data"));;
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue));;
    #().

Definition Paxos__ElectionSession: val :=
  rec: "Paxos__ElectionSession" "px" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      time.Sleep params.NS_ELECTION_TIMEOUT;;
      Mutex__Lock (struct.loadF Paxos "mu" "px");;
      (if: (Paxos__leading "px") || (Paxos__heartbeated "px")
      then
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        Continue
      else
        Paxos__heartbeat "px";;
        let: ("termc", "lsnc") := Paxos__nominate "px" in
        Mutex__Unlock (struct.loadF Paxos "mu" "px");;
        ForSlice uint64T <> "nidloop" (struct.loadF Paxos "peers" "px")
          (let: "nid" := "nidloop" in
          Fork (let: "data" := message.EncodePaxosRequestVoteRequest "termc" "lsnc" in
                Paxos__Send "px" "nid" "data"));;
        Continue));;
    #().

Definition Paxos__Receive: val :=
  rec: "Paxos__Receive" "px" "nid" :=
    let: ("conn", "ok") := Paxos__GetConnection "px" "nid" in
    (if: (~ "ok")
    then
      Paxos__Connect "px" "nid";;
      (slice.nil, #false)
    else
      let: "ret" := grove_ffi.Receive "conn" in
      (if: struct.get grove_ffi.ReceiveRet "Err" "ret"
      then
        Paxos__Connect "px" "nid";;
        (slice.nil, #false)
      else (struct.get grove_ffi.ReceiveRet "Data" "ret", #true))).

Definition Paxos__ResponseSession: val :=
  rec: "Paxos__ResponseSession" "px" "nid" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("data", "ok") := Paxos__Receive "px" "nid" in
      (if: (~ "ok")
      then
        time.Sleep params.NS_RECONNECT;;
        Continue
      else
        let: "resp" := message.DecodePaxosResponse "data" in
        let: "kind" := struct.get message.PaxosResponse "Kind" "resp" in
        Mutex__Lock (struct.loadF Paxos "mu" "px");;
        (if: Paxos__gttermc "px" (struct.get message.PaxosResponse "Term" "resp")
        then
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          Continue
        else
          (if: Paxos__lttermc "px" (struct.get message.PaxosResponse "Term" "resp")
          then
            Paxos__stepdown "px" (struct.get message.PaxosResponse "Term" "resp");;
            Continue
          else
            (if: "kind" = message.MSG_PAXOS_REQUEST_VOTE
            then
              (if: (~ (Paxos__nominated "px"))
              then
                Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                Continue
              else
                Paxos__collect "px" "nid" (struct.get message.PaxosResponse "TermEntries" "resp") (struct.get message.PaxosResponse "Entries" "resp");;
                Paxos__ascend "px";;
                Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                Continue)
            else
              (if: "kind" = message.MSG_PAXOS_APPEND_ENTRIES
              then
                (if: (~ (Paxos__leading "px"))
                then
                  Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                  Continue
                else
                  Paxos__forward "px" "nid" (struct.get message.PaxosResponse "MatchedLSN" "resp");;
                  Mutex__Unlock (struct.loadF Paxos "mu" "px");;
                  Continue)
              else Continue))))));;
    #().

Definition Paxos__RequestSession: val :=
  rec: "Paxos__RequestSession" "px" "conn" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "ret" := grove_ffi.Receive "conn" in
      (if: struct.get grove_ffi.ReceiveRet "Err" "ret"
      then Break
      else
        let: "req" := message.DecodePaxosRequest (struct.get grove_ffi.ReceiveRet "Data" "ret") in
        let: "kind" := struct.get message.PaxosRequest "Kind" "req" in
        Mutex__Lock (struct.loadF Paxos "mu" "px");;
        (if: Paxos__gttermc "px" (struct.get message.PaxosRequest "Term" "req")
        then
          Mutex__Unlock (struct.loadF Paxos "mu" "px");;
          Continue
        else
          Paxos__stepdown "px" (struct.get message.PaxosRequest "Term" "req");;
          Paxos__heartbeat "px";;
          let: "termc" := Paxos__gettermc "px" in
          (if: "kind" = message.MSG_PAXOS_REQUEST_VOTE
          then
            (if: Paxos__latest "px"
            then
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              Continue
            else
              let: ("terml", "ents") := Paxos__prepare "px" (struct.get message.PaxosRequest "CommittedLSN" "req") in
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              let: "data" := message.EncodePaxosRequestVoteResponse "termc" "terml" "ents" in
              grove_ffi.Send "conn" "data";;
              Continue)
          else
            (if: "kind" = message.MSG_PAXOS_APPEND_ENTRIES
            then
              let: "lsn" := Paxos__accept "px" (struct.get message.PaxosRequest "LSNEntries" "req") (struct.get message.PaxosRequest "Term" "req") (struct.get message.PaxosRequest "Entries" "req") in
              Paxos__learn "px" (struct.get message.PaxosRequest "LeaderCommit" "req") (struct.get message.PaxosRequest "Term" "req");;
              Mutex__Unlock (struct.loadF Paxos "mu" "px");;
              let: "data" := message.EncodePaxosAppendEntriesResponse "termc" "lsn" in
              grove_ffi.Send "conn" "data";;
              Continue
            else Continue)))));;
    #().

Definition Paxos__Serve: val :=
  rec: "Paxos__Serve" "px" :=
    let: "ls" := grove_ffi.Listen (struct.loadF Paxos "me" "px") in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "conn" := grove_ffi.Accept "ls" in
      Fork (Paxos__RequestSession "px" "conn");;
      Continue);;
    #().

Definition Paxos__ConnectAll: val :=
  rec: "Paxos__ConnectAll" "px" :=
    ForSlice uint64T <> "nid" (struct.loadF Paxos "peers" "px")
      (Paxos__Connect "px" "nid");;
    #().
