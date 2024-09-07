(* autogenerated from github.com/mit-pdos/gokv/aof *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition AppendOnlyFile := struct.decl [
  "mu" :: ptrT;
  "oldDurableCond" :: ptrT;
  "durableCond" :: ptrT;
  "lengthCond" :: ptrT;
  "membuf" :: slice.T byteT;
  "length" :: uint64T;
  "durableLength" :: uint64T;
  "closeRequested" :: boolT;
  "closed" :: boolT;
  "closedCond" :: ptrT
].

Definition CreateAppendOnlyFile: val :=
  rec: "CreateAppendOnlyFile" "fname" :=
    let: "a" := struct.alloc AppendOnlyFile (zero_val (struct.t AppendOnlyFile)) in
    struct.storeF AppendOnlyFile "mu" "a" (newMutex #());;
    struct.storeF AppendOnlyFile "lengthCond" "a" (NewCond (struct.loadF AppendOnlyFile "mu" "a"));;
    struct.storeF AppendOnlyFile "oldDurableCond" "a" (NewCond (struct.loadF AppendOnlyFile "mu" "a"));;
    struct.storeF AppendOnlyFile "durableCond" "a" (NewCond (struct.loadF AppendOnlyFile "mu" "a"));;
    struct.storeF AppendOnlyFile "closedCond" "a" (NewCond (struct.loadF AppendOnlyFile "mu" "a"));;
    Fork (Mutex__Lock (struct.loadF AppendOnlyFile "mu" "a");;
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            (if: ((slice.len (struct.loadF AppendOnlyFile "membuf" "a")) = #0) && (~ (struct.loadF AppendOnlyFile "closeRequested" "a"))
            then
              Cond__Wait (struct.loadF AppendOnlyFile "lengthCond" "a");;
              Continue
            else
              (if: struct.loadF AppendOnlyFile "closeRequested" "a"
              then
                grove_ffi.FileAppend "fname" (struct.loadF AppendOnlyFile "membuf" "a");;
                struct.storeF AppendOnlyFile "membuf" "a" (NewSlice byteT #0);;
                struct.storeF AppendOnlyFile "durableLength" "a" (struct.loadF AppendOnlyFile "length" "a");;
                Cond__Broadcast (struct.loadF AppendOnlyFile "durableCond" "a");;
                struct.storeF AppendOnlyFile "closed" "a" #true;;
                Cond__Broadcast (struct.loadF AppendOnlyFile "closedCond" "a");;
                Mutex__Unlock (struct.loadF AppendOnlyFile "mu" "a");;
                Break
              else
                let: "l" := struct.loadF AppendOnlyFile "membuf" "a" in
                let: "newLength" := struct.loadF AppendOnlyFile "length" "a" in
                struct.storeF AppendOnlyFile "membuf" "a" (NewSlice byteT #0);;
                let: "cond" := struct.loadF AppendOnlyFile "durableCond" "a" in
                struct.storeF AppendOnlyFile "durableCond" "a" (struct.loadF AppendOnlyFile "oldDurableCond" "a");;
                struct.storeF AppendOnlyFile "oldDurableCond" "a" "cond";;
                Mutex__Unlock (struct.loadF AppendOnlyFile "mu" "a");;
                grove_ffi.FileAppend "fname" "l";;
                Mutex__Lock (struct.loadF AppendOnlyFile "mu" "a");;
                struct.storeF AppendOnlyFile "durableLength" "a" "newLength";;
                Cond__Broadcast "cond";;
                Continue))));;
    "a".

(* NOTE: cannot be called concurrently with Append() *)
Definition AppendOnlyFile__Close: val :=
  rec: "AppendOnlyFile__Close" "a" :=
    Mutex__Lock (struct.loadF AppendOnlyFile "mu" "a");;
    struct.storeF AppendOnlyFile "closeRequested" "a" #true;;
    Cond__Signal (struct.loadF AppendOnlyFile "lengthCond" "a");;
    Skip;;
    (for: (λ: <>, (~ (struct.loadF AppendOnlyFile "closed" "a"))); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF AppendOnlyFile "closedCond" "a");;
      Continue);;
    Mutex__Unlock (struct.loadF AppendOnlyFile "mu" "a");;
    #().

(* NOTE: cannot be called concurrently with Close() *)
Definition AppendOnlyFile__Append: val :=
  rec: "AppendOnlyFile__Append" "a" "data" :=
    Mutex__Lock (struct.loadF AppendOnlyFile "mu" "a");;
    struct.storeF AppendOnlyFile "membuf" "a" (marshal.WriteBytes (struct.loadF AppendOnlyFile "membuf" "a") "data");;
    struct.storeF AppendOnlyFile "length" "a" (std.SumAssumeNoOverflow (struct.loadF AppendOnlyFile "length" "a") (slice.len "data"));;
    let: "r" := struct.loadF AppendOnlyFile "length" "a" in
    Cond__Signal (struct.loadF AppendOnlyFile "lengthCond" "a");;
    Mutex__Unlock (struct.loadF AppendOnlyFile "mu" "a");;
    "r".

Definition AppendOnlyFile__WaitAppend: val :=
  rec: "AppendOnlyFile__WaitAppend" "a" "length" :=
    Mutex__Lock (struct.loadF AppendOnlyFile "mu" "a");;
    let: "cond" := ref (zero_val ptrT) in
    (if: ("length" + (slice.len (struct.loadF AppendOnlyFile "membuf" "a"))) ≤ (struct.loadF AppendOnlyFile "length" "a")
    then "cond" <-[ptrT] (struct.loadF AppendOnlyFile "oldDurableCond" "a")
    else "cond" <-[ptrT] (struct.loadF AppendOnlyFile "durableCond" "a"));;
    Skip;;
    (for: (λ: <>, (struct.loadF AppendOnlyFile "durableLength" "a") < "length"); (λ: <>, Skip) := λ: <>,
      Cond__Wait (![ptrT] "cond");;
      Continue);;
    Mutex__Unlock (struct.loadF AppendOnlyFile "mu" "a");;
    #().
