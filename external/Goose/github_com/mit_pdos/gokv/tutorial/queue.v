(* autogenerated from github.com/mit-pdos/gokv/tutorial/queue *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition Queue := struct.decl [
  "queue" :: slice.T uint64T;
  "cond" :: ptrT;
  "lock" :: ptrT;
  "first" :: uint64T;
  "count" :: uint64T
].

Definition NewQueue: val :=
  rec: "NewQueue" "queue_size" :=
    let: "lock" := newMutex #() in
    struct.mk Queue [
      "queue" ::= NewSliceWithCap uint64T "queue_size" "queue_size";
      "cond" ::= NewCond "lock";
      "lock" ::= "lock";
      "first" ::= #0;
      "count" ::= #0
    ].

Definition Queue__Enqueue: val :=
  rec: "Queue__Enqueue" "q" "a" :=
    Mutex__Lock (struct.loadF Queue "lock" "q");;
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Queue "queue" "q")) in
    Skip;;
    (for: (λ: <>, (struct.loadF Queue "count" "q") ≥ (![uint64T] "queue_size")); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF Queue "cond" "q");;
      Continue);;
    let: "last" := ref_to uint64T (((struct.loadF Queue "first" "q") + (struct.loadF Queue "count" "q")) `rem` (![uint64T] "queue_size")) in
    SliceSet uint64T (struct.loadF Queue "queue" "q") (![uint64T] "last") "a";;
    struct.storeF Queue "count" "q" ((struct.loadF Queue "count" "q") + #1);;
    Mutex__Unlock (struct.loadF Queue "lock" "q");;
    Cond__Broadcast (struct.loadF Queue "cond" "q");;
    #().

Definition Queue__Dequeue: val :=
  rec: "Queue__Dequeue" "q" :=
    Mutex__Lock (struct.loadF Queue "lock" "q");;
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Queue "queue" "q")) in
    Skip;;
    (for: (λ: <>, (struct.loadF Queue "count" "q") = #0); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF Queue "cond" "q");;
      Continue);;
    let: "res" := SliceGet uint64T (struct.loadF Queue "queue" "q") (struct.loadF Queue "first" "q") in
    struct.storeF Queue "first" "q" (((struct.loadF Queue "first" "q") + #1) `rem` (![uint64T] "queue_size"));;
    struct.storeF Queue "count" "q" ((struct.loadF Queue "count" "q") - #1);;
    Mutex__Unlock (struct.loadF Queue "lock" "q");;
    Cond__Broadcast (struct.loadF Queue "cond" "q");;
    "res".

Definition Queue__Peek: val :=
  rec: "Queue__Peek" "q" :=
    Mutex__Lock (struct.loadF Queue "lock" "q");;
    (if: (struct.loadF Queue "count" "q") > #0
    then
      let: "first" := SliceGet uint64T (struct.loadF Queue "queue" "q") (struct.loadF Queue "first" "q") in
      Mutex__Unlock (struct.loadF Queue "lock" "q");;
      ("first", #true)
    else
      Mutex__Unlock (struct.loadF Queue "lock" "q");;
      (#0, #false)).

End code.
