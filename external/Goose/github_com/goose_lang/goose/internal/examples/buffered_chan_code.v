From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

(* Buffered channels. These are essentially the same thing as a queue with 
Send being push and Receive being pop *)
Definition Buffered_Chan := struct.decl [
  "queue" :: slice.T uint64T;
  "cond" :: ptrT;
  "lock" :: ptrT;
  "first" :: uint64T;
  "count" :: uint64T;
  "closed" :: boolT
].

Definition NewBuffered_Chan: val :=
  rec: "NewBuffered_Chan" "queue_size" :=
    let: "lock" := newMutex #() in
    struct.new Buffered_Chan [
      "queue" ::= NewSliceWithCap uint64T "queue_size" "queue_size";
      "cond" ::= NewCond "lock";
      "lock" ::= "lock";
      "first" ::= #0;
      "count" ::= #0;
      "closed" ::= #false
    ]
    .

Definition Buffered_Chan__Send: val :=
  rec: "Buffered_Chan__Send" "q" "a" :=
    Mutex__Lock (struct.loadF Buffered_Chan "lock" "q");;
    if: (struct.loadF Buffered_Chan "closed" "q") 
    then Panic "Send on closed channel!"
    else
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Buffered_Chan "queue" "q")) in
    Skip;;
    (for: (λ: <>, (struct.loadF Buffered_Chan "count" "q") ≥ (![uint64T] "queue_size")); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF Buffered_Chan "cond" "q");;
      if: (struct.loadF Buffered_Chan "closed" "q") 
        then Panic "Send on closed channel!"
      else
      Continue);;
    let: "last" := ref_to uint64T (((struct.loadF Buffered_Chan "first" "q") + (struct.loadF Buffered_Chan "count" "q")) `rem` (![uint64T] "queue_size")) in
    SliceSet uint64T (struct.loadF Buffered_Chan "queue" "q") (![uint64T] "last") "a";;
    struct.storeF Buffered_Chan "count" "q" ((struct.loadF Buffered_Chan "count" "q") + #1);;
    Mutex__Unlock (struct.loadF Buffered_Chan "lock" "q");;
    Cond__Broadcast (struct.loadF Buffered_Chan "cond" "q");;
    #().

Definition Buffered_Chan__Receive: val :=
  rec: "Buffered_Chan__Receive" "q" :=
    Mutex__Lock (struct.loadF Buffered_Chan "lock" "q");;
    if: (struct.loadF Buffered_Chan "closed" "q") 
    then (#null, #false)
    else
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Buffered_Chan "queue" "q")) in
    Skip;;
    (for: (λ: <>, (struct.loadF Buffered_Chan "count" "q") = #0); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF Buffered_Chan "cond" "q");;
      Continue);;
    let: "res" := SliceGet uint64T (struct.loadF Buffered_Chan "queue" "q") (struct.loadF Buffered_Chan "first" "q") in
    struct.storeF Buffered_Chan "first" "q" (((struct.loadF Buffered_Chan "first" "q") + #1) `rem` (![uint64T] "queue_size"));;
    struct.storeF Buffered_Chan "count" "q" ((struct.loadF Buffered_Chan "count" "q") - #1);;
    Mutex__Unlock (struct.loadF Buffered_Chan "lock" "q");;
    Cond__Broadcast (struct.loadF Buffered_Chan "cond" "q");;
    ("res", #true).


Definition Buffered_Chan__Close: val :=
  rec: "Buffered_Chan__Close" "q" :=
    Mutex__Lock (struct.loadF Buffered_Chan "lock" "q");;
    struct.storeF Buffered_Chan "closed" "q" #true;;
    Cond__Broadcast (struct.loadF Buffered_Chan "cond" "q");;
    Mutex__Unlock (struct.loadF Buffered_Chan "lock" "q");;
    #().

End code.