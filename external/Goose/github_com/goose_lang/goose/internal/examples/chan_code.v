From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

(* Unbuffered channels *)
Definition ChanHandle := struct.decl [
  "mu" :: ptrT;
  "receiver_done" :: boolT;
  "value" :: uint64T;
  "sender_ready" :: boolT;
  "receiver_cond" :: ptrT;
  "sender_cond" :: ptrT
].

Definition newChanHandle: val :=
  rec: "newChanHandle" <> :=
    let: "mu" := newMutex #() in
    let: "receiver_cond" := NewCond "mu" in
    let: "sender_cond" := NewCond "mu" in
    struct.new ChanHandle [
      "mu" ::= "mu";
      "receiver_done" ::= #false;
      "sender_ready" ::= #false;
      "receiver_cond" ::= "receiver_cond";
      "sender_cond" ::= "sender_cond";
      "value" ::= #0
    ].

(* Let the receiver Goroutine know that we are going to send something. *)
Definition ChanHandle__RegisterSender : val :=
  rec: "ChanHandle__RegisterSender" "h" "v" :=
   let: "v_ptr" := ref_to uint64T "v" in 
   let: "v_int" := ![uint64T] "v_ptr" in 
    Mutex__Lock (struct.loadF ChanHandle "mu" "h");;
   struct.storeF ChanHandle "sender_ready" "h" #true;;

   struct.storeF ChanHandle "value" "h" "v_int";;
    Cond__Signal (struct.loadF ChanHandle "receiver_cond" "h");;
    Mutex__Unlock (struct.loadF ChanHandle "mu" "h");;
    #().

Definition ChanHandle__Send: val :=
  rec: "ChanHandle__Send" "h" "v" :=
  ChanHandle__RegisterSender "h" "v";;
    Mutex__Lock (struct.loadF ChanHandle "mu" "h");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ((struct.loadF ChanHandle "receiver_done" "h") &&
      ((struct.loadF ChanHandle "sender_ready" "h") = #false))
      then
        (* Reset the receiver_done bool so we can restart the sequence *)
        struct.storeF ChanHandle "receiver_done" "h" #false;;
        Break
      else
        Cond__Wait (struct.loadF ChanHandle "sender_cond" "h");;
        Continue));;
    Mutex__Unlock (struct.loadF ChanHandle "mu" "h");;
    #().

(* This is very similar to send *)
Definition ChanHandle__Receive: val :=
  rec: "ChanHandle__Receive" "h" :=
    Mutex__Lock (struct.loadF ChanHandle "mu" "h");;
    Skip;;
    let: "ret_val_ptr" := 
    ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: 
      ((struct.loadF ChanHandle "sender_ready" "h") &&
      ((struct.loadF ChanHandle "receiver_done" "h") = #false))
      then
        struct.storeF ChanHandle "receiver_done" "h" #true;;
        Cond__Signal (struct.loadF ChanHandle "sender_cond" "h");;
        "ret_val_ptr" <-[uint64T] (struct.loadF ChanHandle "value" "h");;
        Break
      else
        Cond__Wait (struct.loadF ChanHandle "receiver_cond" "h");;
        Continue));;
    Mutex__Unlock (struct.loadF ChanHandle "mu" "h");;
    ![uint64T] "ret_val_ptr".

(* Unit tests that use synchronization with unbuffered channels. *)
Definition SendChanTest: val :=
  rec: "SendChanTest" <> :=
    let: "i" := ref_to uint64T #5 in
    let: "ch" := newChanHandle #() in
    
      Fork (
            "i" <-[uint64T] ((![uint64T] "i") + #7);;
            ChanHandle__Send "ch" (![uint64T] "i") ;;            
            #());;
      ChanHandle__Receive "ch";;
    #().
Definition RecChanTest: val :=
  rec: "RecChanTest" <> :=
    let: "i" := ref_to uint64T #5 in
    let: "ch" := newChanHandle #() in
    
      Fork (
            "i" <-[uint64T] ((![uint64T] "i") + #7);;
            ChanHandle__Receive "ch" ;;            
            #());;
    let: "rval" := ref_to uint64T #0 in
      ChanHandle__Send "ch" (![uint64T] "rval");;
    #().

Definition RecChanTestFail: val :=
  rec: "RecChanTest" <> :=
    let: "i" := ref_to uint64T #5 in
    let: "ch" := newChanHandle #() in
    
      Fork (
            ChanHandle__Receive "ch" ;;            
            "i" <-[uint64T] ((![uint64T] "i") + #7);;
            #());;
    let: "rval" := ref_to uint64T #0 in
      ChanHandle__Send "ch" (![uint64T] "rval");;
    #().


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

    Definition ReusableChanHandle := struct.decl [
  "mu" :: ptrT;
  "receiver_waiting" :: boolT;
  "value" :: uint64T;
  "sender_waiting" :: boolT;
  "receiver_cond" :: ptrT;
  "sender_cond" :: ptrT
].

Definition newReusableChanHandle: val :=
  rec: "newReusableChanHandle" "buffer_size" :=
    let: "mu" := newMutex #() in
    let: "receiver_cond" := NewCond "mu" in
    let: "sender_cond" := NewCond "mu" in
    struct.new ReusableChanHandle [
      "mu" ::= "mu";
      "receiver_waiting" ::= #false;
      "sender_waiting" ::= #false;
      "receiver_cond" ::= "receiver_cond";
      "sender_cond" ::= "sender_cond";
      "value" ::= #0
    ].

Definition ReusableChanHandle__Send: val :=
  rec: "ReusableChanHandle__Send" "h" "v" :=
   let: "v_ptr" := ref_to uint64T "v" in 
   let: "v_int" := ![uint64T] "v_ptr" in 
    Mutex__Lock (struct.loadF ReusableChanHandle "mu" "h");;
    struct.storeF ReusableChanHandle "sender_waiting" "h" #true;;
    Cond__Signal (struct.loadF ReusableChanHandle "receiver_cond" "h");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ((struct.loadF ReusableChanHandle "receiver_waiting" "h")
      && ((struct.loadF ReusableChanHandle "sender_waiting" "h") = #false))
      then
        struct.storeF ReusableChanHandle "receiver_waiting" "h" #false;;
        struct.storeF ReusableChanHandle "value" "h" "v_int";;
        Cond__Signal (struct.loadF ReusableChanHandle "receiver_cond" "h");;
        Break
      else
        Continue
      ));;
        struct.storeF ReusableChanHandle "receiver_waiting" "h" #false;;
      Mutex__Unlock (struct.loadF ReusableChanHandle "mu" "h");;
    #(). 


Definition ReusableChanHandle__Receive: val :=
  rec: "ReusableChanHandle__Receive" "h" :=
    Mutex__Lock (struct.loadF ReusableChanHandle "mu" "h");;
    struct.storeF ReusableChanHandle "receiver_waiting" "h" #true;;
    Cond__Signal (struct.loadF ReusableChanHandle "sender_cond" "h");;
    let: "ret_val_ptr" := 
    ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: 
      (struct.loadF ReusableChanHandle "sender_waiting" "h")
      then
        struct.storeF ReusableChanHandle "sender_waiting" "h" #false;;
        Cond__Signal (struct.loadF ReusableChanHandle "sender_cond" "h");;
        "ret_val_ptr" <-[uint64T] (struct.loadF ReusableChanHandle "value" "h");;
        Break
      else
        Continue));;
    Mutex__Unlock (struct.loadF ReusableChanHandle "mu" "h");;
    ![uint64T] "ret_val_ptr".

Definition SendReusableChanTest: val :=
  rec: "SendReusableChanTest" <> :=
    let: "i" := ref_to uint64T #5 in
    let: "ch" := newReusableChanHandle #() in
    
      Fork (
            "i" <-[uint64T] ((![uint64T] "i") + #7);;
            ReusableChanHandle__Send "ch" (![uint64T] "i") ;;            

            let: "z" := ref_to uint64T #20 in
            ReusableChanHandle__Send "ch" (![uint64T] "z") ;;            
            #());;
      ReusableChanHandle__Receive "ch";;
      ReusableChanHandle__Receive "ch";;
    #().

End code.