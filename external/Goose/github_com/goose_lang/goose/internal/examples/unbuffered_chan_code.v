From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition UnbufferedChannel := struct.decl [
 "mu" :: ptrT;
 "v" :: uint64T;
 "receiver_ready" :: boolT;
 "sender_ready" :: boolT;
 "receiver_done" :: boolT;
 "sender_done" :: boolT;
 "closed" :: boolT
].


Definition NewUnbufferedChannel: val :=
 rec: "NewUnbufferedChannel" <> :=
   struct.new UnbufferedChannel [
     "mu" ::= newMutex #()
   ].

Definition UnbufferedChannel__Send: val :=
 rec: "UnbufferedChannel__Send" "c" "val" :=
   let: "return_early" := ref_to boolT #false in
   Skip;;
   (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
     Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
     (if: struct.loadF UnbufferedChannel "receiver_ready" "c"
     then
       struct.storeF UnbufferedChannel "receiver_ready" "c" #false;;
       struct.storeF UnbufferedChannel "sender_done" "c" #true;;
       struct.storeF UnbufferedChannel "v" "c" "val";;
       Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
       "return_early" <-[boolT] #true;;
       Break
     else
       (if: struct.loadF UnbufferedChannel "closed" "c"
       then Panic "send on closed channel"
       else #());;
       (if: (((~ (struct.loadF UnbufferedChannel "receiver_ready" "c")) && (~ (struct.loadF UnbufferedChannel "sender_ready" "c"))) && (~ (struct.loadF UnbufferedChannel "receiver_done" "c"))) && (~ (struct.loadF UnbufferedChannel "sender_done" "c"))
       then
         struct.storeF UnbufferedChannel "sender_ready" "c" #true;;
         struct.storeF UnbufferedChannel "v" "c" "val";;
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Break
       else
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Continue)));;
   (if: ![boolT] "return_early"
   then
     Skip;;
     (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
       Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
       (if: (~ (struct.loadF UnbufferedChannel "sender_done" "c"))
       then
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Break
       else
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Continue));;
     #()
   else
     Skip;;
     (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
       Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
       (if: struct.loadF UnbufferedChannel "receiver_done" "c"
       then
         struct.storeF UnbufferedChannel "receiver_done" "c" #false;;
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Break
       else
         (if: struct.loadF UnbufferedChannel "closed" "c"
         then Panic "send on closed channel"
         else #());;
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Continue));;
     #()).


Definition UnbufferedChannel__Receive: val :=
 rec: "UnbufferedChannel__Receive" "c" :=
   let: "return_early" := ref_to boolT #false in
   let: "closed" := ref_to boolT #false in
   let: "ret_val" := ref_to uint64T #0 in
   Skip;;
   (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
     Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
     (if: struct.loadF UnbufferedChannel "closed" "c"
     then
       Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
       "closed" <-[boolT] #true;;
       Break
     else
       (if: struct.loadF UnbufferedChannel "sender_ready" "c"
       then
         struct.storeF UnbufferedChannel "sender_ready" "c" #false;;
         struct.storeF UnbufferedChannel "receiver_done" "c" #true;;
         "ret_val" <-[uint64T] (struct.loadF UnbufferedChannel "v" "c");;
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         "return_early" <-[boolT] #true;;
         Break
       else
         (if: (((~ (struct.loadF UnbufferedChannel "receiver_ready" "c")) && (~ (struct.loadF UnbufferedChannel "sender_ready" "c"))) && (~ (struct.loadF UnbufferedChannel "receiver_done" "c"))) && (~ (struct.loadF UnbufferedChannel "sender_done" "c"))
         then
           struct.storeF UnbufferedChannel "receiver_ready" "c" #true;;
           Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
           Break
         else
           Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
           Continue))));;
   (if: ![boolT] "closed"
   then (#0, #true)
   else
     (if: ![boolT] "return_early"
     then
       Skip;;
       (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
         Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
         (if: (~ (struct.loadF UnbufferedChannel "receiver_done" "c"))
         then
           Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
           Break
         else
           Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
           Continue));;
       (![uint64T] "ret_val", #false)
     else
       Skip;;
       (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
         Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
         (if: struct.loadF UnbufferedChannel "closed" "c"
         then
           Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
           "closed" <-[boolT] #true;;
           Break
         else
           (if: struct.loadF UnbufferedChannel "sender_done" "c"
           then
             struct.storeF UnbufferedChannel "sender_done" "c" #false;;
             "ret_val" <-[uint64T] (struct.loadF UnbufferedChannel "v" "c");;
             Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
             Break
           else
             Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
             Continue)));;
       (![uint64T] "ret_val", ![boolT] "closed"))).
   
Definition UnbufferedChannel__TryReceive: val :=
 rec: "UnbufferedChannel__TryReceive" "c" :=
   let: "ret_val" := ref_to uint64T #0 in
   let: "return_bool" := ref_to boolT #false in
   Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
   (if: struct.loadF UnbufferedChannel "closed" "c"
   then "ret_val" <-[uint64T] #0
   else
     (if: struct.loadF UnbufferedChannel "sender_ready" "c"
     then
       struct.storeF UnbufferedChannel "sender_ready" "c" #false;;
       struct.storeF UnbufferedChannel "receiver_done" "c" #true;;
       "ret_val" <-[uint64T] (struct.loadF UnbufferedChannel "v" "c");;
       "return_bool" <-[boolT] #true
     else #()));;
   Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
   (if: ![boolT] "return_bool"
   then
     Skip;;
     (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
       Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
       (if: (~ (struct.loadF UnbufferedChannel "receiver_done" "c"))
       then
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Break
       else
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Continue))
   else #());;
   (![uint64T] "ret_val", ![boolT] "return_bool").


Definition UnbufferedChannel__TrySend: val :=
 rec: "UnbufferedChannel__TrySend" "c" "val" :=
   let: "return_bool" := ref_to boolT #false in
   Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
   (if: struct.loadF UnbufferedChannel "closed" "c"
   then Panic "Send on closed channel."
   else #());;
   (if: struct.loadF UnbufferedChannel "receiver_ready" "c"
   then
     struct.storeF UnbufferedChannel "receiver_ready" "c" #false;;
     struct.storeF UnbufferedChannel "sender_done" "c" #true;;
     struct.storeF UnbufferedChannel "v" "c" "val";;
     "return_bool" <-[boolT] #true
   else #());;
   Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
   (if: ![boolT] "return_bool"
   then
     Skip;;
     (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
       Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
       (if: (~ (struct.loadF UnbufferedChannel "sender_done" "c"))
       then
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Break
       else
         Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
         Continue))
   else #());;
   ![boolT] "return_bool".


Definition UnbufferedChannel__Close: val :=
 rec: "UnbufferedChannel__Close" "c" :=
   Mutex__Lock (struct.loadF UnbufferedChannel "mu" "c");;
   (if: struct.loadF UnbufferedChannel "closed" "c"
   then Panic "send on closed channel"
   else #());;
   struct.storeF UnbufferedChannel "receiver_ready" "c" #false;;
   struct.storeF UnbufferedChannel "sender_ready" "c" #false;;
   struct.storeF UnbufferedChannel "closed" "c" #true;;
   Mutex__Unlock (struct.loadF UnbufferedChannel "mu" "c");;
   #().

End code.