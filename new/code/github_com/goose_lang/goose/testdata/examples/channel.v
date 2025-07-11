(* autogenerated from github.com/goose-lang/goose/testdata/examples/channel *)
From New.golang Require Import defn.
Require Export New.code.github_com.goose_lang.goose.model.channel.

Definition chan_spec_raw_examples : go_string := "github.com/goose-lang/goose/testdata/examples/channel".

Module chan_spec_raw_examples.
Section code.
Context `{ffi_syntax}.


(* Example 1: Simple goroutine sending a string, check basic message passing without
   synchronization

   go: examples.go:10:6 *)
Definition SendMessage : val :=
  rec: "SendMessage" <> :=
    exception_do (let: "messageChan" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #stringT) "$a0") in
    do:  ("messageChan" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (do:  (let: "$a0" := #"hello world"%go in
      (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "messageChan") #stringT) "$a0");;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    let: "message" := (mem.alloc (type.zero_val #stringT)) in
    let: "$r0" := ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "messageChan") #stringT) #()) in
    do:  ("message" <-[#stringT] "$r0");;;
    (if: (![#stringT] "message") ≠ #"hello world"%go
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Did not receive expected message"%go) in
      Panic "$a0")
    else do:  #());;;
    return: #()).

(* Example 2: Join goroutine with receive on unbuffered channel

   go: examples.go:29:6 *)
Definition JoinWithReceive : val :=
  rec: "JoinWithReceive" <> :=
    exception_do (let: "message" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #stringT)) in
    do:  ("message" <-[#ptrT] "$r0");;;
    let: "done" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (let: "$r0" := #"hello world"%go in
      do:  ((![#ptrT] "message") <-[#stringT] "$r0");;;
      do:  (let: "$a0" := #(W64 0) in
      (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "done") #uint64T) "$a0");;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "done") #uint64T) #());;;
    (if: (![#stringT] (![#ptrT] "message")) ≠ #"hello world"%go
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Message was not set correctly"%go) in
      Panic "$a0")
    else do:  #());;;
    return: #()).

(* Example 3: Join goroutine with send on unbuffered channel

   go: examples.go:55:6 *)
Definition JoinWithSend : val :=
  rec: "JoinWithSend" <> :=
    exception_do (let: "message" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #stringT)) in
    do:  ("message" <-[#ptrT] "$r0");;;
    let: "done" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (let: "$r0" := #"hello world"%go in
      do:  ((![#ptrT] "message") <-[#stringT] "$r0");;;
      do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "done") #uint64T) #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    do:  (let: "$a0" := #(W64 0) in
    (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "done") #uint64T) "$a0");;;
    (if: (![#stringT] (![#ptrT] "message")) ≠ #"hello world"%go
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Message was not set correctly"%go) in
      Panic "$a0")
    else do:  #());;;
    return: #()).

(* Example 4: Broadcast notification with close. This is testing a case where
   we transfer disjoint ownership to different threads in a single broadcast

   go: examples.go:82:6 *)
Definition BroadcastNotification : val :=
  rec: "BroadcastNotification" <> :=
    exception_do (let: "notifyCh" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("notifyCh" <-[#ptrT] "$r0");;;
    let: "done1" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done1" <-[#ptrT] "$r0");;;
    let: "done2" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done2" <-[#ptrT] "$r0");;;
    let: "done3" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done3" <-[#ptrT] "$r0");;;
    let: "results" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "results") in
    let: "$a1" := ((let: "$sl0" := #""%go in
    slice.literal #stringT ["$sl0"])) in
    (slice.append #stringT) "$a0" "$a1") in
    do:  ("results" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "results") in
    let: "$a1" := ((let: "$sl0" := #""%go in
    slice.literal #stringT ["$sl0"])) in
    (slice.append #stringT) "$a0" "$a1") in
    do:  ("results" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "results") in
    let: "$a1" := ((let: "$sl0" := #""%go in
    slice.literal #stringT ["$sl0"])) in
    (slice.append #stringT) "$a0" "$a1") in
    do:  ("results" <-[#sliceT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (let: "ok" := (mem.alloc (type.zero_val #boolT)) in
      let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "notifyCh") #uint64T) #()) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  "$r0";;;
      do:  ("ok" <-[#boolT] "$r1");;;
      (if: (~ (![#boolT] "ok"))
      then
        (if: (![#stringT] (slice.elem_ref #stringT (![#sliceT] "results") #(W64 0))) ≠ #"thread1"%go
        then
          do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Thread 1 received incorrect value"%go) in
          Panic "$a0")
        else do:  #());;;
        do:  (let: "$a0" := #(W64 0) in
        (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "done1") #uint64T) "$a0")
      else do:  #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    let: "$go" := (λ: <>,
      exception_do (let: "ok" := (mem.alloc (type.zero_val #boolT)) in
      let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "notifyCh") #uint64T) #()) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  "$r0";;;
      do:  ("ok" <-[#boolT] "$r1");;;
      (if: (~ (![#boolT] "ok"))
      then
        (if: (![#stringT] (slice.elem_ref #stringT (![#sliceT] "results") #(W64 1))) ≠ #"thread2"%go
        then
          do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Thread 2 received incorrect value"%go) in
          Panic "$a0")
        else do:  #());;;
        do:  (let: "$a0" := #(W64 0) in
        (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "done2") #uint64T) "$a0")
      else do:  #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    let: "$go" := (λ: <>,
      exception_do (let: "ok" := (mem.alloc (type.zero_val #boolT)) in
      let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "notifyCh") #uint64T) #()) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  "$r0";;;
      do:  ("ok" <-[#boolT] "$r1");;;
      (if: (~ (![#boolT] "ok"))
      then
        (if: (![#stringT] (slice.elem_ref #stringT (![#sliceT] "results") #(W64 2))) ≠ #"thread3"%go
        then
          do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Thread 3 received incorrect value"%go) in
          Panic "$a0")
        else do:  #());;;
        do:  (let: "$a0" := #(W64 0) in
        (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "done3") #uint64T) "$a0")
      else do:  #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    let: "$r0" := #"thread1"%go in
    do:  ((slice.elem_ref #stringT (![#sliceT] "results") #(W64 0)) <-[#stringT] "$r0");;;
    let: "$r0" := #"thread2"%go in
    do:  ((slice.elem_ref #stringT (![#sliceT] "results") #(W64 1)) <-[#stringT] "$r0");;;
    let: "$r0" := #"thread3"%go in
    do:  ((slice.elem_ref #stringT (![#sliceT] "results") #(W64 2)) <-[#stringT] "$r0");;;
    do:  ((method_call #channel #"Channel'ptr" #"Close" (![#ptrT] "notifyCh") #uint64T) #());;;
    do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "done1") #uint64T) #());;;
    do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "done2") #uint64T) #());;;
    do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "done3") #uint64T) #());;;
    return: #()).

(* Example 5: Join sending goroutine before closing a buffered channel.
   This should demonstrate the spec's ability to prevent closing on a channel
   without joining all the senders.

   go: examples.go:149:6 *)
Definition CoordinatedChannelClose : val :=
  rec: "CoordinatedChannelClose" <> :=
    exception_do (let: "bufCh" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 2) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("bufCh" <-[#ptrT] "$r0");;;
    let: "syncCh" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("syncCh" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (do:  (let: "$a0" := #(W64 42) in
      (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "bufCh") #uint64T) "$a0");;;
      do:  (let: "$a0" := #(W64 0) in
      (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "syncCh") #uint64T) "$a0");;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    do:  (let: "$a0" := #(W64 84) in
    (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "bufCh") #uint64T) "$a0");;;
    do:  ((method_call #channel #"Channel'ptr" #"ReceiveDiscardOk" (![#ptrT] "syncCh") #uint64T) #());;;
    do:  ((method_call #channel #"Channel'ptr" #"Close" (![#ptrT] "bufCh") #uint64T) #());;;
    let: "ok1" := (mem.alloc (type.zero_val #boolT)) in
    let: "val1" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "bufCh") #uint64T) #()) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("val1" <-[#uint64T] "$r0");;;
    do:  ("ok1" <-[#boolT] "$r1");;;
    let: "ok2" := (mem.alloc (type.zero_val #boolT)) in
    let: "val2" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "bufCh") #uint64T) #()) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("val2" <-[#uint64T] "$r0");;;
    do:  ("ok2" <-[#boolT] "$r1");;;
    (if: (~ (![#boolT] "ok1")) || (~ (![#boolT] "ok2"))
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Channel shouldn't be empty yet"%go) in
      Panic "$a0")
    else do:  #());;;
    (if: (~ ((((![#uint64T] "val1") = #(W64 42)) && ((![#uint64T] "val2") = #(W64 84))) || (((![#uint64T] "val1") = #(W64 84)) && ((![#uint64T] "val2") = #(W64 42)))))
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Did not receive both expected values"%go) in
      Panic "$a0")
    else do:  #());;;
    return: #()).

(* Example 6: A basic pipeline that just passes pointers
   to a single worker who doubles the value of what they
   point to.

   go: examples.go:189:6 *)
Definition DoubleValues : val :=
  rec: "DoubleValues" <> :=
    exception_do (let: "val1" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 5) in
    do:  ("val1" <-[#uint64T] "$r0");;;
    let: "val2" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 10) in
    do:  ("val2" <-[#uint64T] "$r0");;;
    let: "val3" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 15) in
    do:  ("val3" <-[#uint64T] "$r0");;;
    let: "values" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "values") in
    let: "$a1" := ((let: "$sl0" := "val1" in
    slice.literal #ptrT ["$sl0"])) in
    (slice.append #ptrT) "$a0" "$a1") in
    do:  ("values" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "values") in
    let: "$a1" := ((let: "$sl0" := "val2" in
    slice.literal #ptrT ["$sl0"])) in
    (slice.append #ptrT) "$a0" "$a1") in
    do:  ("values" <-[#sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "values") in
    let: "$a1" := ((let: "$sl0" := "val3" in
    slice.literal #ptrT ["$sl0"])) in
    (slice.append #ptrT) "$a0" "$a1") in
    do:  ("values" <-[#sliceT] "$r0");;;
    let: "ch" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #ptrT) "$a0") in
    do:  ("ch" <-[#ptrT] "$r0");;;
    let: "done" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #channel.channel #"NewChannelRef"%go #uint64T) "$a0") in
    do:  ("done" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do ((for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        let: "ok" := (mem.alloc (type.zero_val #boolT)) in
        let: "ptr" := (mem.alloc (type.zero_val #ptrT)) in
        let: ("$ret0", "$ret1") := ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "ch") #ptrT) #()) in
        let: "$r0" := "$ret0" in
        let: "$r1" := "$ret1" in
        do:  ("ptr" <-[#ptrT] "$r0");;;
        do:  ("ok" <-[#boolT] "$r1");;;
        (if: (~ (![#boolT] "ok"))
        then break: #()
        else do:  #());;;
        let: "$r0" := ((![#uint64T] (![#ptrT] "ptr")) * #(W64 2)) in
        do:  ((![#ptrT] "ptr") <-[#uint64T] "$r0"));;;
      do:  ((method_call #channel #"Channel'ptr" #"Close" (![#ptrT] "done") #uint64T) #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    do:  (let: "$a0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] "values") #(W64 0))) in
    (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "ch") #ptrT) "$a0");;;
    do:  (let: "$a0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] "values") #(W64 1))) in
    (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "ch") #ptrT) "$a0");;;
    do:  (let: "$a0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] "values") #(W64 2))) in
    (method_call #channel #"Channel'ptr" #"Send" (![#ptrT] "ch") #ptrT) "$a0");;;
    do:  ((method_call #channel #"Channel'ptr" #"Close" (![#ptrT] "ch") #ptrT) #());;;
    do:  ((method_call #channel #"Channel'ptr" #"Receive" (![#ptrT] "done") #uint64T) #());;;
    (if: (~ ((((![#uint64T] "val1") = #(W64 10)) && ((![#uint64T] "val2") = #(W64 20))) && ((![#uint64T] "val3") = #(W64 30))))
    then
      do:  (let: "$a0" := (interface.make (#""%go, #"string"%go) #"Values were not doubled correctly"%go) in
      Panic "$a0")
    else do:  #());;;
    return: #()).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("SendMessage"%go, SendMessage); ("JoinWithReceive"%go, JoinWithReceive); ("JoinWithSend"%go, JoinWithSend); ("BroadcastNotification"%go, BroadcastNotification); ("CoordinatedChannelClose"%go, CoordinatedChannelClose); ("DoubleValues"%go, DoubleValues)].

Definition msets' : list (go_string * (list (go_string * val))) := [].

#[global] Instance info' : PkgInfo channel.chan_spec_raw_examples :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [channel.channel];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init channel.chan_spec_raw_examples (λ: <>,
      exception_do (do:  channel.initialize')
      ).

End code.
End chan_spec_raw_examples.
