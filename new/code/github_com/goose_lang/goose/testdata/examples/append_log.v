(* autogenerated from github.com/goose-lang/goose/testdata/examples/append_log *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.disk.
From New.code Require github_com.tchajed.marshal.
From New.code Require sync.

From New Require Import disk_prelude.

Definition Log : go_type := structT [
  "m" :: ptrT;
  "sz" :: uint64T;
  "diskSz" :: uint64T
].

Definition Log__mset : list (string * val) := [
].

(* go: append_log.go:22:17 *)
Definition Log__mkHdr : val :=
  rec: "Log__mkHdr" "log" <> :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "enc" := (ref_ty marshal.Enc (zero_val marshal.Enc)) in
    let: "$r0" := (let: "$a0" := disk.BlockSize in
    marshal.NewEnc "$a0") in
    do:  ("enc" <-[marshal.Enc] "$r0");;;
    do:  (let: "$a0" := (![uint64T] (struct.field_ref Log "sz" (![ptrT] "log"))) in
    (marshal.Enc__PutInt (![marshal.Enc] "enc")) "$a0");;;
    do:  (let: "$a0" := (![uint64T] (struct.field_ref Log "diskSz" (![ptrT] "log"))) in
    (marshal.Enc__PutInt (![marshal.Enc] "enc")) "$a0");;;
    return: ((marshal.Enc__Finish (![marshal.Enc] "enc")) #())).

(* go: append_log.go:29:17 *)
Definition Log__writeHdr : val :=
  rec: "Log__writeHdr" "log" <> :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    do:  (let: "$a0" := #(W64 0) in
    let: "$a1" := ((Log__mkHdr (![ptrT] "log")) #()) in
    disk.Write "$a0" "$a1")).

(* go: append_log.go:65:6 *)
Definition writeAll : val :=
  rec: "writeAll" "bks" "off" :=
    exception_do (let: "off" := (ref_ty uint64T "off") in
    let: "bks" := (ref_ty sliceT "bks") in
    do:  (let: "$range" := (![sliceT] "bks") in
    slice.for_range sliceT "$range" (λ: "i" "bk",
      let: "i" := ref_ty uint64T "i" in
      let: "bk" := ref_ty sliceT "bk" in
      do:  (let: "$a0" := ((![uint64T] "off") + (![intT] "i")) in
      let: "$a1" := (![sliceT] "bk") in
      disk.Write "$a0" "$a1")))).

(* go: append_log.go:71:17 *)
Definition Log__append : val :=
  rec: "Log__append" "log" "bks" :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "bks" := (ref_ty sliceT "bks") in
    let: "sz" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (struct.field_ref Log "sz" (![ptrT] "log"))) in
    do:  ("sz" <-[uint64T] "$r0");;;
    (if: (let: "$a0" := (![sliceT] "bks") in
    slice.len "$a0") ≥ (((![uint64T] (struct.field_ref Log "diskSz" (![ptrT] "log"))) - #(W64 1)) - (![uint64T] "sz"))
    then return: (#false)
    else do:  #());;;
    do:  (let: "$a0" := (![sliceT] "bks") in
    let: "$a1" := (#(W64 1) + (![uint64T] "sz")) in
    writeAll "$a0" "$a1");;;
    do:  ((struct.field_ref Log "sz" (![ptrT] "log")) <-[uint64T] ((![uint64T] (struct.field_ref Log "sz" (![ptrT] "log"))) + (let: "$a0" := (![sliceT] "bks") in
    slice.len "$a0")));;;
    do:  ((Log__writeHdr (![ptrT] "log")) #());;;
    return: (#true)).

(* go: append_log.go:82:17 *)
Definition Log__Append : val :=
  rec: "Log__Append" "log" "bks" :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "bks" := (ref_ty sliceT "bks") in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #());;;
    let: "b" := (ref_ty boolT (zero_val boolT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "bks") in
    (Log__append (![ptrT] "log")) "$a0") in
    do:  ("b" <-[boolT] "$r0");;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #());;;
    return: (![boolT] "b")).

(* go: append_log.go:50:17 *)
Definition Log__get : val :=
  rec: "Log__get" "log" "i" :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "i" := (ref_ty uint64T "i") in
    let: "sz" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (struct.field_ref Log "sz" (![ptrT] "log"))) in
    do:  ("sz" <-[uint64T] "$r0");;;
    (if: (![uint64T] "i") < (![uint64T] "sz")
    then
      return: (let: "$a0" := (#(W64 1) + (![uint64T] "i")) in
       disk.Read "$a0", #true)
    else do:  #());;;
    return: (#slice.nil, #false)).

(* go: append_log.go:58:17 *)
Definition Log__Get : val :=
  rec: "Log__Get" "log" "i" :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "i" := (ref_ty uint64T "i") in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #());;;
    let: "b" := (ref_ty boolT (zero_val boolT)) in
    let: "v" := (ref_ty sliceT (zero_val sliceT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![uint64T] "i") in
    (Log__get (![ptrT] "log")) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("v" <-[sliceT] "$r0");;;
    do:  ("b" <-[boolT] "$r1");;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #());;;
    return: (![sliceT] "v", ![boolT] "b")).

(* go: append_log.go:89:17 *)
Definition Log__reset : val :=
  rec: "Log__reset" "log" <> :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "$r0" := #(W64 0) in
    do:  ((struct.field_ref Log "sz" (![ptrT] "log")) <-[uint64T] "$r0");;;
    do:  ((Log__writeHdr (![ptrT] "log")) #())).

(* go: append_log.go:94:17 *)
Definition Log__Reset : val :=
  rec: "Log__Reset" "log" <> :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #());;;
    do:  ((Log__reset (![ptrT] "log")) #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref Log "m" (![ptrT] "log")))) #())).

Definition Log__mset_ptr : list (string * val) := [
  ("Append", Log__Append%V);
  ("Get", Log__Get%V);
  ("Reset", Log__Reset%V);
  ("append", Log__append%V);
  ("get", Log__get%V);
  ("mkHdr", Log__mkHdr%V);
  ("reset", Log__reset%V);
  ("writeHdr", Log__writeHdr%V)
].

(* go: append_log.go:33:6 *)
Definition Init : val :=
  rec: "Init" "diskSz" :=
    exception_do (let: "diskSz" := (ref_ty uint64T "diskSz") in
    (if: (![uint64T] "diskSz") < #(W64 1)
    then
      return: (ref_ty Log (let: "$m" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
       let: "$sz" := #(W64 0) in
       let: "$diskSz" := #(W64 0) in
       struct.make Log [{
         "m" ::= "$m";
         "sz" ::= "$sz";
         "diskSz" ::= "$diskSz"
       }]), #false)
    else do:  #());;;
    let: "log" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty Log (let: "$m" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    let: "$sz" := #(W64 0) in
    let: "$diskSz" := (![uint64T] "diskSz") in
    struct.make Log [{
      "m" ::= "$m";
      "sz" ::= "$sz";
      "diskSz" ::= "$diskSz"
    }])) in
    do:  ("log" <-[ptrT] "$r0");;;
    do:  ((Log__writeHdr (![ptrT] "log")) #());;;
    return: (![ptrT] "log", #true)).

(* go: append_log.go:42:6 *)
Definition Open : val :=
  rec: "Open" <> :=
    exception_do (let: "hdr" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    disk.Read "$a0") in
    do:  ("hdr" <-[sliceT] "$r0");;;
    let: "dec" := (ref_ty marshal.Dec (zero_val marshal.Dec)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "hdr") in
    marshal.NewDec "$a0") in
    do:  ("dec" <-[marshal.Dec] "$r0");;;
    let: "sz" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((marshal.Dec__GetInt (![marshal.Dec] "dec")) #()) in
    do:  ("sz" <-[uint64T] "$r0");;;
    let: "diskSz" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((marshal.Dec__GetInt (![marshal.Dec] "dec")) #()) in
    do:  ("diskSz" <-[uint64T] "$r0");;;
    return: (ref_ty Log (let: "$m" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
     let: "$sz" := (![uint64T] "sz") in
     let: "$diskSz" := (![uint64T] "diskSz") in
     struct.make Log [{
       "m" ::= "$m";
       "sz" ::= "$sz";
       "diskSz" ::= "$diskSz"
     }]))).

Definition global_id' : string := "github.com/goose-lang/goose/testdata/examples/append_log".

Definition define' : val :=
  rec: "define'" <> :=
    exception_do (do:  #()).

Definition initialize' : val :=
  rec: "initialize'" <> :=
    exception_do (if: globals.is_uninitialized global_id'
    then
      do:  disk.initialize';;;
      do:  marshal.initialize';;;
      do:  sync.initialize';;;
      do:  (define' #())
    else do:  #()).
