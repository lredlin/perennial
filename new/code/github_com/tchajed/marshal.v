(* autogenerated from github.com/tchajed/marshal *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.
From New.code Require github_com.goose_lang.std.

Section code.
Context `{ffi_syntax}.

Definition Enc : go_type := structT [
  "b" :: sliceT;
  "off" :: ptrT
].

Definition pkg_name' : go_string := "github.com/tchajed/marshal".

Definition Enc' : (go_string * go_string) := (pkg_name', "Enc").

(* go: marshal.go:13:6 *)
Definition NewEncFromSlice' : val :=
  rec: "NewEncFromSlice'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    return: (let: "$b" := (![sliceT] "b") in
     let: "$off" := (ref_ty uint64T (zero_val uint64T)) in
     struct.make Enc [{
       "b" ::= "$b";
       "off" ::= "$off"
     }])).

Definition NewEncFromSlice : (go_string * go_string) := (pkg_name', "NewEncFromSlice"%go).

(* go: marshal.go:20:6 *)
Definition NewEnc' : val :=
  rec: "NewEnc'" "sz" :=
    exception_do (let: "sz" := (ref_ty uint64T "sz") in
    let: "b" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make2 byteT (![uint64T] "sz")) in
    do:  ("b" <-[sliceT] "$r0");;;
    return: (let: "$a0" := (![sliceT] "b") in
     (func_call NewEncFromSlice #()) "$a0")).

Definition NewEnc : (go_string * go_string) := (pkg_name', "NewEnc"%go).

(* go: marshal.go:25:16 *)
Definition Enc__PutInt' : val :=
  rec: "Enc__PutInt'" "enc" "x" :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    let: "x" := (ref_ty uint64T "x") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![sliceT] (struct.field_ref Enc "b" "enc")) in
    slice.slice byteT "$s" (![uint64T] "off") (slice.len "$s")) in
    let: "$a1" := (![uint64T] "x") in
    (func_call primitive.UInt64Put #()) "$a0" "$a1");;;
    do:  ((![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #(W64 8)))).

(* go: marshal.go:31:16 *)
Definition Enc__PutInt32' : val :=
  rec: "Enc__PutInt32'" "enc" "x" :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    let: "x" := (ref_ty uint32T "x") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![sliceT] (struct.field_ref Enc "b" "enc")) in
    slice.slice byteT "$s" (![uint64T] "off") (slice.len "$s")) in
    let: "$a1" := (![uint32T] "x") in
    (func_call primitive.UInt32Put #()) "$a0" "$a1");;;
    do:  ((![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #(W64 4)))).

(* go: marshal.go:37:16 *)
Definition Enc__PutInts' : val :=
  rec: "Enc__PutInts'" "enc" "xs" :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    let: "xs" := (ref_ty sliceT "xs") in
    do:  (let: "$range" := (![sliceT] "xs") in
    slice.for_range uint64T "$range" (λ: <> "x",
      let: "x" := ref_ty uint64T "x" in
      do:  (let: "$a0" := (![uint64T] "x") in
      ((method_call Enc' "PutInt" #()) (![Enc] "enc")) "$a0")))).

(* go: marshal.go:43:16 *)
Definition Enc__PutBytes' : val :=
  rec: "Enc__PutBytes'" "enc" "b" :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    let: "b" := (ref_ty sliceT "b") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    let: "n" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (let: "$s" := (![sliceT] (struct.field_ref Enc "b" "enc")) in
    slice.slice byteT "$s" (![uint64T] "off") (slice.len "$s")) in
    let: "$a1" := (![sliceT] "b") in
    (slice.copy byteT) "$a0" "$a1") in
    do:  ("n" <-[uint64T] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + (![uint64T] "n")))).

(* go: marshal.go:49:6 *)
Definition bool2byte' : val :=
  rec: "bool2byte'" "b" :=
    exception_do (let: "b" := (ref_ty boolT "b") in
    (if: ![boolT] "b"
    then return: (#(W8 1))
    else return: (#(W8 0)))).

Definition bool2byte : (go_string * go_string) := (pkg_name', "bool2byte"%go).

(* go: marshal.go:57:16 *)
Definition Enc__PutBool' : val :=
  rec: "Enc__PutBool'" "enc" "b" :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    let: "b" := (ref_ty boolT "b") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    let: "$r0" := (let: "$a0" := (![boolT] "b") in
    (func_call bool2byte #()) "$a0") in
    do:  ((slice.elem_ref byteT (![sliceT] (struct.field_ref Enc "b" "enc")) (![uint64T] "off")) <-[byteT] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #(W64 1)))).

(* go: marshal.go:63:16 *)
Definition Enc__Finish' : val :=
  rec: "Enc__Finish'" "enc" <> :=
    exception_do (let: "enc" := (ref_ty Enc "enc") in
    return: (![sliceT] (struct.field_ref Enc "b" "enc"))).

Definition Dec : go_type := structT [
  "b" :: sliceT;
  "off" :: ptrT
].

Definition Dec' : (go_string * go_string) := (pkg_name', "Dec").

(* go: marshal.go:74:6 *)
Definition NewDec' : val :=
  rec: "NewDec'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    return: (let: "$b" := (![sliceT] "b") in
     let: "$off" := (ref_ty uint64T (zero_val uint64T)) in
     struct.make Dec [{
       "b" ::= "$b";
       "off" ::= "$off"
     }])).

Definition NewDec : (go_string * go_string) := (pkg_name', "NewDec"%go).

(* go: marshal.go:78:16 *)
Definition Dec__GetInt' : val :=
  rec: "Dec__GetInt'" "dec" <> :=
    exception_do (let: "dec" := (ref_ty Dec "dec") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #(W64 8)));;;
    return: (let: "$a0" := (let: "$s" := (![sliceT] (struct.field_ref Dec "b" "dec")) in
     slice.slice byteT "$s" (![uint64T] "off") (slice.len "$s")) in
     (func_call primitive.UInt64Get #()) "$a0")).

(* go: marshal.go:84:16 *)
Definition Dec__GetInt32' : val :=
  rec: "Dec__GetInt32'" "dec" <> :=
    exception_do (let: "dec" := (ref_ty Dec "dec") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #(W64 4)));;;
    return: (let: "$a0" := (let: "$s" := (![sliceT] (struct.field_ref Dec "b" "dec")) in
     slice.slice byteT "$s" (![uint64T] "off") (slice.len "$s")) in
     (func_call primitive.UInt32Get #()) "$a0")).

(* go: marshal.go:90:16 *)
Definition Dec__GetInts' : val :=
  rec: "Dec__GetInts'" "dec" "num" :=
    exception_do (let: "dec" := (ref_ty Dec "dec") in
    let: "num" := (ref_ty uint64T "num") in
    let: "xs" := (ref_ty sliceT (zero_val sliceT)) in
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "num")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "$r0" := (let: "$a0" := (![sliceT] "xs") in
      let: "$a1" := ((let: "$sl0" := (((method_call Dec' "GetInt" #()) (![Dec] "dec")) #()) in
      slice.literal uint64T ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("xs" <-[sliceT] "$r0")));;;
    return: (![sliceT] "xs")).

(* go: marshal.go:98:16 *)
Definition Dec__GetBytes' : val :=
  rec: "Dec__GetBytes'" "dec" "num" :=
    exception_do (let: "dec" := (ref_ty Dec "dec") in
    let: "num" := (ref_ty uint64T "num") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    let: "b" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$s" := (![sliceT] (struct.field_ref Dec "b" "dec")) in
    slice.slice byteT "$s" (![uint64T] "off") ((![uint64T] "off") + (![uint64T] "num"))) in
    do:  ("b" <-[sliceT] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + (![uint64T] "num")));;;
    return: (![sliceT] "b")).

(* go: marshal.go:105:16 *)
Definition Dec__GetBool' : val :=
  rec: "Dec__GetBool'" "dec" <> :=
    exception_do (let: "dec" := (ref_ty Dec "dec") in
    let: "off" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) in
    do:  ("off" <-[uint64T] "$r0");;;
    do:  ((![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #(W64 1)));;;
    (if: (![byteT] (slice.elem_ref byteT (![sliceT] (struct.field_ref Dec "b" "dec")) (![uint64T] "off"))) = #(W8 0)
    then return: (#false)
    else return: (#true))).

(* go: stateless.go:8:6 *)
Definition compute_new_cap' : val :=
  rec: "compute_new_cap'" "old_cap" "min_cap" :=
    exception_do (let: "min_cap" := (ref_ty uint64T "min_cap") in
    let: "old_cap" := (ref_ty uint64T "old_cap") in
    let: "new_cap" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((![uint64T] "old_cap") * #(W64 2)) in
    do:  ("new_cap" <-[uint64T] "$r0");;;
    (if: (![uint64T] "new_cap") < (![uint64T] "min_cap")
    then
      let: "$r0" := (![uint64T] "min_cap") in
      do:  ("new_cap" <-[uint64T] "$r0")
    else do:  #());;;
    return: (![uint64T] "new_cap")).

Definition compute_new_cap : (go_string * go_string) := (pkg_name', "compute_new_cap"%go).

(* Grow a slice to have at least `additional` unused bytes in the capacity.
   Runtime-check against overflow.

   go: stateless.go:19:6 *)
Definition reserve' : val :=
  rec: "reserve'" "b" "additional" :=
    exception_do (let: "additional" := (ref_ty uint64T "additional") in
    let: "b" := (ref_ty sliceT "b") in
    let: "min_cap" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (let: "$a0" := (![sliceT] "b") in
    slice.len "$a0") in
    let: "$a1" := (![uint64T] "additional") in
    (func_call std.SumAssumeNoOverflow #()) "$a0" "$a1") in
    do:  ("min_cap" <-[uint64T] "$r0");;;
    (if: (let: "$a0" := (![sliceT] "b") in
    slice.cap "$a0") < (![uint64T] "min_cap")
    then
      let: "new_cap" := (ref_ty uint64T (zero_val uint64T)) in
      let: "$r0" := (let: "$a0" := (let: "$a0" := (![sliceT] "b") in
      slice.cap "$a0") in
      let: "$a1" := (![uint64T] "min_cap") in
      (func_call compute_new_cap #()) "$a0" "$a1") in
      do:  ("new_cap" <-[uint64T] "$r0");;;
      let: "dest" := (ref_ty sliceT (zero_val sliceT)) in
      let: "$r0" := (slice.make3 byteT (let: "$a0" := (![sliceT] "b") in
      slice.len "$a0") (![uint64T] "new_cap")) in
      do:  ("dest" <-[sliceT] "$r0");;;
      do:  (let: "$a0" := (![sliceT] "dest") in
      let: "$a1" := (![sliceT] "b") in
      (slice.copy byteT) "$a0" "$a1");;;
      return: (![sliceT] "dest")
    else return: (![sliceT] "b"))).

Definition reserve : (go_string * go_string) := (pkg_name', "reserve"%go).

(* go: stateless.go:40:6 *)
Definition ReadInt' : val :=
  rec: "ReadInt'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    (func_call primitive.UInt64Get #()) "$a0") in
    do:  ("i" <-[uint64T] "$r0");;;
    return: (![uint64T] "i", let: "$s" := (![sliceT] "b") in
     slice.slice byteT "$s" #(W64 8) (slice.len "$s"))).

Definition ReadInt : (go_string * go_string) := (pkg_name', "ReadInt"%go).

(* go: stateless.go:45:6 *)
Definition ReadInt32' : val :=
  rec: "ReadInt32'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    let: "i" := (ref_ty uint32T (zero_val uint32T)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    (func_call primitive.UInt32Get #()) "$a0") in
    do:  ("i" <-[uint32T] "$r0");;;
    return: (![uint32T] "i", let: "$s" := (![sliceT] "b") in
     slice.slice byteT "$s" #(W64 4) (slice.len "$s"))).

Definition ReadInt32 : (go_string * go_string) := (pkg_name', "ReadInt32"%go).

(* ReadBytes reads `l` bytes from b and returns (bs, rest)

   go: stateless.go:51:6 *)
Definition ReadBytes' : val :=
  rec: "ReadBytes'" "b" "l" :=
    exception_do (let: "l" := (ref_ty uint64T "l") in
    let: "b" := (ref_ty sliceT "b") in
    let: "s" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$s" := (![sliceT] "b") in
    slice.slice byteT "$s" #(W64 0) (![uint64T] "l")) in
    do:  ("s" <-[sliceT] "$r0");;;
    return: (![sliceT] "s", let: "$s" := (![sliceT] "b") in
     slice.slice byteT "$s" (![uint64T] "l") (slice.len "$s"))).

Definition ReadBytes : (go_string * go_string) := (pkg_name', "ReadBytes"%go).

(* Like ReadBytes, but avoids keeping the source slice [b] alive.

   go: stateless.go:57:6 *)
Definition ReadBytesCopy' : val :=
  rec: "ReadBytesCopy'" "b" "l" :=
    exception_do (let: "l" := (ref_ty uint64T "l") in
    let: "b" := (ref_ty sliceT "b") in
    let: "s" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make2 byteT (![uint64T] "l")) in
    do:  ("s" <-[sliceT] "$r0");;;
    do:  (let: "$a0" := (![sliceT] "s") in
    let: "$a1" := (let: "$s" := (![sliceT] "b") in
    slice.slice byteT "$s" #(W64 0) (![uint64T] "l")) in
    (slice.copy byteT) "$a0" "$a1");;;
    return: (![sliceT] "s", let: "$s" := (![sliceT] "b") in
     slice.slice byteT "$s" (![uint64T] "l") (slice.len "$s"))).

Definition ReadBytesCopy : (go_string * go_string) := (pkg_name', "ReadBytesCopy"%go).

(* go: stateless.go:63:6 *)
Definition ReadBool' : val :=
  rec: "ReadBool'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    let: "x" := (ref_ty boolT (zero_val boolT)) in
    let: "$r0" := ((![byteT] (slice.elem_ref byteT (![sliceT] "b") #(W64 0))) ≠ #(W8 0)) in
    do:  ("x" <-[boolT] "$r0");;;
    return: (![boolT] "x", let: "$s" := (![sliceT] "b") in
     slice.slice byteT "$s" #(W64 1) (slice.len "$s"))).

Definition ReadBool : (go_string * go_string) := (pkg_name', "ReadBool"%go).

(* go: stateless.go:68:6 *)
Definition ReadLenPrefixedBytes' : val :=
  rec: "ReadLenPrefixedBytes'" "b" :=
    exception_do (let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "l" := (ref_ty uint64T (zero_val uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![sliceT] "b") in
    (func_call ReadInt #()) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("l" <-[uint64T] "$r0");;;
    do:  ("b2" <-[sliceT] "$r1");;;
    let: "b3" := (ref_ty sliceT (zero_val sliceT)) in
    let: "bs" := (ref_ty sliceT (zero_val sliceT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![sliceT] "b2") in
    let: "$a1" := (![uint64T] "l") in
    (func_call ReadBytes #()) "$a0" "$a1") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("bs" <-[sliceT] "$r0");;;
    do:  ("b3" <-[sliceT] "$r1");;;
    return: (![sliceT] "bs", ![sliceT] "b3")).

Definition ReadLenPrefixedBytes : (go_string * go_string) := (pkg_name', "ReadLenPrefixedBytes"%go).

(* WriteInt appends i in little-endian format to b, returning the new slice.

   go: stateless.go:77:6 *)
Definition WriteInt' : val :=
  rec: "WriteInt'" "b" "i" :=
    exception_do (let: "i" := (ref_ty uint64T "i") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    let: "$a1" := #(W64 8) in
    (func_call reserve #()) "$a0" "$a1") in
    do:  ("b2" <-[sliceT] "$r0");;;
    let: "off" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b2") in
    slice.len "$a0") in
    do:  ("off" <-[intT] "$r0");;;
    let: "b3" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$s" := (![sliceT] "b2") in
    slice.slice byteT "$s" #(W64 0) ((![intT] "off") + #(W64 8))) in
    do:  ("b3" <-[sliceT] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![sliceT] "b3") in
    slice.slice byteT "$s" (![intT] "off") (slice.len "$s")) in
    let: "$a1" := (![uint64T] "i") in
    (func_call primitive.UInt64Put #()) "$a0" "$a1");;;
    return: (![sliceT] "b3")).

Definition WriteInt : (go_string * go_string) := (pkg_name', "WriteInt"%go).

(* WriteInt32 appends 32-bit integer i in little-endian format to b, returning the new slice.

   go: stateless.go:87:6 *)
Definition WriteInt32' : val :=
  rec: "WriteInt32'" "b" "i" :=
    exception_do (let: "i" := (ref_ty uint32T "i") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    let: "$a1" := #(W64 4) in
    (func_call reserve #()) "$a0" "$a1") in
    do:  ("b2" <-[sliceT] "$r0");;;
    let: "off" := (ref_ty intT (zero_val intT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b2") in
    slice.len "$a0") in
    do:  ("off" <-[intT] "$r0");;;
    let: "b3" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$s" := (![sliceT] "b2") in
    slice.slice byteT "$s" #(W64 0) ((![intT] "off") + #(W64 4))) in
    do:  ("b3" <-[sliceT] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![sliceT] "b3") in
    slice.slice byteT "$s" (![intT] "off") (slice.len "$s")) in
    let: "$a1" := (![uint32T] "i") in
    (func_call primitive.UInt32Put #()) "$a0" "$a1");;;
    return: (![sliceT] "b3")).

Definition WriteInt32 : (go_string * go_string) := (pkg_name', "WriteInt32"%go).

(* Append data to b, returning the new slice.

   go: stateless.go:96:6 *)
Definition WriteBytes' : val :=
  rec: "WriteBytes'" "b" "data" :=
    exception_do (let: "data" := (ref_ty sliceT "data") in
    let: "b" := (ref_ty sliceT "b") in
    return: (let: "$a0" := (![sliceT] "b") in
     let: "$a1" := (![sliceT] "data") in
     (slice.append sliceT) "$a0" "$a1")).

Definition WriteBytes : (go_string * go_string) := (pkg_name', "WriteBytes"%go).

(* go: stateless.go:100:6 *)
Definition WriteBool' : val :=
  rec: "WriteBool'" "b" "x" :=
    exception_do (let: "x" := (ref_ty boolT "x") in
    let: "b" := (ref_ty sliceT "b") in
    (if: ![boolT] "x"
    then
      return: (let: "$a0" := (![sliceT] "b") in
       let: "$a1" := ((let: "$sl0" := #(W8 1) in
       slice.literal byteT ["$sl0"])) in
       (slice.append sliceT) "$a0" "$a1")
    else
      return: (let: "$a0" := (![sliceT] "b") in
       let: "$a1" := ((let: "$sl0" := #(W8 0) in
       slice.literal byteT ["$sl0"])) in
       (slice.append sliceT) "$a0" "$a1"))).

Definition WriteBool : (go_string * go_string) := (pkg_name', "WriteBool"%go).

(* go: stateless.go:108:6 *)
Definition WriteLenPrefixedBytes' : val :=
  rec: "WriteLenPrefixedBytes'" "b" "bs" :=
    exception_do (let: "bs" := (ref_ty sliceT "bs") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    let: "$a1" := (let: "$a0" := (![sliceT] "bs") in
    slice.len "$a0") in
    (func_call WriteInt #()) "$a0" "$a1") in
    do:  ("b2" <-[sliceT] "$r0");;;
    return: (let: "$a0" := (![sliceT] "b2") in
     let: "$a1" := (![sliceT] "bs") in
     (func_call WriteBytes #()) "$a0" "$a1")).

Definition WriteLenPrefixedBytes : (go_string * go_string) := (pkg_name', "WriteLenPrefixedBytes"%go).

(* go: stateless_slice.go:3:6 *)
Definition ReadSlice' (T: go_type) : val :=
  rec: "ReadSlice'" "b" "count" "readOne" :=
    exception_do (let: "readOne" := (ref_ty funcT "readOne") in
    let: "count" := (ref_ty uint64T "count") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (![sliceT] "b") in
    do:  ("b2" <-[sliceT] "$r0");;;
    let: "xs" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := #slice.nil in
    do:  ("xs" <-[sliceT] "$r0");;;
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "count")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "bNew" := (ref_ty sliceT (zero_val sliceT)) in
      let: "xNew" := (ref_ty T (zero_val T)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![sliceT] "b2") in
      (![funcT] "readOne") "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("xNew" <-[T] "$r0");;;
      do:  ("bNew" <-[sliceT] "$r1");;;
      let: "$r0" := (let: "$a0" := (![sliceT] "xs") in
      let: "$a1" := ((let: "$sl0" := (![T] "xNew") in
      slice.literal T ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("xs" <-[sliceT] "$r0");;;
      let: "$r0" := (![sliceT] "bNew") in
      do:  ("b2" <-[sliceT] "$r0")));;;
    return: (![sliceT] "xs", ![sliceT] "b2")).

Definition ReadSlice : (go_string * go_string) := (pkg_name', "ReadSlice"%go).

(* go: stateless_slice.go:14:6 *)
Definition ReadSliceLenPrefix' (T: go_type) : val :=
  rec: "ReadSliceLenPrefix'" "b" "readOne" :=
    exception_do (let: "readOne" := (ref_ty funcT "readOne") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "count" := (ref_ty uint64T (zero_val uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![sliceT] "b") in
    (func_call ReadInt #()) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("count" <-[uint64T] "$r0");;;
    do:  ("b2" <-[sliceT] "$r1");;;
    let: ("$ret0", "$ret1") := ((let: "$a0" := (![sliceT] "b2") in
    let: "$a1" := (![uint64T] "count") in
    let: "$a2" := (![funcT] "readOne") in
    (ReadSlice T) "$a0" "$a1" "$a2")) in
    return: ("$ret0", "$ret1")).

Definition ReadSliceLenPrefix : (go_string * go_string) := (pkg_name', "ReadSliceLenPrefix"%go).

(* go: stateless_slice.go:19:6 *)
Definition WriteSlice' (T: go_type) : val :=
  rec: "WriteSlice'" "b" "xs" "writeOne" :=
    exception_do (let: "writeOne" := (ref_ty funcT "writeOne") in
    let: "xs" := (ref_ty sliceT "xs") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (![sliceT] "b") in
    do:  ("b2" <-[sliceT] "$r0");;;
    do:  (let: "$range" := (![sliceT] "xs") in
    slice.for_range T "$range" (λ: <> "x",
      let: "x" := ref_ty T "x" in
      let: "$r0" := (let: "$a0" := (![T] "x") in
      let: "$a1" := (![sliceT] "b2") in
      (![funcT] "writeOne") "$a0" "$a1") in
      do:  ("b2" <-[sliceT] "$r0")));;;
    return: (![sliceT] "b2")).

Definition WriteSlice : (go_string * go_string) := (pkg_name', "WriteSlice"%go).

(* go: stateless_slice.go:27:6 *)
Definition WriteSliceLenPrefix' (T: go_type) : val :=
  rec: "WriteSliceLenPrefix'" "b" "xs" "writeOne" :=
    exception_do (let: "writeOne" := (ref_ty funcT "writeOne") in
    let: "xs" := (ref_ty sliceT "xs") in
    let: "b" := (ref_ty sliceT "b") in
    let: "b2" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b") in
    let: "$a1" := (let: "$a0" := (![sliceT] "xs") in
    slice.len "$a0") in
    (func_call WriteInt #()) "$a0" "$a1") in
    do:  ("b2" <-[sliceT] "$r0");;;
    let: "b3" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "b2") in
    let: "$a1" := (![sliceT] "xs") in
    let: "$a2" := (![funcT] "writeOne") in
    (WriteSlice T) "$a0" "$a1" "$a2") in
    do:  ("b3" <-[sliceT] "$r0");;;
    return: (![sliceT] "b3")).

Definition WriteSliceLenPrefix : (go_string * go_string) := (pkg_name', "WriteSliceLenPrefix"%go).

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  std.initialize';;;
      do:  primitive.initialize')
      ).

End code.
