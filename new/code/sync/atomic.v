(* autogenerated from sync/atomic *)
From New.golang Require Import defn.

Require Export New.trusted_code.sync.atomic.
Import atomic.
Definition atomic : go_string := "sync/atomic".

Module atomic.
Section code.
Context `{ffi_syntax}.


Definition noCopy : go_type := structT [
].

Definition Int32 : go_type := structT [
  "_0" :: noCopy;
  "v" :: int32T
].

(* Load atomically loads and returns the value stored in x.

   go: type.go:74:17 *)
Definition Int32__Load : val :=
  rec: "Int32__Load" "x" <> :=
    exception_do (let: "x" := (mem.alloc "x") in
    return: (let: "$a0" := (struct.field_ref #Int32 #"v"%go (![#ptrT] "x")) in
     (func_call #atomic.atomic #"LoadInt32"%go) "$a0")).

(* Store atomically stores val into x.

   go: type.go:77:17 *)
Definition Int32__Store : val :=
  rec: "Int32__Store" "x" "val" :=
    exception_do (let: "x" := (mem.alloc "x") in
    let: "val" := (mem.alloc "val") in
    do:  (let: "$a0" := (struct.field_ref #Int32 #"v"%go (![#ptrT] "x")) in
    let: "$a1" := (![#int32T] "val") in
    (func_call #atomic.atomic #"StoreInt32"%go) "$a0" "$a1")).

(* CompareAndSwap executes the compare-and-swap operation for x.

   go: type.go:83:17 *)
Definition Int32__CompareAndSwap : val :=
  rec: "Int32__CompareAndSwap" "x" "old" "new" :=
    exception_do (let: "swapped" := (mem.alloc (type.zero_val #boolT)) in
    let: "x" := (mem.alloc "x") in
    let: "new" := (mem.alloc "new") in
    let: "old" := (mem.alloc "old") in
    return: (let: "$a0" := (struct.field_ref #Int32 #"v"%go (![#ptrT] "x")) in
     let: "$a1" := (![#int32T] "old") in
     let: "$a2" := (![#int32T] "new") in
     (func_call #atomic.atomic #"CompareAndSwapInt32"%go) "$a0" "$a1" "$a2")).

(* Add atomically adds delta to x and returns the new value.

   go: type.go:88:17 *)
Definition Int32__Add : val :=
  rec: "Int32__Add" "x" "delta" :=
    exception_do (let: "new" := (mem.alloc (type.zero_val #int32T)) in
    let: "x" := (mem.alloc "x") in
    let: "delta" := (mem.alloc "delta") in
    return: (let: "$a0" := (struct.field_ref #Int32 #"v"%go (![#ptrT] "x")) in
     let: "$a1" := (![#int32T] "delta") in
     (func_call #atomic.atomic #"AddInt32"%go) "$a0" "$a1")).

Definition align64 : go_type := structT [
].

Definition Uint64 : go_type := structT [
  "_0" :: noCopy;
  "_1" :: align64;
  "v" :: uint64T
].

(* Load atomically loads and returns the value stored in x.

   go: type.go:169:18 *)
Definition Uint64__Load : val :=
  rec: "Uint64__Load" "x" <> :=
    exception_do (let: "x" := (mem.alloc "x") in
    return: (let: "$a0" := (struct.field_ref #Uint64 #"v"%go (![#ptrT] "x")) in
     (func_call #atomic.atomic #"LoadUint64"%go) "$a0")).

(* Store atomically stores val into x.

   go: type.go:172:18 *)
Definition Uint64__Store : val :=
  rec: "Uint64__Store" "x" "val" :=
    exception_do (let: "x" := (mem.alloc "x") in
    let: "val" := (mem.alloc "val") in
    do:  (let: "$a0" := (struct.field_ref #Uint64 #"v"%go (![#ptrT] "x")) in
    let: "$a1" := (![#uint64T] "val") in
    (func_call #atomic.atomic #"StoreUint64"%go) "$a0" "$a1")).

(* CompareAndSwap executes the compare-and-swap operation for x.

   go: type.go:178:18 *)
Definition Uint64__CompareAndSwap : val :=
  rec: "Uint64__CompareAndSwap" "x" "old" "new" :=
    exception_do (let: "swapped" := (mem.alloc (type.zero_val #boolT)) in
    let: "x" := (mem.alloc "x") in
    let: "new" := (mem.alloc "new") in
    let: "old" := (mem.alloc "old") in
    return: (let: "$a0" := (struct.field_ref #Uint64 #"v"%go (![#ptrT] "x")) in
     let: "$a1" := (![#uint64T] "old") in
     let: "$a2" := (![#uint64T] "new") in
     (func_call #atomic.atomic #"CompareAndSwapUint64"%go) "$a0" "$a1" "$a2")).

(* Add atomically adds delta to x and returns the new value.

   go: type.go:183:18 *)
Definition Uint64__Add : val :=
  rec: "Uint64__Add" "x" "delta" :=
    exception_do (let: "new" := (mem.alloc (type.zero_val #uint64T)) in
    let: "x" := (mem.alloc "x") in
    let: "delta" := (mem.alloc "delta") in
    return: (let: "$a0" := (struct.field_ref #Uint64 #"v"%go (![#ptrT] "x")) in
     let: "$a1" := (![#uint64T] "delta") in
     (func_call #atomic.atomic #"AddUint64"%go) "$a0" "$a1")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("CompareAndSwapInt32"%go, CompareAndSwapInt32); ("AddInt32"%go, AddInt32); ("LoadInt32"%go, LoadInt32); ("StoreInt32"%go, StoreInt32); ("CompareAndSwapUint64"%go, CompareAndSwapUint64); ("AddUint64"%go, AddUint64); ("LoadUint64"%go, LoadUint64); ("StoreUint64"%go, StoreUint64)].

Definition msets' : list (go_string * (list (go_string * val))) := [("Int32"%go, []); ("Int32'ptr"%go, [("Add"%go, Int32__Add); ("CompareAndSwap"%go, Int32__CompareAndSwap); ("Load"%go, Int32__Load); ("Store"%go, Int32__Store)]); ("Uint64"%go, []); ("Uint64'ptr"%go, [("Add"%go, Uint64__Add); ("CompareAndSwap"%go, Uint64__CompareAndSwap); ("Load"%go, Uint64__Load); ("Store"%go, Uint64__Store)]); ("noCopy"%go, []); ("noCopy'ptr"%go, []); ("align64"%go, []); ("align64'ptr"%go, [])].

#[global] Instance info' : PkgInfo atomic.atomic :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init atomic.atomic (λ: <>,
      exception_do (do:  (_'init #()))
      ).

End code.
End atomic.
