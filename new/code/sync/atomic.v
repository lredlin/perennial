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
    exception_do (let: "x" := (ref_ty ptrT "x") in
    return: (let: "$a0" := (struct.field_ref Uint64 "v" (![ptrT] "x")) in
     (func_call #atomic.atomic #"LoadUint64"%go) "$a0")).

(* Store atomically stores val into x.

   go: type.go:172:18 *)
Definition Uint64__Store : val :=
  rec: "Uint64__Store" "x" "val" :=
    exception_do (let: "x" := (ref_ty ptrT "x") in
    let: "val" := (ref_ty uint64T "val") in
    do:  (let: "$a0" := (struct.field_ref Uint64 "v" (![ptrT] "x")) in
    let: "$a1" := (![uint64T] "val") in
    (func_call #atomic.atomic #"StoreUint64"%go) "$a0" "$a1")).

(* CompareAndSwap executes the compare-and-swap operation for x.

   go: type.go:178:18 *)
Definition Uint64__CompareAndSwap : val :=
  rec: "Uint64__CompareAndSwap" "x" "old" "new" :=
    exception_do (let: "swapped" := (ref_ty boolT (zero_val boolT)) in
    let: "x" := (ref_ty ptrT "x") in
    let: "new" := (ref_ty uint64T "new") in
    let: "old" := (ref_ty uint64T "old") in
    return: (let: "$a0" := (struct.field_ref Uint64 "v" (![ptrT] "x")) in
     let: "$a1" := (![uint64T] "old") in
     let: "$a2" := (![uint64T] "new") in
     (func_call #atomic.atomic #"CompareAndSwapUint64"%go) "$a0" "$a1" "$a2")).

(* Add atomically adds delta to x and returns the new value.

   go: type.go:183:18 *)
Definition Uint64__Add : val :=
  rec: "Uint64__Add" "x" "delta" :=
    exception_do (let: "new" := (ref_ty uint64T (zero_val uint64T)) in
    let: "x" := (ref_ty ptrT "x") in
    let: "delta" := (ref_ty uint64T "delta") in
    return: (let: "$a0" := (struct.field_ref Uint64 "v" (![ptrT] "x")) in
     let: "$a1" := (![uint64T] "delta") in
     (func_call #atomic.atomic #"AddUint64"%go) "$a0" "$a1")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("CompareAndSwapUint64"%go, CompareAndSwapUint64); ("AddUint64"%go, AddUint64); ("LoadUint64"%go, LoadUint64); ("StoreUint64"%go, StoreUint64)].

Definition msets' : list (go_string * (list (go_string * val))) := [("Uint64"%go, []); ("Uint64'ptr"%go, [("Add"%go, Uint64__Add); ("CompareAndSwap"%go, Uint64__CompareAndSwap); ("Load"%go, Uint64__Load); ("Store"%go, Uint64__Store)]); ("noCopy"%go, []); ("noCopy'ptr"%go, []); ("align64"%go, []); ("align64'ptr"%go, [])].

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
