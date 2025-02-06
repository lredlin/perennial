(* autogenerated from github.com/mit-pdos/gokv/lockservice *)
From New.golang Require Import defn.
Require Export New.code.github_com.mit_pdos.gokv.kv.

Module lockservice.
Section code.
Context `{ffi_syntax}.


Definition LockClerk : go_type := structT [
  "kv" :: kv.KvCput
].

(* go: lock_clerk.go:11:22 *)
Definition LockClerk__Lock : val :=
  rec: "LockClerk__Lock" "ck" "key" :=
    exception_do (let: "ck" := (ref_ty ptrT "ck") in
    let: "key" := (ref_ty stringT "key") in
    (for: (λ: <>, (let: "$a0" := (![stringT] "key") in
    let: "$a1" := #""%go in
    let: "$a2" := #"1"%go in
    (interface.get "ConditionalPut" (![kv.KvCput] (struct.field_ref LockClerk "kv" (![ptrT] "ck")))) "$a0" "$a1" "$a2") ≠ #"ok"%go); (λ: <>, Skip) := λ: <>,
      do:  #())).

(* go: lock_clerk.go:16:22 *)
Definition LockClerk__Unlock : val :=
  rec: "LockClerk__Unlock" "ck" "key" :=
    exception_do (let: "ck" := (ref_ty ptrT "ck") in
    let: "key" := (ref_ty stringT "key") in
    do:  (let: "$a0" := (![stringT] "key") in
    let: "$a1" := #""%go in
    (interface.get "Put" (![kv.KvCput] (struct.field_ref LockClerk "kv" (![ptrT] "ck")))) "$a0" "$a1")).

(* go: lock_clerk.go:20:6 *)
Definition MakeLockClerk : val :=
  rec: "MakeLockClerk" "kv" :=
    exception_do (let: "kv" := (ref_ty kv.KvCput "kv") in
    return: (ref_ty LockClerk (let: "$kv" := (![kv.KvCput] "kv") in
     struct.make LockClerk [{
       "kv" ::= "$kv"
     }]))).

Definition pkg_name' : go_string := "github.com/mit-pdos/gokv/lockservice".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("MakeLockClerk"%go, MakeLockClerk)].

Definition msets' : list (go_string * (list (go_string * val))) := [("LockClerk"%go, []); ("LockClerk'ptr"%go, [("Lock"%go, LockClerk__Lock); ("Unlock"%go, LockClerk__Unlock)])].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  kv.initialize')
      ).

End code.
End lockservice.
