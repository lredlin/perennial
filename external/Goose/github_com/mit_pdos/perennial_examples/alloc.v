(* autogenerated from github.com/mit-pdos/perennial-examples/alloc *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition unit := struct.decl [
].

Notation AddrSet := (mapT (struct.t unit)) (only parsing).

(* Allocator manages free disk blocks. It does not store its state durably, so
   the caller is responsible for returning its set of free disk blocks on
   recovery. *)
Definition Allocator := struct.decl [
  "m" :: ptrT;
  "free" :: mapT (struct.t unit)
].

Definition freeRange: val :=
  rec: "freeRange" "start" "sz" :=
    let: "m" := NewMap uint64T (struct.t unit) #() in
    let: "end" := "start" + "sz" in
    let: "i" := ref_to uint64T "start" in
    (for: (λ: <>, (![uint64T] "i") < "end"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      MapInsert "m" (![uint64T] "i") (struct.mk unit [
      ]);;
      Continue);;
    "m".

(* mapRemove deletes addresses in remove from m

   like m -= remove *)
Definition mapRemove: val :=
  rec: "mapRemove" "m" "remove" :=
    MapIter "remove" (λ: "k" <>,
      MapDelete "m" "k");;
    #().

(* SetAdd adds addresses in add to m

   like m += add *)
Definition SetAdd: val :=
  rec: "SetAdd" "m" "add" :=
    ForSlice uint64T <> "k" "add"
      (MapInsert "m" "k" (struct.mk unit [
      ]));;
    #().

Definition New: val :=
  rec: "New" "start" "sz" "used" :=
    let: "free" := freeRange "start" "sz" in
    mapRemove "free" "used";;
    struct.new Allocator [
      "m" ::= newMutex #();
      "free" ::= "free"
    ].

Definition findKey: val :=
  rec: "findKey" "m" :=
    let: "found" := ref_to uint64T #0 in
    let: "ok" := ref_to boolT #false in
    MapIter "m" (λ: "k" <>,
      (if: (~ (![boolT] "ok"))
      then
        "found" <-[uint64T] "k";;
        "ok" <-[boolT] #true
      else #()));;
    (![uint64T] "found", ![boolT] "ok").

(* Reserve transfers ownership of a free block from the Allocator to the caller

   The initial contents of the block are arbitrary. *)
Definition Allocator__Reserve: val :=
  rec: "Allocator__Reserve" "a" :=
    Mutex__Lock (struct.loadF Allocator "m" "a");;
    let: ("k", "ok") := findKey (struct.loadF Allocator "free" "a") in
    MapDelete (struct.loadF Allocator "free" "a") "k";;
    Linearize;;
    Mutex__Unlock (struct.loadF Allocator "m" "a");;
    ("k", "ok").

Definition Allocator__Free: val :=
  rec: "Allocator__Free" "a" "addr" :=
    Mutex__Lock (struct.loadF Allocator "m" "a");;
    MapInsert (struct.loadF Allocator "free" "a") "addr" (struct.mk unit [
    ]);;
    Linearize;;
    Mutex__Unlock (struct.loadF Allocator "m" "a");;
    #().

End code.
