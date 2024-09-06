(* autogenerated from github.com/mit-pdos/rsm/mpaxos *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition Paxos := struct.decl [
].

(* TODO: Figure do we need to return the term? *)
Definition Paxos__Propose: val :=
  rec: "Paxos__Propose" "px" "v" :=
    (#0, #0).

Definition Paxos__Lookup: val :=
  rec: "Paxos__Lookup" "px" "i" :=
    (#(str""), #false).

(* TODO: This really should be returning a slice of paxos objects, but now for
   simplicity let's just return one of them. *)
Definition MkPaxos: val :=
  rec: "MkPaxos" <> :=
    let: "px" := ref (zero_val ptrT) in
    ![ptrT] "px".

(* The goal of this example is to show the basic usage of consensus: getting the
   same value from two successful @px.Lookup. *)
Definition example1: val :=
  rec: "example1" <> :=
    let: "px" := MkPaxos #() in
    let: ("i1", <>) := Paxos__Propose "px" #(str"hello") in
    Paxos__Propose "px" #(str"world");;
    let: ("v1", "ok1") := Paxos__Lookup "px" "i1" in
    let: ("v2", "ok2") := Paxos__Lookup "px" "i1" in
    (if: "ok1" && "ok2"
    then
      control.impl.Assert ("v1" = "v2");;
      control.impl.Assert ((StringLength "v1") = #5);;
      #()
    else #()).

(* The goal of this example is to show how to construct invariants on the
   candidate set, and then transfer those invariants to the consensus using the
   inclusion property between the consensus and the candidate set. The specific
   invariant here is a "dependency invariant" that says "hello" must precede
   "world" in the replicated log. This kind of invariants is necessary in
   distributed transactions (e.g., prepares must precede commits). *)
Definition example2: val :=
  rec: "example2" <> :=
    let: "px" := MkPaxos #() in
    let: ("i", <>) := Paxos__Propose "px" #(str"hello") in
    let: ("v", "ok") := Paxos__Lookup "px" "i" in
    (if: "ok" && ("v" = #(str"hello"))
    then
      Paxos__Propose "px" #(str"world");;
      #()
    else #()).

End code.
