(* autogenerated from github.com/mit-pdos/tulip/tulip *)
From Perennial.goose_lang Require Import prelude.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Value := struct.decl [
  "Present" :: boolT;
  "Content" :: stringT
].

Definition WriteEntry := struct.decl [
  "Key" :: stringT;
  "Value" :: struct.t Value
].

Definition Version := struct.decl [
  "Timestamp" :: uint64T;
  "Value" :: struct.t Value
].

Definition PrepareProposal := struct.decl [
  "Rank" :: uint64T;
  "Prepared" :: boolT
].

Definition CoordID := struct.decl [
  "GroupID" :: uint64T;
  "ReplicaID" :: uint64T
].

Definition KVMap: ty := mapT (struct.t Value).

Definition AddressMap: ty := mapT uint64T.

Definition AddressMaps: ty := mapT AddressMap.

Definition TXN_PREPARED : expr := #0.

Definition TXN_COMMITTED : expr := #1.

Definition TXN_ABORTED : expr := #2.

Definition REPLICA_OK : expr := #0.

Definition REPLICA_COMMITTED_TXN : expr := #1.

Definition REPLICA_ABORTED_TXN : expr := #2.

Definition REPLICA_STALE_COORDINATOR : expr := #3.

Definition REPLICA_FAILED_VALIDATION : expr := #4.

Definition REPLICA_INVALID_RANK : expr := #5.

Definition REPLICA_WRONG_LEADER : expr := #6.
