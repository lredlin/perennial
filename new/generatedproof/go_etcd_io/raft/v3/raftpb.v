(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

Require Export New.code.go_etcd_io.raft.v3.raftpb.

Set Default Proof Using "Type".

Module raftpb.

(* type raftpb.ConfChangeI *)
Module ConfChangeI.
Section def.
Context `{ffi_syntax}.
Definition t := interface.t.
End def.
End ConfChangeI.

(* type raftpb.EntryType *)
Module EntryType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End EntryType.

(* type raftpb.MessageType *)
Module MessageType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End MessageType.

(* type raftpb.ConfChangeTransition *)
Module ConfChangeTransition.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End ConfChangeTransition.

(* type raftpb.ConfChangeType *)
Module ConfChangeType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End ConfChangeType.

(* type raftpb.Entry *)
Module Entry.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Term' : w64;
  Index' : w64;
  Type' : EntryType.t;
  Data' : slice.t;
}.
End def.
End Entry.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Entry : Settable Entry.t :=
  settable! Entry.mk < Entry.Term'; Entry.Index'; Entry.Type'; Entry.Data' >.
Global Instance into_val_Entry : IntoVal Entry.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.Entry [
    "Term" ::= #(Entry.Term' v);
    "Index" ::= #(Entry.Index' v);
    "Type" ::= #(Entry.Type' v);
    "Data" ::= #(Entry.Data' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Entry : IntoValTyped Entry.t raftpb.Entry :=
{|
  default_val := Entry.mk (default_val _) (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Entry_Term : IntoValStructField "Term" raftpb.Entry Entry.Term'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Entry_Index : IntoValStructField "Index" raftpb.Entry Entry.Index'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Entry_Type : IntoValStructField "Type" raftpb.Entry Entry.Type'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Entry_Data : IntoValStructField "Data" raftpb.Entry Entry.Data'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Entry Term' Index' Type' Data':
  PureWp True
    (struct.make #raftpb.Entry (alist_val [
      "Term" ::= #Term';
      "Index" ::= #Index';
      "Type" ::= #Type';
      "Data" ::= #Data'
    ]))%struct
    #(Entry.mk Term' Index' Type' Data').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Entry_struct_fields_split dq l (v : Entry.t) :
  StructFieldsSplit dq l v (
    "HTerm" ∷ l ↦s[raftpb.Entry :: "Term"]{dq} v.(Entry.Term') ∗
    "HIndex" ∷ l ↦s[raftpb.Entry :: "Index"]{dq} v.(Entry.Index') ∗
    "HType" ∷ l ↦s[raftpb.Entry :: "Type"]{dq} v.(Entry.Type') ∗
    "HData" ∷ l ↦s[raftpb.Entry :: "Data"]{dq} v.(Entry.Data')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (Entry.Term' v)) raftpb.Entry "Term"%go.
  simpl_one_flatten_struct (# (Entry.Index' v)) raftpb.Entry "Index"%go.
  simpl_one_flatten_struct (# (Entry.Type' v)) raftpb.Entry "Type"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.ConfState *)
Module ConfState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Voters' : slice.t;
  Learners' : slice.t;
  VotersOutgoing' : slice.t;
  LearnersNext' : slice.t;
  AutoLeave' : bool;
}.
End def.
End ConfState.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_ConfState : Settable ConfState.t :=
  settable! ConfState.mk < ConfState.Voters'; ConfState.Learners'; ConfState.VotersOutgoing'; ConfState.LearnersNext'; ConfState.AutoLeave' >.
Global Instance into_val_ConfState : IntoVal ConfState.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.ConfState [
    "Voters" ::= #(ConfState.Voters' v);
    "Learners" ::= #(ConfState.Learners' v);
    "VotersOutgoing" ::= #(ConfState.VotersOutgoing' v);
    "LearnersNext" ::= #(ConfState.LearnersNext' v);
    "AutoLeave" ::= #(ConfState.AutoLeave' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_ConfState : IntoValTyped ConfState.t raftpb.ConfState :=
{|
  default_val := ConfState.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_ConfState_Voters : IntoValStructField "Voters" raftpb.ConfState ConfState.Voters'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfState_Learners : IntoValStructField "Learners" raftpb.ConfState ConfState.Learners'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfState_VotersOutgoing : IntoValStructField "VotersOutgoing" raftpb.ConfState ConfState.VotersOutgoing'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfState_LearnersNext : IntoValStructField "LearnersNext" raftpb.ConfState ConfState.LearnersNext'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfState_AutoLeave : IntoValStructField "AutoLeave" raftpb.ConfState ConfState.AutoLeave'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfState Voters' Learners' VotersOutgoing' LearnersNext' AutoLeave':
  PureWp True
    (struct.make #raftpb.ConfState (alist_val [
      "Voters" ::= #Voters';
      "Learners" ::= #Learners';
      "VotersOutgoing" ::= #VotersOutgoing';
      "LearnersNext" ::= #LearnersNext';
      "AutoLeave" ::= #AutoLeave'
    ]))%struct
    #(ConfState.mk Voters' Learners' VotersOutgoing' LearnersNext' AutoLeave').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance ConfState_struct_fields_split dq l (v : ConfState.t) :
  StructFieldsSplit dq l v (
    "HVoters" ∷ l ↦s[raftpb.ConfState :: "Voters"]{dq} v.(ConfState.Voters') ∗
    "HLearners" ∷ l ↦s[raftpb.ConfState :: "Learners"]{dq} v.(ConfState.Learners') ∗
    "HVotersOutgoing" ∷ l ↦s[raftpb.ConfState :: "VotersOutgoing"]{dq} v.(ConfState.VotersOutgoing') ∗
    "HLearnersNext" ∷ l ↦s[raftpb.ConfState :: "LearnersNext"]{dq} v.(ConfState.LearnersNext') ∗
    "HAutoLeave" ∷ l ↦s[raftpb.ConfState :: "AutoLeave"]{dq} v.(ConfState.AutoLeave')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (ConfState.Voters' v)) raftpb.ConfState "Voters"%go.
  simpl_one_flatten_struct (# (ConfState.Learners' v)) raftpb.ConfState "Learners"%go.
  simpl_one_flatten_struct (# (ConfState.VotersOutgoing' v)) raftpb.ConfState "VotersOutgoing"%go.
  simpl_one_flatten_struct (# (ConfState.LearnersNext' v)) raftpb.ConfState "LearnersNext"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.SnapshotMetadata *)
Module SnapshotMetadata.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  ConfState' : ConfState.t;
  Index' : w64;
  Term' : w64;
}.
End def.
End SnapshotMetadata.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_SnapshotMetadata : Settable SnapshotMetadata.t :=
  settable! SnapshotMetadata.mk < SnapshotMetadata.ConfState'; SnapshotMetadata.Index'; SnapshotMetadata.Term' >.
Global Instance into_val_SnapshotMetadata : IntoVal SnapshotMetadata.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.SnapshotMetadata [
    "ConfState" ::= #(SnapshotMetadata.ConfState' v);
    "Index" ::= #(SnapshotMetadata.Index' v);
    "Term" ::= #(SnapshotMetadata.Term' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_SnapshotMetadata : IntoValTyped SnapshotMetadata.t raftpb.SnapshotMetadata :=
{|
  default_val := SnapshotMetadata.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_SnapshotMetadata_ConfState : IntoValStructField "ConfState" raftpb.SnapshotMetadata SnapshotMetadata.ConfState'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_SnapshotMetadata_Index : IntoValStructField "Index" raftpb.SnapshotMetadata SnapshotMetadata.Index'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_SnapshotMetadata_Term : IntoValStructField "Term" raftpb.SnapshotMetadata SnapshotMetadata.Term'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_SnapshotMetadata ConfState' Index' Term':
  PureWp True
    (struct.make #raftpb.SnapshotMetadata (alist_val [
      "ConfState" ::= #ConfState';
      "Index" ::= #Index';
      "Term" ::= #Term'
    ]))%struct
    #(SnapshotMetadata.mk ConfState' Index' Term').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance SnapshotMetadata_struct_fields_split dq l (v : SnapshotMetadata.t) :
  StructFieldsSplit dq l v (
    "HConfState" ∷ l ↦s[raftpb.SnapshotMetadata :: "ConfState"]{dq} v.(SnapshotMetadata.ConfState') ∗
    "HIndex" ∷ l ↦s[raftpb.SnapshotMetadata :: "Index"]{dq} v.(SnapshotMetadata.Index') ∗
    "HTerm" ∷ l ↦s[raftpb.SnapshotMetadata :: "Term"]{dq} v.(SnapshotMetadata.Term')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (SnapshotMetadata.ConfState' v)) raftpb.SnapshotMetadata "ConfState"%go.
  simpl_one_flatten_struct (# (SnapshotMetadata.Index' v)) raftpb.SnapshotMetadata "Index"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.Snapshot *)
Module Snapshot.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Data' : slice.t;
  Metadata' : SnapshotMetadata.t;
}.
End def.
End Snapshot.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Snapshot : Settable Snapshot.t :=
  settable! Snapshot.mk < Snapshot.Data'; Snapshot.Metadata' >.
Global Instance into_val_Snapshot : IntoVal Snapshot.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.Snapshot [
    "Data" ::= #(Snapshot.Data' v);
    "Metadata" ::= #(Snapshot.Metadata' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Snapshot : IntoValTyped Snapshot.t raftpb.Snapshot :=
{|
  default_val := Snapshot.mk (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Snapshot_Data : IntoValStructField "Data" raftpb.Snapshot Snapshot.Data'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Snapshot_Metadata : IntoValStructField "Metadata" raftpb.Snapshot Snapshot.Metadata'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Snapshot Data' Metadata':
  PureWp True
    (struct.make #raftpb.Snapshot (alist_val [
      "Data" ::= #Data';
      "Metadata" ::= #Metadata'
    ]))%struct
    #(Snapshot.mk Data' Metadata').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Snapshot_struct_fields_split dq l (v : Snapshot.t) :
  StructFieldsSplit dq l v (
    "HData" ∷ l ↦s[raftpb.Snapshot :: "Data"]{dq} v.(Snapshot.Data') ∗
    "HMetadata" ∷ l ↦s[raftpb.Snapshot :: "Metadata"]{dq} v.(Snapshot.Metadata')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (Snapshot.Data' v)) raftpb.Snapshot "Data"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.Message *)
Module Message.
Section def.
Context `{ffi_syntax}.
Axiom t : Type.
End def.
End Message.

Global Instance bounded_size_Message : BoundedTypeSize raftpb.Message.
Admitted.

Global Instance into_val_Message `{ffi_syntax} : IntoVal Message.t.
Admitted.

Global Instance into_val_typed_Message `{ffi_syntax} : IntoValTyped Message.t raftpb.Message.
Admitted.

(* type raftpb.HardState *)
Module HardState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Term' : w64;
  Vote' : w64;
  Commit' : w64;
}.
End def.
End HardState.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_HardState : Settable HardState.t :=
  settable! HardState.mk < HardState.Term'; HardState.Vote'; HardState.Commit' >.
Global Instance into_val_HardState : IntoVal HardState.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.HardState [
    "Term" ::= #(HardState.Term' v);
    "Vote" ::= #(HardState.Vote' v);
    "Commit" ::= #(HardState.Commit' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_HardState : IntoValTyped HardState.t raftpb.HardState :=
{|
  default_val := HardState.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_HardState_Term : IntoValStructField "Term" raftpb.HardState HardState.Term'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_HardState_Vote : IntoValStructField "Vote" raftpb.HardState HardState.Vote'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_HardState_Commit : IntoValStructField "Commit" raftpb.HardState HardState.Commit'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_HardState Term' Vote' Commit':
  PureWp True
    (struct.make #raftpb.HardState (alist_val [
      "Term" ::= #Term';
      "Vote" ::= #Vote';
      "Commit" ::= #Commit'
    ]))%struct
    #(HardState.mk Term' Vote' Commit').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance HardState_struct_fields_split dq l (v : HardState.t) :
  StructFieldsSplit dq l v (
    "HTerm" ∷ l ↦s[raftpb.HardState :: "Term"]{dq} v.(HardState.Term') ∗
    "HVote" ∷ l ↦s[raftpb.HardState :: "Vote"]{dq} v.(HardState.Vote') ∗
    "HCommit" ∷ l ↦s[raftpb.HardState :: "Commit"]{dq} v.(HardState.Commit')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (HardState.Term' v)) raftpb.HardState "Term"%go.
  simpl_one_flatten_struct (# (HardState.Vote' v)) raftpb.HardState "Vote"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.ConfChange *)
Module ConfChange.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Type' : ConfChangeType.t;
  NodeID' : w64;
  Context' : slice.t;
  ID' : w64;
}.
End def.
End ConfChange.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_ConfChange : Settable ConfChange.t :=
  settable! ConfChange.mk < ConfChange.Type'; ConfChange.NodeID'; ConfChange.Context'; ConfChange.ID' >.
Global Instance into_val_ConfChange : IntoVal ConfChange.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.ConfChange [
    "Type" ::= #(ConfChange.Type' v);
    "NodeID" ::= #(ConfChange.NodeID' v);
    "Context" ::= #(ConfChange.Context' v);
    "ID" ::= #(ConfChange.ID' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_ConfChange : IntoValTyped ConfChange.t raftpb.ConfChange :=
{|
  default_val := ConfChange.mk (default_val _) (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_ConfChange_Type : IntoValStructField "Type" raftpb.ConfChange ConfChange.Type'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfChange_NodeID : IntoValStructField "NodeID" raftpb.ConfChange ConfChange.NodeID'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfChange_Context : IntoValStructField "Context" raftpb.ConfChange ConfChange.Context'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfChange_ID : IntoValStructField "ID" raftpb.ConfChange ConfChange.ID'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfChange Type' NodeID' Context' ID':
  PureWp True
    (struct.make #raftpb.ConfChange (alist_val [
      "Type" ::= #Type';
      "NodeID" ::= #NodeID';
      "Context" ::= #Context';
      "ID" ::= #ID'
    ]))%struct
    #(ConfChange.mk Type' NodeID' Context' ID').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance ConfChange_struct_fields_split dq l (v : ConfChange.t) :
  StructFieldsSplit dq l v (
    "HType" ∷ l ↦s[raftpb.ConfChange :: "Type"]{dq} v.(ConfChange.Type') ∗
    "HNodeID" ∷ l ↦s[raftpb.ConfChange :: "NodeID"]{dq} v.(ConfChange.NodeID') ∗
    "HContext" ∷ l ↦s[raftpb.ConfChange :: "Context"]{dq} v.(ConfChange.Context') ∗
    "HID" ∷ l ↦s[raftpb.ConfChange :: "ID"]{dq} v.(ConfChange.ID')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (ConfChange.Type' v)) raftpb.ConfChange "Type"%go.
  simpl_one_flatten_struct (# (ConfChange.NodeID' v)) raftpb.ConfChange "NodeID"%go.
  simpl_one_flatten_struct (# (ConfChange.Context' v)) raftpb.ConfChange "Context"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type raftpb.ConfChangeV2 *)
Module ConfChangeV2.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Transition' : ConfChangeTransition.t;
  Changes' : slice.t;
  Context' : slice.t;
}.
End def.
End ConfChangeV2.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_ConfChangeV2 : Settable ConfChangeV2.t :=
  settable! ConfChangeV2.mk < ConfChangeV2.Transition'; ConfChangeV2.Changes'; ConfChangeV2.Context' >.
Global Instance into_val_ConfChangeV2 : IntoVal ConfChangeV2.t :=
  {| to_val_def v :=
    struct.val_aux raftpb.ConfChangeV2 [
    "Transition" ::= #(ConfChangeV2.Transition' v);
    "Changes" ::= #(ConfChangeV2.Changes' v);
    "Context" ::= #(ConfChangeV2.Context' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_ConfChangeV2 : IntoValTyped ConfChangeV2.t raftpb.ConfChangeV2 :=
{|
  default_val := ConfChangeV2.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_ConfChangeV2_Transition : IntoValStructField "Transition" raftpb.ConfChangeV2 ConfChangeV2.Transition'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfChangeV2_Changes : IntoValStructField "Changes" raftpb.ConfChangeV2 ConfChangeV2.Changes'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ConfChangeV2_Context : IntoValStructField "Context" raftpb.ConfChangeV2 ConfChangeV2.Context'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfChangeV2 Transition' Changes' Context':
  PureWp True
    (struct.make #raftpb.ConfChangeV2 (alist_val [
      "Transition" ::= #Transition';
      "Changes" ::= #Changes';
      "Context" ::= #Context'
    ]))%struct
    #(ConfChangeV2.mk Transition' Changes' Context').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance ConfChangeV2_struct_fields_split dq l (v : ConfChangeV2.t) :
  StructFieldsSplit dq l v (
    "HTransition" ∷ l ↦s[raftpb.ConfChangeV2 :: "Transition"]{dq} v.(ConfChangeV2.Transition') ∗
    "HChanges" ∷ l ↦s[raftpb.ConfChangeV2 :: "Changes"]{dq} v.(ConfChangeV2.Changes') ∗
    "HContext" ∷ l ↦s[raftpb.ConfChangeV2 :: "Context"]{dq} v.(ConfChangeV2.Context')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (ConfChangeV2.Transition' v)) raftpb.ConfChangeV2 "Transition"%go.
  simpl_one_flatten_struct (# (ConfChangeV2.Changes' v)) raftpb.ConfChangeV2 "Changes"%go.

  solve_field_ref_f.
Qed.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined raftpb :=
{|
  is_pkg_defined := is_global_definitions raftpb var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

End names.
End raftpb.
