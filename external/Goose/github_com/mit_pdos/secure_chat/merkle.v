(* autogenerated from github.com/mit-pdos/secure-chat/merkle *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.secure_chat.cryptoffi.
From Goose Require github_com.mit_pdos.secure_chat.cryptoutil.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition errorTy: ty := boolT.

Definition ProofTy: ty := boolT.

Definition errNone : expr := #false.

Definition errSome : expr := #true.

Definition numChildren : expr := #256.

Definition emptyNodeId : expr := #(U8 0).

Definition leafNodeId : expr := #(U8 1).

Definition interiorNodeId : expr := #(U8 2).

Definition NonmembProofTy : expr := #false.

Definition MembProofTy : expr := #true.

Definition Id: ty := slice.T byteT.

Definition Val: ty := slice.T byteT.

Definition node := struct.decl [
  "val" :: Val;
  "hash" :: slice.T byteT;
  "children" :: slice.T ptrT
].

(* getHash getter to support hashes of empty (nil) nodes. *)
Definition node__getHash: val :=
  rec: "node__getHash" "n" :=
    (if: "n" = #null
    then cryptoffi.Hash (SliceSingleton emptyNodeId)
    else struct.loadF node "hash" "n").

Definition node__deepCopy: val :=
  rec: "node__deepCopy" "n" :=
    (if: "n" = #null
    then slice.nil
    else
      let: "n2" := ref_to ptrT (struct.new node [
      ]) in
      struct.storeF node "val" (![ptrT] "n2") (std.BytesClone (struct.loadF node "val" "n"));;
      struct.storeF node "hash" (![ptrT] "n2") (std.BytesClone (struct.loadF node "hash" "n"));;
      let: "children" := NewSlice ptrT (slice.len (struct.loadF node "children" "n")) in
      ForSlice ptrT "i" "c" (struct.loadF node "children" "n")
        (SliceSet ptrT "children" "i" ("node__deepCopy" "c"));;
      struct.storeF node "children" (![ptrT] "n2") "children";;
      ![ptrT] "n2").

Definition node__updateLeafHash: val :=
  rec: "node__updateLeafHash" "n" :=
    let: "h" := ref (zero_val (slice.T byteT)) in
    cryptoutil.HasherWrite "h" (struct.loadF node "val" "n");;
    cryptoutil.HasherWrite "h" (SliceSingleton leafNodeId);;
    struct.storeF node "hash" "n" (cryptoutil.HasherSum (![slice.T byteT] "h") slice.nil);;
    #().

(* Assumes recursive child hashes are already up-to-date. *)
Definition node__updateInteriorHash: val :=
  rec: "node__updateInteriorHash" "n" :=
    let: "h" := ref (zero_val (slice.T byteT)) in
    ForSlice ptrT <> "n" (struct.loadF node "children" "n")
      (cryptoutil.HasherWrite "h" (node__getHash "n"));;
    cryptoutil.HasherWrite "h" (SliceSingleton interiorNodeId);;
    struct.storeF node "hash" "n" (cryptoutil.HasherSum (![slice.T byteT] "h") slice.nil);;
    #().

(* This node doesn't satisfy the invariant for any logical node.
   It'll be specialized after adding it to the tree. *)
Definition newGenericNode: val :=
  rec: "newGenericNode" <> :=
    let: "c" := NewSlice ptrT numChildren in
    struct.new node [
      "val" ::= slice.nil;
      "hash" ::= slice.nil;
      "children" ::= "c"
    ].

Definition Digest: ty := slice.T byteT.

(* General proof object.
   Binds an id down the tree to a particular node hash. *)
Definition pathProof := struct.decl [
  "id" :: Id;
  "NodeHash" :: slice.T byteT;
  "Digest" :: Digest;
  "ChildHashes" :: slice.T (slice.T (slice.T byteT))
].

Definition Proof: ty := slice.T (slice.T (slice.T byteT)).

Definition isValidHashSl: val :=
  rec: "isValidHashSl" "data" :=
    let: "ok" := ref_to boolT #true in
    ForSlice (slice.T byteT) <> "hash" "data"
      ((if: (slice.len "hash") ≠ cryptoffi.HashLen
      then "ok" <-[boolT] #false
      else #()));;
    ![boolT] "ok".

Definition pathProof__check: val :=
  rec: "pathProof__check" "p" :=
    let: "err" := ref_to boolT errNone in
    let: "currHash" := ref_to (slice.T byteT) (struct.loadF pathProof "NodeHash" "p") in
    let: "proofLen" := slice.len (struct.loadF pathProof "ChildHashes" "p") in
    let: "loopIdx" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "loopIdx") < "proofLen"); (λ: <>, "loopIdx" <-[uint64T] ((![uint64T] "loopIdx") + #1)) := λ: <>,
      let: "pathIdx" := ("proofLen" - #1) - (![uint64T] "loopIdx") in
      let: "children" := SliceGet (slice.T (slice.T byteT)) (struct.loadF pathProof "ChildHashes" "p") "pathIdx" in
      (if: (slice.len "children") ≠ (numChildren - #1)
      then
        "err" <-[boolT] errSome;;
        Continue
      else
        (if: (~ (isValidHashSl "children"))
        then
          "err" <-[boolT] errSome;;
          Continue
        else
          let: "pos" := to_u64 (SliceGet byteT (struct.loadF pathProof "id" "p") "pathIdx") in
          let: "before" := SliceTake "children" "pos" in
          let: "after" := SliceSkip (slice.T byteT) "children" "pos" in
          let: "hr" := ref (zero_val (slice.T byteT)) in
          cryptoutil.HasherWriteSl "hr" "before";;
          cryptoutil.HasherWrite "hr" (![slice.T byteT] "currHash");;
          cryptoutil.HasherWriteSl "hr" "after";;
          cryptoutil.HasherWrite "hr" (SliceSingleton interiorNodeId);;
          "currHash" <-[slice.T byteT] (cryptoutil.HasherSum (![slice.T byteT] "hr") slice.nil);;
          Continue)));;
    (if: ![boolT] "err"
    then errSome
    else
      (if: (~ (std.BytesEqual (![slice.T byteT] "currHash") (struct.loadF pathProof "Digest" "p")))
      then errSome
      else errNone)).

Definition getLeafNodeHash: val :=
  rec: "getLeafNodeHash" "val" :=
    let: "hr" := ref (zero_val (slice.T byteT)) in
    cryptoutil.HasherWrite "hr" "val";;
    cryptoutil.HasherWrite "hr" (SliceSingleton leafNodeId);;
    cryptoutil.HasherSum (![slice.T byteT] "hr") slice.nil.

Definition getEmptyNodeHash: val :=
  rec: "getEmptyNodeHash" <> :=
    cryptoffi.Hash (SliceSingleton emptyNodeId).

Definition CheckProof: val :=
  rec: "CheckProof" "proofTy" "proof" "id" "val" "digest" :=
    (if: (slice.len "proof") > cryptoffi.HashLen
    then errSome
    else
      (if: (slice.len "id") < (slice.len "proof")
      then errSome
      else
        let: "idPref" := SliceTake "id" (slice.len "proof") in
        let: "nodeHash" := ref (zero_val (slice.T byteT)) in
        (if: "proofTy"
        then "nodeHash" <-[slice.T byteT] (getLeafNodeHash "val")
        else "nodeHash" <-[slice.T byteT] (getEmptyNodeHash #()));;
        let: "pathProof" := struct.new pathProof [
          "id" ::= "idPref";
          "NodeHash" ::= ![slice.T byteT] "nodeHash";
          "Digest" ::= "digest";
          "ChildHashes" ::= "proof"
        ] in
        pathProof__check "pathProof")).

(* Having a separate Tree type makes the API more clear compared to if it
   was just a Node. *)
Definition Tree := struct.decl [
  "root" :: ptrT
].

Definition Tree__DeepCopy: val :=
  rec: "Tree__DeepCopy" "t" :=
    struct.new Tree [
      "root" ::= node__deepCopy (struct.loadF Tree "root" "t")
    ].

Definition Tree__Digest: val :=
  rec: "Tree__Digest" "t" :=
    node__getHash (struct.loadF Tree "root" "t").

Definition appendNode2D: val :=
  rec: "appendNode2D" "dst" "src" :=
    ForSlice ptrT <> "sl" "src"
      ("dst" <-[slice.T (slice.T byteT)] (SliceAppend (slice.T byteT) (![slice.T (slice.T byteT)] "dst") (std.BytesClone (node__getHash "sl"))));;
    #().

Definition getChildHashes: val :=
  rec: "getChildHashes" "nodePath" "id" :=
    let: "childHashes" := NewSlice (slice.T (slice.T byteT)) ((slice.len "nodePath") - #1) in
    let: "pathIdx" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "pathIdx") < ((slice.len "nodePath") - #1)); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
      let: "children" := struct.loadF node "children" (SliceGet ptrT "nodePath" (![uint64T] "pathIdx")) in
      let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
      let: "proofChildren" := ref (zero_val (slice.T (slice.T byteT))) in
      appendNode2D "proofChildren" (SliceTake "children" "pos");;
      appendNode2D "proofChildren" (SliceSkip ptrT "children" ("pos" + #(U8 1)));;
      SliceSet (slice.T (slice.T byteT)) "childHashes" (![uint64T] "pathIdx") (![slice.T (slice.T byteT)] "proofChildren");;
      Continue);;
    "childHashes".

(* Get the maximal path corresponding to Id.
   If the full path to a leaf node doesn't exist,
   return the partial path that ends in an empty node. *)
Definition Tree__getPath: val :=
  rec: "Tree__getPath" "t" "id" :=
    let: "nodePath" := ref (zero_val (slice.T ptrT)) in
    "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (struct.loadF Tree "root" "t"));;
    (if: (struct.loadF Tree "root" "t") = #null
    then ![slice.T ptrT] "nodePath"
    else
      let: "stop" := ref_to boolT #false in
      let: "pathIdx" := ref_to uint64T #0 in
      (for: (λ: <>, ((![uint64T] "pathIdx") < cryptoffi.HashLen) && (~ (![boolT] "stop"))); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
        let: "currNode" := SliceGet ptrT (![slice.T ptrT] "nodePath") (![uint64T] "pathIdx") in
        let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
        let: "nextNode" := SliceGet ptrT (struct.loadF node "children" "currNode") "pos" in
        "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") "nextNode");;
        (if: "nextNode" = #null
        then
          "stop" <-[boolT] #true;;
          Continue
        else Continue));;
      ![slice.T ptrT] "nodePath").

Definition Tree__getPathAddNodes: val :=
  rec: "Tree__getPathAddNodes" "t" "id" :=
    (if: (struct.loadF Tree "root" "t") = #null
    then struct.storeF Tree "root" "t" (newGenericNode #())
    else #());;
    let: "nodePath" := ref (zero_val (slice.T ptrT)) in
    "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (struct.loadF Tree "root" "t"));;
    let: "pathIdx" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "pathIdx") < cryptoffi.HashLen); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
      let: "currNode" := SliceGet ptrT (![slice.T ptrT] "nodePath") (![uint64T] "pathIdx") in
      let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
      (if: (SliceGet ptrT (struct.loadF node "children" "currNode") "pos") = #null
      then SliceSet ptrT (struct.loadF node "children" "currNode") "pos" (newGenericNode #())
      else #());;
      "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (SliceGet ptrT (struct.loadF node "children" "currNode") "pos"));;
      Continue);;
    ![slice.T ptrT] "nodePath".

Definition Tree__Put: val :=
  rec: "Tree__Put" "t" "id" "val" :=
    (if: (slice.len "id") ≠ cryptoffi.HashLen
    then (slice.nil, slice.nil, errSome)
    else
      let: "nodePath" := Tree__getPathAddNodes "t" "id" in
      struct.storeF node "val" (SliceGet ptrT "nodePath" cryptoffi.HashLen) "val";;
      node__updateLeafHash (SliceGet ptrT "nodePath" cryptoffi.HashLen);;
      let: "pathIdx" := ref_to uint64T cryptoffi.HashLen in
      (for: (λ: <>, (![uint64T] "pathIdx") ≥ #1); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") - #1)) := λ: <>,
        node__updateInteriorHash (SliceGet ptrT "nodePath" ((![uint64T] "pathIdx") - #1));;
        Continue);;
      let: "digest" := std.BytesClone (node__getHash (SliceGet ptrT "nodePath" #0)) in
      let: "proof" := getChildHashes "nodePath" "id" in
      ("digest", "proof", errNone)).

(* Goose doesn't support returning more than 4 vars. *)
Definition GetReply := struct.decl [
  "Val" :: Val;
  "Digest" :: Digest;
  "ProofTy" :: ProofTy;
  "Proof" :: Proof;
  "Error" :: errorTy
].

(* Return ProofTy vs. having sep funcs bc regardless, would want a proof. *)
Definition Tree__Get: val :=
  rec: "Tree__Get" "t" "id" :=
    let: "errReply" := struct.new GetReply [
    ] in
    (if: (slice.len "id") ≠ cryptoffi.HashLen
    then
      struct.storeF GetReply "Error" "errReply" errSome;;
      "errReply"
    else
      let: "nodePath" := Tree__getPath "t" "id" in
      let: "lastNode" := SliceGet ptrT "nodePath" ((slice.len "nodePath") - #1) in
      let: "digest" := std.BytesClone (node__getHash (SliceGet ptrT "nodePath" #0)) in
      let: "proof" := getChildHashes "nodePath" "id" in
      (if: "lastNode" = #null
      then
        struct.new GetReply [
          "Val" ::= slice.nil;
          "Digest" ::= "digest";
          "ProofTy" ::= NonmembProofTy;
          "Proof" ::= "proof";
          "Error" ::= errNone
        ]
      else
        let: "val" := std.BytesClone (struct.loadF node "val" "lastNode") in
        struct.new GetReply [
          "Val" ::= "val";
          "Digest" ::= "digest";
          "ProofTy" ::= MembProofTy;
          "Proof" ::= "proof";
          "Error" ::= errNone
        ])).

End code.
