(* autogenerated from github.com/mit-pdos/perennial-examples/dynamic_dir *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.perennial_examples.alloc.
From Goose Require github_com.mit_pdos.perennial_examples.inode.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition MaxInodes : expr := disk.BlockSize `quot` #8.

Definition rootInode : expr := #0.

Definition Dir := struct.decl [
  "d" :: disk.Disk;
  "allocator" :: ptrT;
  "m" :: ptrT;
  "inodes" :: mapT ptrT
].

Definition Dir__mkHdr: val :=
  rec: "Dir__mkHdr" "d" :=
    let: "inode_addrs" := ref (zero_val (slice.T uint64T)) in
    MapIter (struct.loadF Dir "inodes" "d") (λ: "a" <>,
      "inode_addrs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "inode_addrs") "a"));;
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInt "enc" (slice.len (![slice.T uint64T] "inode_addrs"));;
    marshal.Enc__PutInts "enc" (![slice.T uint64T] "inode_addrs");;
    marshal.Enc__Finish "enc".

Definition Dir__writeHdr: val :=
  rec: "Dir__writeHdr" "d" :=
    let: "hdr" := Dir__mkHdr "d" in
    disk.Write rootInode "hdr";;
    #().

(* read header (which has addresses for inodes in use) *)
Definition parseHdr: val :=
  rec: "parseHdr" "b" :=
    let: "dec" := marshal.NewDec "b" in
    let: "num" := marshal.Dec__GetInt "dec" in
    marshal.Dec__GetInts "dec" "num".

Definition openInodes: val :=
  rec: "openInodes" "d" :=
    let: "inode_addrs" := parseHdr (disk.Read rootInode) in
    let: "inodes" := NewMap uint64T ptrT #() in
    ForSlice uint64T <> "a" "inode_addrs"
      (MapInsert "inodes" "a" (inode.Open "d" "a"));;
    "inodes".

Definition inodeUsedBlocks: val :=
  rec: "inodeUsedBlocks" "inodes" :=
    let: "used" := NewMap uint64T (struct.t alloc.unit) #() in
    MapIter "inodes" (λ: "a" "i",
      alloc.SetAdd "used" (SliceSingleton "a");;
      alloc.SetAdd "used" (inode.Inode__UsedBlocks "i"));;
    "used".

Definition Open: val :=
  rec: "Open" "d" "sz" :=
    let: "inodes" := openInodes "d" in
    let: "used" := inodeUsedBlocks "inodes" in
    let: "allocator" := alloc.New #1 ("sz" - #1) "used" in
    struct.new Dir [
      "d" ::= "d";
      "allocator" ::= "allocator";
      "m" ::= newMutex #();
      "inodes" ::= "inodes"
    ].

Definition Dir__Create: val :=
  rec: "Dir__Create" "d" :=
    let: ("a", "ok") := alloc.Allocator__Reserve (struct.loadF Dir "allocator" "d") in
    (if: (~ "ok")
    then (#0, #false)
    else
      let: "empty" := NewSlice byteT disk.BlockSize in
      disk.Write "a" "empty";;
      Mutex__Lock (struct.loadF Dir "m" "d");;
      MapInsert (struct.loadF Dir "inodes" "d") "a" (inode.Open (struct.loadF Dir "d" "d") "a");;
      Dir__writeHdr "d";;
      Mutex__Unlock (struct.loadF Dir "m" "d");;
      ("a", #true)).

Definition Dir__delete: val :=
  rec: "Dir__delete" "d" "ino" :=
    let: "i" := Fst (MapGet (struct.loadF Dir "inodes" "d") "ino") in
    MapDelete (struct.loadF Dir "inodes" "d") "ino";;
    Dir__writeHdr "d";;
    alloc.Allocator__Free (struct.loadF Dir "allocator" "d") "ino";;
    ForSlice uint64T <> "inode_a" (inode.Inode__UsedBlocks "i")
      (alloc.Allocator__Free (struct.loadF Dir "allocator" "d") "inode_a");;
    #().

Definition Dir__Delete: val :=
  rec: "Dir__Delete" "d" "ino" :=
    Mutex__Lock (struct.loadF Dir "m" "d");;
    Dir__delete "d" "ino";;
    Mutex__Unlock (struct.loadF Dir "m" "d");;
    #().

Definition Dir__Read: val :=
  rec: "Dir__Read" "d" "ino" "off" :=
    Mutex__Lock (struct.loadF Dir "m" "d");;
    let: "i" := Fst (MapGet (struct.loadF Dir "inodes" "d") "ino") in
    (if: "i" = #null
    then Panic "invalid inode"
    else #());;
    let: "b" := inode.Inode__Read "i" "off" in
    Mutex__Unlock (struct.loadF Dir "m" "d");;
    "b".

Definition Dir__Size: val :=
  rec: "Dir__Size" "d" "ino" :=
    Mutex__Lock (struct.loadF Dir "m" "d");;
    let: "i" := Fst (MapGet (struct.loadF Dir "inodes" "d") "ino") in
    (if: "i" = #null
    then Panic "invalid inode"
    else #());;
    let: "sz" := inode.Inode__Size "i" in
    Mutex__Unlock (struct.loadF Dir "m" "d");;
    "sz".

Definition Dir__Append: val :=
  rec: "Dir__Append" "d" "ino" "b" :=
    Mutex__Lock (struct.loadF Dir "m" "d");;
    let: "i" := Fst (MapGet (struct.loadF Dir "inodes" "d") "ino") in
    (if: "i" = #null
    then Panic "invalid inode"
    else #());;
    let: "ok" := inode.Inode__Append "i" "b" (struct.loadF Dir "allocator" "d") in
    Mutex__Unlock (struct.loadF Dir "m" "d");;
    "ok".
