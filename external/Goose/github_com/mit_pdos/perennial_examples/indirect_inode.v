(* autogenerated from github.com/mit-pdos/perennial-examples/indirect_inode *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.perennial_examples.alloc.
From Goose Require github_com.tchajed.marshal.

Definition MaxBlocks : expr := #500 + #10 * #512.

Definition maxDirect : expr := #500.

Definition maxIndirect : expr := #10.

Definition indirectNumBlocks : expr := #512.

Module Inode.
  Definition S := struct.decl [
    "d" :: disk.Disk;
    "m" :: lockRefT;
    "addr" :: uint64T;
    "size" :: uint64T;
    "direct" :: slice.T uint64T;
    "indirect" :: slice.T uint64T
  ].
End Inode.

Definition min: val :=
  rec: "min" "a" "b" :=
    (if: "a" ≤ "b"
    then "a"
    else "b").

Definition Open: val :=
  rec: "Open" "d" "addr" :=
    let: "b" := disk.Read "addr" in
    let: "dec" := marshal.NewDec "b" in
    let: "size" := marshal.Dec__GetInt "dec" in
    let: "direct" := marshal.Dec__GetInts "dec" maxDirect in
    let: "indirect" := marshal.Dec__GetInts "dec" maxIndirect in
    let: "numIndirect" := marshal.Dec__GetInt "dec" in
    let: "numDirect" := min "size" maxDirect in
    struct.new Inode.S [
      "d" ::= "d";
      "m" ::= lock.new #();
      "size" ::= "size";
      "addr" ::= "addr";
      "direct" ::= SliceTake "direct" "numDirect";
      "indirect" ::= SliceTake "indirect" "numIndirect"
    ].

Definition readIndirect: val :=
  rec: "readIndirect" "d" "a" :=
    let: "b" := disk.Read "a" in
    let: "dec" := marshal.NewDec "b" in
    marshal.Dec__GetInts "dec" indirectNumBlocks.

Definition prepIndirect: val :=
  rec: "prepIndirect" "addrs" :=
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInts "enc" "addrs";;
    marshal.Enc__Finish "enc".

Definition Inode__UsedBlocks: val :=
  rec: "Inode__UsedBlocks" "i" :=
    let: "addrs" := ref (zero_val (slice.T uint64T)) in
    "addrs" <-[slice.T uint64T] NewSlice uint64T #0;;
    let: "direct" := struct.loadF Inode.S "direct" "i" in
    let: "indirect" := struct.loadF Inode.S "indirect" "i" in
    ForSlice uint64T <> "a" "direct"
      ("addrs" <-[slice.T uint64T] SliceAppend uint64T (![slice.T uint64T] "addrs") "a");;
    ForSlice uint64T <> "blkAddr" "indirect"
      ("addrs" <-[slice.T uint64T] SliceAppend uint64T (![slice.T uint64T] "addrs") "blkAddr");;
    ForSlice uint64T <> "blkAddr" "indirect"
      ("addrs" <-[slice.T uint64T] SliceAppendSlice uint64T (![slice.T uint64T] "addrs") (readIndirect (struct.loadF Inode.S "d" "i") "blkAddr"));;
    ![slice.T uint64T] "addrs".

Definition indNum: val :=
  rec: "indNum" "off" :=
    ("off" - maxDirect) `quot` indirectNumBlocks.

Definition indOff: val :=
  rec: "indOff" "off" :=
    ("off" - maxDirect) `rem` indirectNumBlocks.

Definition Inode__Read: val :=
  rec: "Inode__Read" "i" "off" :=
    lock.acquire (struct.loadF Inode.S "m" "i");;
    (if: "off" ≥ struct.loadF Inode.S "size" "i"
    then
      lock.release (struct.loadF Inode.S "m" "i");;
      slice.nil
    else
      (if: "off" < maxDirect
      then
        let: "a" := SliceGet uint64T (struct.loadF Inode.S "direct" "i") "off" in
        let: "b" := disk.Read "a" in
        lock.release (struct.loadF Inode.S "m" "i");;
        "b"
      else
        let: "addrs" := readIndirect (struct.loadF Inode.S "d" "i") (SliceGet uint64T (struct.loadF Inode.S "indirect" "i") (indNum "off")) in
        let: "b" := disk.Read (SliceGet uint64T "addrs" (indOff "off")) in
        lock.release (struct.loadF Inode.S "m" "i");;
        "b")).

Definition Inode__Size: val :=
  rec: "Inode__Size" "i" :=
    lock.acquire (struct.loadF Inode.S "m" "i");;
    let: "sz" := struct.loadF Inode.S "size" "i" in
    lock.release (struct.loadF Inode.S "m" "i");;
    "sz".

Definition padInts: val :=
  rec: "padInts" "enc" "num" :=
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < "num"); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      marshal.Enc__PutInt "enc" #0;;
      Continue).

Definition Inode__mkHdr: val :=
  rec: "Inode__mkHdr" "i" :=
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInt "enc" (struct.loadF Inode.S "size" "i");;
    marshal.Enc__PutInts "enc" (struct.loadF Inode.S "direct" "i");;
    padInts "enc" (maxDirect - slice.len (struct.loadF Inode.S "direct" "i"));;
    marshal.Enc__PutInts "enc" (struct.loadF Inode.S "indirect" "i");;
    padInts "enc" (maxIndirect - slice.len (struct.loadF Inode.S "indirect" "i"));;
    marshal.Enc__PutInt "enc" (slice.len (struct.loadF Inode.S "indirect" "i"));;
    let: "hdr" := marshal.Enc__Finish "enc" in
    "hdr".

Definition Inode__inSize: val :=
  rec: "Inode__inSize" "i" :=
    let: "hdr" := Inode__mkHdr "i" in
    disk.Write (struct.loadF Inode.S "addr" "i") "hdr".

(* checkTotalSize determines that the inode is not already at maximum size

   Requires the lock to be held. *)
Definition Inode__checkTotalSize: val :=
  rec: "Inode__checkTotalSize" "i" :=
    (if: struct.loadF Inode.S "size" "i" ≥ MaxBlocks
    then #false
    else #true).

(* appendDirect adds address a (and whatever data is stored there) to the inode

   Requires the lock to be held.

   In this simple design with only direct blocks, appending never requires
   internal allocation, so we don't take an allocator.

   This method can only fail due to running out of space in the inode. In this
   case, append returns ownership of the allocated block. *)
Definition Inode__appendDirect: val :=
  rec: "Inode__appendDirect" "i" "a" :=
    (if: struct.loadF Inode.S "size" "i" < maxDirect
    then
      struct.storeF Inode.S "direct" "i" (SliceAppend uint64T (struct.loadF Inode.S "direct" "i") "a");;
      struct.storeF Inode.S "size" "i" (struct.loadF Inode.S "size" "i" + #1);;
      let: "hdr" := Inode__mkHdr "i" in
      disk.Write (struct.loadF Inode.S "addr" "i") "hdr";;
      #true
    else #false).

(* appendIndirect adds address a (and whatever data is stored there) to the inode

   Requires the lock to be held.

   In this simple design with only direct blocks, appending never requires
   internal allocation, so we don't take an allocator.

   This method can only fail due to running out of space in the inode. In this
   case, append returns ownership of the allocated block. *)
Definition Inode__appendIndirect: val :=
  rec: "Inode__appendIndirect" "i" "a" :=
    (if: indNum (struct.loadF Inode.S "size" "i") ≥ slice.len (struct.loadF Inode.S "indirect" "i")
    then #false
    else
      let: "indAddr" := SliceGet uint64T (struct.loadF Inode.S "indirect" "i") (indNum (struct.loadF Inode.S "size" "i")) in
      let: "addrs" := readIndirect (struct.loadF Inode.S "d" "i") "indAddr" in
      SliceSet uint64T "addrs" (indOff (struct.loadF Inode.S "size" "i")) "a";;
      Inode__writeIndirect "i" "indAddr" "addrs";;
      #true).

(* writeIndirect preps the block of addrs and
   adds writes the new indirect block to disk

   Requires the lock to be held. *)
Definition Inode__writeIndirect: val :=
  rec: "Inode__writeIndirect" "i" "indAddr" "addrs" :=
    let: "diskBlk" := prepIndirect "addrs" in
    disk.Write "indAddr" "diskBlk";;
    struct.storeF Inode.S "size" "i" (struct.loadF Inode.S "size" "i" + #1);;
    let: "hdr" := Inode__mkHdr "i" in
    disk.Write (struct.loadF Inode.S "addr" "i") "hdr".

(* Append adds a block to the inode.

   Takes ownership of the disk at a on success.

   Returns false on failure (if the allocator or inode are out of space) *)
Definition Inode__Append: val :=
  rec: "Inode__Append" "i" "b" "allocator" :=
    lock.acquire (struct.loadF Inode.S "m" "i");;
    let: "ok" := Inode__checkTotalSize "i" in
    (if: ~ "ok"
    then
      lock.release (struct.loadF Inode.S "m" "i");;
      #false
    else
      let: ("a", "ok2") := alloc.Allocator__Reserve "allocator" in
      (if: ~ "ok2"
      then
        lock.release (struct.loadF Inode.S "m" "i");;
        #false
      else
        disk.Write "a" "b";;
        let: "ok3" := Inode__appendDirect "i" "a" in
        (if: "ok3"
        then
          lock.release (struct.loadF Inode.S "m" "i");;
          #true
        else
          let: "ok4" := Inode__appendIndirect "i" "a" in
          (if: "ok4"
          then
            lock.release (struct.loadF Inode.S "m" "i");;
            #true
          else
            let: ("indAddr", "ok") := alloc.Allocator__Reserve "allocator" in
            (if: ~ "ok"
            then
              lock.release (struct.loadF Inode.S "m" "i");;
              alloc.Allocator__Free "allocator" "a";;
              #false
            else
              struct.storeF Inode.S "indirect" "i" (SliceAppend uint64T (struct.loadF Inode.S "indirect" "i") "indAddr");;
              Inode__writeIndirect "i" "indAddr" (SliceSingleton "a");;
              lock.release (struct.loadF Inode.S "m" "i");;
              #true))))).

(* Give a block to the inode for metadata purposes.
   Precondition: Block at addr a should be zeroed

   Returns true if the block was consumed. *)
Definition Inode__Alloc: val :=
  rec: "Inode__Alloc" "i" "a" :=
    lock.acquire (struct.loadF Inode.S "m" "i");;
    (if: slice.len (struct.loadF Inode.S "indirect" "i") ≥ maxIndirect
    then
      lock.release (struct.loadF Inode.S "m" "i");;
      #false
    else
      struct.storeF Inode.S "indirect" "i" (SliceAppend uint64T (struct.loadF Inode.S "indirect" "i") "a");;
      let: "hdr" := Inode__mkHdr "i" in
      disk.Write (struct.loadF Inode.S "addr" "i") "hdr";;
      lock.release (struct.loadF Inode.S "m" "i");;
      #true).
