(* autogenerated from github.com/mit-pdos/goose-nfsd/txn *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.goose_nfsd.addr.
From Goose Require github_com.mit_pdos.goose_nfsd.buf.
From Goose Require github_com.mit_pdos.goose_nfsd.common.
From Goose Require github_com.mit_pdos.goose_nfsd.util.
From Goose Require github_com.mit_pdos.goose_nfsd.wal.

(* Txn mediates access to the transaction system.

   There is only one Txn object. *)
Definition Txn := struct.decl [
  "mu" :: lockRefT;
  "log" :: struct.ptrT wal.Walog;
  "pos" :: wal.LogPosition
].

(* MkTxn recovers the txn system (or initializes from an all-zero disk). *)
Definition MkTxn: val :=
  rec: "MkTxn" "d" :=
    let: "txn" := struct.new Txn [
      "mu" ::= lock.new #();
      "log" ::= wal.MkLog "d";
      "pos" ::= #0
    ] in
    "txn".

(* Read a disk object into buf *)
Definition Txn__Load: val :=
  rec: "Txn__Load" "txn" "addr" "sz" :=
    let: "blk" := wal.Walog__Read (struct.loadF Txn "log" "txn") (struct.get addr.Addr "Blkno" "addr") in
    let: "b" := buf.MkBufLoad "addr" "sz" "blk" in
    "b".

(* Installs the txn's bufs into their blocks and returns the blocks.
   A buf may only partially update a disk block and several bufs may
   apply to the same disk block. Assume caller holds commit lock. *)
Definition Txn__installBufsMap: val :=
  rec: "Txn__installBufsMap" "txn" "bufs" :=
    let: "blks" := NewMap (slice.T byteT) in
    ForSlice (refT (struct.t buf.Buf)) <> "b" "bufs"
      (if: (struct.loadF buf.Buf "Sz" "b" = common.NBITBLOCK)
      then MapInsert "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) (struct.loadF buf.Buf "Data" "b")
      else
        let: "blk" := ref (zero_val (slice.T byteT)) in
        let: ("mapblk", "ok") := MapGet "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) in
        (if: "ok"
        then "blk" <-[slice.T byteT] "mapblk"
        else
          "blk" <-[slice.T byteT] wal.Walog__Read (struct.loadF Txn "log" "txn") (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b"));;
          MapInsert "blks" (struct.get addr.Addr "Blkno" (struct.loadF buf.Buf "Addr" "b")) (![slice.T byteT] "blk"));;
        buf.Buf__Install "b" (![slice.T byteT] "blk"));;
    "blks".

Definition Txn__installBufs: val :=
  rec: "Txn__installBufs" "txn" "bufs" :=
    let: "blks" := ref (zero_val (slice.T (struct.t wal.Update))) in
    let: "bufmap" := Txn__installBufsMap "txn" "bufs" in
    MapIter "bufmap" (λ: "blkno" "data",
      "blks" <-[slice.T (struct.t wal.Update)] SliceAppend (struct.t wal.Update) (![slice.T (struct.t wal.Update)] "blks") (wal.MkBlockData "blkno" "data"));;
    ![slice.T (struct.t wal.Update)] "blks".

(* Acquires the commit log, installs the txn's buffers into their
   blocks, and appends the blocks to the in-memory log. *)
Definition Txn__doCommit: val :=
  rec: "Txn__doCommit" "txn" "bufs" :=
    lock.acquire (struct.loadF Txn "mu" "txn");;
    let: "blks" := Txn__installBufs "txn" "bufs" in
    util.DPrintf #3 (#(str"doCommit: %v bufs
    ")) #();;
    let: ("n", "ok") := wal.Walog__MemAppend (struct.loadF Txn "log" "txn") "blks" in
    struct.storeF Txn "pos" "txn" "n";;
    lock.release (struct.loadF Txn "mu" "txn");;
    ("n", "ok").

(* Commit dirty bufs of the transaction into the log, and perhaps wait. *)
Definition Txn__CommitWait: val :=
  rec: "Txn__CommitWait" "txn" "bufs" "wait" :=
    let: "commit" := ref_to boolT #true in
    (if: slice.len "bufs" > #0
    then
      let: ("n", "ok") := Txn__doCommit "txn" "bufs" in
      (if: ~ "ok"
      then
        util.DPrintf #10 (#(str"memappend failed; log is too small
        ")) #();;
        "commit" <-[boolT] #false
      else
        (if: "wait"
        then wal.Walog__Flush (struct.loadF Txn "log" "txn") "n"
        else #()))
    else
      util.DPrintf #5 (#(str"commit read-only trans
      ")) #());;
    ![boolT] "commit".

(* NOTE: this is coarse-grained and unattached to the transaction ID *)
Definition Txn__Flush: val :=
  rec: "Txn__Flush" "txn" :=
    lock.acquire (struct.loadF Txn "mu" "txn");;
    let: "pos" := struct.loadF Txn "pos" "txn" in
    lock.release (struct.loadF Txn "mu" "txn");;
    wal.Walog__Flush (struct.loadF Txn "log" "txn") "pos";;
    #true.

(* LogSz returns 511 (the size of the wal log) *)
Definition Txn__LogSz: val :=
  rec: "Txn__LogSz" "txn" :=
    wal.LOGSZ.

Definition Txn__Shutdown: val :=
  rec: "Txn__Shutdown" "txn" :=
    wal.Walog__Shutdown (struct.loadF Txn "log" "txn").
