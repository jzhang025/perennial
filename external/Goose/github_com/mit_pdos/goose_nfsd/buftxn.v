(* autogenerated from github.com/mit-pdos/goose-nfsd/buftxn *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.goose_nfsd.addr.
From Goose Require github_com.mit_pdos.goose_nfsd.buf.
From Goose Require github_com.mit_pdos.goose_nfsd.txn.
From Goose Require github_com.mit_pdos.goose_nfsd.util.

(* buftxn manages "buffer"-based transactions

   The caller uses this interface by creating a BufTxn, reading/writing within
   the transaction, and finally committing the buffered transaction.

   Note that while the API has reads and writes, these are not the usual database
   read/write transactions. Only writes are made atomic and visible atomically;
   reads are cached on first read. Thus to use this library the file
   system in practice locks (sub-block) objects before running a transaction.
   This is necessary so that loaded objects are read from a consistent view.

   Transactions support asynchronous durability by setting wait=false in
   CommitWait. An asynchronous transaction is made visible atomically to other
   threads, including across crashes, but if the system crashes a committed
   asynchronous transaction can be lost. To guarantee that a particular
   transaction is durable, call ( *Buftxn) Flush (which flushes all transactions).

   Objects have sizes. Implicit in the code is that there is a static "schema"
   that determines the disk layout: each block has objects of a particular size,
   and all sizes used fit an integer number of objects in a block. This schema
   guarantees that objects never overlap, as long as operations involving an
   addr.Addr use the correct size for that block number.

   The file system realizes this schema fairly simply, since the disk is simply
   partitioned into inodes, data blocks, and bitmap allocators for each (sized
   appropriately), all allocated statically. *)

Definition BufTxn := struct.decl [
  "txn" :: struct.ptrT txn.Txn;
  "bufs" :: struct.ptrT buf.BufMap
].

(* Start a local transaction with no writes from a global Txn manager. *)
Definition Begin: val :=
  rec: "Begin" "txn" :=
    let: "trans" := struct.new BufTxn [
      "txn" ::= "txn";
      "bufs" ::= buf.MkBufMap #()
    ] in
    util.DPrintf #3 (#(str"Begin: %v
    ")) #();;
    "trans".

Definition BufTxn__ReadBuf: val :=
  rec: "BufTxn__ReadBuf" "buftxn" "addr" "sz" :=
    let: "b" := buf.BufMap__Lookup (struct.loadF BufTxn "bufs" "buftxn") "addr" in
    (if: ("b" = #null)
    then
      let: "buf" := txn.Txn__Load (struct.loadF BufTxn "txn" "buftxn") "addr" "sz" in
      buf.BufMap__Insert (struct.loadF BufTxn "bufs" "buftxn") "buf";;
      buf.BufMap__Lookup (struct.loadF BufTxn "bufs" "buftxn") "addr"
    else "b").

(* OverWrite writes an object to addr *)
Definition BufTxn__OverWrite: val :=
  rec: "BufTxn__OverWrite" "buftxn" "addr" "sz" "data" :=
    let: "b" := ref_to (refT (struct.t buf.Buf)) (buf.BufMap__Lookup (struct.loadF BufTxn "bufs" "buftxn") "addr") in
    (if: (![refT (struct.t buf.Buf)] "b" = #null)
    then
      "b" <-[refT (struct.t buf.Buf)] buf.MkBuf "addr" "sz" "data";;
      buf.Buf__SetDirty (![refT (struct.t buf.Buf)] "b");;
      buf.BufMap__Insert (struct.loadF BufTxn "bufs" "buftxn") (![refT (struct.t buf.Buf)] "b")
    else
      (if: "sz" ≠ struct.loadF buf.Buf "Sz" (![refT (struct.t buf.Buf)] "b")
      then
        Panic "overwrite";;
        #()
      else #());;
      struct.storeF buf.Buf "Data" (![refT (struct.t buf.Buf)] "b") "data";;
      buf.Buf__SetDirty (![refT (struct.t buf.Buf)] "b")).

(* NDirty reports an upper bound on the size of this transaction when committed.

   The caller cannot rely on any particular properties of this function for
   safety. *)
Definition BufTxn__NDirty: val :=
  rec: "BufTxn__NDirty" "buftxn" :=
    buf.BufMap__Ndirty (struct.loadF BufTxn "bufs" "buftxn").

(* LogSz returns 511 *)
Definition BufTxn__LogSz: val :=
  rec: "BufTxn__LogSz" "buftxn" :=
    txn.Txn__LogSz (struct.loadF BufTxn "txn" "buftxn").

(* LogSzBytes returns 511*4096 *)
Definition BufTxn__LogSzBytes: val :=
  rec: "BufTxn__LogSzBytes" "buftxn" :=
    txn.Txn__LogSz (struct.loadF BufTxn "txn" "buftxn") * disk.BlockSize.

(* CommitWait commits the writes in the transaction to disk.

   If CommitWait returns false, the transaction failed and had no logical effect.
   This can happen, for example, if the transaction is too big to fit in the
   on-disk journal.

   wait=true is a synchronous commit, which is durable as soon as CommitWait
   returns.

   wait=false is an asynchronous commit, which can be made durable later with
   Flush. *)
Definition BufTxn__CommitWait: val :=
  rec: "BufTxn__CommitWait" "buftxn" "wait" :=
    util.DPrintf #3 (#(str"Commit %p w %v
    ")) #();;
    let: "ok" := txn.Txn__CommitWait (struct.loadF BufTxn "txn" "buftxn") (buf.BufMap__DirtyBufs (struct.loadF BufTxn "bufs" "buftxn")) "wait" in
    "ok".

Definition BufTxn__Flush: val :=
  rec: "BufTxn__Flush" "buftxn" :=
    let: "ok" := txn.Txn__Flush (struct.loadF BufTxn "txn" "buftxn") in
    "ok".
