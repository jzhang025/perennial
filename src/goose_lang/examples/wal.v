(* autogenerated from awol *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* 10 is completely arbitrary *)
Definition MaxTxnWrites : expr := #10.

Definition logLength : expr := #1 + #2 * MaxTxnWrites.

Definition Log := struct.decl [
  "d" :: disk.Disk;
  "l" :: lockRefT;
  "cache" :: mapT disk.blockT;
  "length" :: refT uint64T
].

Definition intToBlock: val :=
  rec: "intToBlock" "a" :=
    let: "b" := NewSlice byteT disk.BlockSize in
    UInt64Put "b" "a";;
    "b".

Definition blockToInt: val :=
  rec: "blockToInt" "v" :=
    let: "a" := UInt64Get "v" in
    "a".

(* New initializes a fresh log *)
Definition New: val :=
  rec: "New" <> :=
    let: "d" := disk.Get #() in
    let: "diskSize" := disk.Size #() in
    (if: "diskSize" ≤ logLength
    then
      Panic ("disk is too small to host log");;
      #()
    else #());;
    let: "cache" := NewMap disk.blockT in
    let: "header" := intToBlock #0 in
    disk.Write #0 "header";;
    let: "lengthPtr" := ref (zero_val uint64T) in
    "lengthPtr" <-[uint64T] #0;;
    let: "l" := lock.new #() in
    struct.mk Log [
      "d" ::= "d";
      "cache" ::= "cache";
      "length" ::= "lengthPtr";
      "l" ::= "l"
    ].

Definition Log__lock: val :=
  rec: "Log__lock" "l" :=
    lock.acquire (struct.get Log "l" "l").

Definition Log__unlock: val :=
  rec: "Log__unlock" "l" :=
    lock.release (struct.get Log "l" "l").

(* BeginTxn allocates space for a new transaction in the log.

   Returns true if the allocation succeeded. *)
Definition Log__BeginTxn: val :=
  rec: "Log__BeginTxn" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log "length" "l") in
    (if: ("length" = #0)
    then
      Log__unlock "l";;
      #true
    else
      Log__unlock "l";;
      #false).

(* Read from the logical disk.

   Reads must go through the log to return committed but un-applied writes. *)
Definition Log__Read: val :=
  rec: "Log__Read" "l" "a" :=
    Log__lock "l";;
    let: ("v", "ok") := MapGet (struct.get Log "cache" "l") "a" in
    (if: "ok"
    then
      Log__unlock "l";;
      "v"
    else
      Log__unlock "l";;
      let: "dv" := disk.Read (logLength + "a") in
      "dv").

Definition Log__Size: val :=
  rec: "Log__Size" "l" :=
    let: "sz" := disk.Size #() in
    "sz" - logLength.

(* Write to the disk through the log. *)
Definition Log__Write: val :=
  rec: "Log__Write" "l" "a" "v" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log "length" "l") in
    (if: "length" ≥ MaxTxnWrites
    then
      Panic ("transaction is at capacity");;
      #()
    else #());;
    let: "aBlock" := intToBlock "a" in
    let: "nextAddr" := #1 + #2 * "length" in
    disk.Write "nextAddr" "aBlock";;
    disk.Write ("nextAddr" + #1) "v";;
    MapInsert (struct.get Log "cache" "l") "a" "v";;
    struct.get Log "length" "l" <-[uint64T] "length" + #1;;
    Log__unlock "l".

(* Commit the current transaction. *)
Definition Log__Commit: val :=
  rec: "Log__Commit" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log "length" "l") in
    Log__unlock "l";;
    let: "header" := intToBlock "length" in
    disk.Write #0 "header".

Definition getLogEntry: val :=
  rec: "getLogEntry" "d" "logOffset" :=
    let: "diskAddr" := #1 + #2 * "logOffset" in
    let: "aBlock" := disk.Read "diskAddr" in
    let: "a" := blockToInt "aBlock" in
    let: "v" := disk.Read ("diskAddr" + #1) in
    ("a", "v").

(* applyLog assumes we are running sequentially *)
Definition applyLog: val :=
  rec: "applyLog" "d" "length" :=
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "i" < "length"
      then
        let: ("a", "v") := getLogEntry "d" (![uint64T] "i") in
        disk.Write (logLength + "a") "v";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue
      else Break)).

Definition clearLog: val :=
  rec: "clearLog" "d" :=
    let: "header" := intToBlock #0 in
    disk.Write #0 "header".

(* Apply all the committed transactions.

   Frees all the space in the log. *)
Definition Log__Apply: val :=
  rec: "Log__Apply" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log "length" "l") in
    applyLog (struct.get Log "d" "l") "length";;
    clearLog (struct.get Log "d" "l");;
    struct.get Log "length" "l" <-[uint64T] #0;;
    Log__unlock "l".

(* Open recovers the log following a crash or shutdown *)
Definition Open: val :=
  rec: "Open" <> :=
    let: "d" := disk.Get #() in
    let: "header" := disk.Read #0 in
    let: "length" := blockToInt "header" in
    applyLog "d" "length";;
    clearLog "d";;
    let: "cache" := NewMap disk.blockT in
    let: "lengthPtr" := ref (zero_val uint64T) in
    "lengthPtr" <-[uint64T] #0;;
    let: "l" := lock.new #() in
    struct.mk Log [
      "d" ::= "d";
      "cache" ::= "cache";
      "length" ::= "lengthPtr";
      "l" ::= "l"
    ].
