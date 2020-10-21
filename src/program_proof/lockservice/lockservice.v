(* autogenerated from lockservice *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* common.go *)

(* TryLock(lockname) returns OK=true if the lock is not held.
   If it is held, it returns OK=false immediately. *)
Module TryLockRequest.
  Definition S := struct.decl [
    "CID" :: uint64T;
    "Seq" :: uint64T;
    "Args" :: uint64T
  ].
End TryLockRequest.

Module TryLockReply.
  Definition S := struct.decl [
    "Stale" :: boolT;
    "Ret" :: boolT
  ].
End TryLockReply.

(* Unlock(lockname) returns OK=true if the lock was held.
   It returns OK=false if the lock was not held. *)
Module UnlockRequest.
  Definition S := struct.decl [
    "CID" :: uint64T;
    "Seq" :: uint64T;
    "Args" :: uint64T
  ].
End UnlockRequest.

Definition UnlockReply: ty := struct.t TryLockReply.S.

(* Call this before doing an increment that has risk of overflowing.
   If it's going to overflow, this'll loop forever, so the bad addition can never happen *)
Definition overflow_guard_incr: val :=
  rec: "overflow_guard_incr" "v" :=
    Skip;;
    (for: (λ: <>, "v" + #1 < "v"); (λ: <>, Skip) := λ: <>,
      Continue).

(* nondet.go *)

Definition nondet: val :=
  rec: "nondet" <> :=
    #true.

(* server.go *)

Module LockServer.
  Definition S := struct.decl [
    "mu" :: lockRefT;
    "locks" :: mapT boolT;
    "lastSeq" :: mapT uint64T;
    "lastReply" :: mapT boolT
  ].
End LockServer.

Definition LockServer__tryLock_core: val :=
  rec: "LockServer__tryLock_core" "ls" "lockname" :=
    let: ("locked", <>) := MapGet (struct.loadF LockServer.S "locks" "ls") "lockname" in
    (if: "locked"
    then #false
    else
      MapInsert (struct.loadF LockServer.S "locks" "ls") "lockname" #true;;
      #true).

Definition LockServer__unlock_core: val :=
  rec: "LockServer__unlock_core" "ls" "lockname" :=
    let: ("locked", <>) := MapGet (struct.loadF LockServer.S "locks" "ls") "lockname" in
    (if: "locked"
    then
      MapInsert (struct.loadF LockServer.S "locks" "ls") "lockname" #false;;
      #true
    else #false).

Definition LockServer__checkReplyCache: val :=
  rec: "LockServer__checkReplyCache" "ls" "CID" "Seq" "reply" :=
    let: ("last", "ok") := MapGet (struct.loadF LockServer.S "lastSeq" "ls") "CID" in
    struct.storeF TryLockReply.S "Stale" "reply" #false;;
    (if: "ok" && ("Seq" ≤ "last")
    then
      (if: "Seq" < "last"
      then
        struct.storeF TryLockReply.S "Stale" "reply" #true;;
        #true
      else
        struct.storeF TryLockReply.S "Ret" "reply" (Fst (MapGet (struct.loadF LockServer.S "lastReply" "ls") "CID"));;
        #true)
    else
      MapInsert (struct.loadF LockServer.S "lastSeq" "ls") "CID" "Seq";;
      #false).

(* server Lock RPC handler.
   returns true iff error *)
Definition LockServer__TryLock: val :=
  rec: "LockServer__TryLock" "ls" "req" "reply" :=
    lock.acquire (struct.loadF LockServer.S "mu" "ls");;
    (if: LockServer__checkReplyCache "ls" (struct.loadF TryLockRequest.S "CID" "req") (struct.loadF TryLockRequest.S "Seq" "req") "reply"
    then
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false
    else
      struct.storeF TryLockReply.S "Ret" "reply" (LockServer__tryLock_core "ls" (struct.loadF TryLockRequest.S "Args" "req"));;
      MapInsert (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF TryLockRequest.S "CID" "req") (struct.loadF TryLockReply.S "Ret" "reply");;
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false).

(* server Unlock RPC handler.
   returns true iff error *)
Definition LockServer__Unlock: val :=
  rec: "LockServer__Unlock" "ls" "req" "reply" :=
    lock.acquire (struct.loadF LockServer.S "mu" "ls");;
    (if: LockServer__checkReplyCache "ls" (struct.loadF UnlockRequest.S "CID" "req") (struct.loadF UnlockRequest.S "Seq" "req") "reply"
    then
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false
    else
      struct.storeF TryLockReply.S "Ret" "reply" (LockServer__unlock_core "ls" (struct.loadF UnlockRequest.S "Args" "req"));;
      MapInsert (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF UnlockRequest.S "CID" "req") (struct.loadF TryLockReply.S "Ret" "reply");;
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false).

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "ls" := struct.alloc LockServer.S (zero_val (struct.t LockServer.S)) in
    struct.storeF LockServer.S "locks" "ls" (NewMap boolT);;
    struct.storeF LockServer.S "lastSeq" "ls" (NewMap uint64T);;
    struct.storeF LockServer.S "lastReply" "ls" (NewMap boolT);;
    struct.storeF LockServer.S "mu" "ls" (lock.new #());;
    "ls".

(* rpc.go *)

(* Returns true iff server reported error or request "timed out" *)
Definition CallTryLock: val :=
  rec: "CallTryLock" "srv" "args" "reply" :=
    Fork (let: "dummy_reply" := struct.alloc TryLockReply.S (zero_val (struct.t TryLockReply.S)) in
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            LockServer__TryLock "srv" "args" "dummy_reply";;
            Continue));;
    (if: nondet #()
    then LockServer__TryLock "srv" "args" "reply"
    else #true).

(* Returns true iff server reported error or request "timed out" *)
Definition CallUnlock: val :=
  rec: "CallUnlock" "srv" "args" "reply" :=
    Fork (let: "dummy_reply" := struct.alloc TryLockReply.S (zero_val UnlockReply) in
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            LockServer__Unlock "srv" "args" "dummy_reply";;
            Continue));;
    (if: nondet #()
    then LockServer__Unlock "srv" "args" "reply"
    else #true).

(* client.go *)

(* the lockservice Clerk lives in the client
   and maintains a little state. *)
Module Clerk.
  Definition S := struct.decl [
    "primary" :: struct.ptrT LockServer.S;
    "cid" :: uint64T;
    "seq" :: uint64T
  ].
End Clerk.

Definition MakeClerk: val :=
  rec: "MakeClerk" "primary" "cid" :=
    let: "ck" := struct.alloc Clerk.S (zero_val (struct.t Clerk.S)) in
    struct.storeF Clerk.S "primary" "ck" "primary";;
    struct.storeF Clerk.S "cid" "ck" "cid";;
    struct.storeF Clerk.S "seq" "ck" #1;;
    "ck".

Definition Clerk__TryLock: val :=
  rec: "Clerk__TryLock" "ck" "lockname" :=
    overflow_guard_incr (struct.loadF Clerk.S "seq" "ck");;
    let: "args" := ref_to (refT (struct.t TryLockRequest.S)) (struct.new TryLockRequest.S [
      "Args" ::= "lockname";
      "CID" ::= struct.loadF Clerk.S "cid" "ck";
      "Seq" ::= struct.loadF Clerk.S "seq" "ck"
    ]) in
    struct.storeF Clerk.S "seq" "ck" (struct.loadF Clerk.S "seq" "ck" + #1);;
    let: "errb" := ref_to boolT #false in
    let: "reply" := struct.alloc TryLockReply.S (zero_val (struct.t TryLockReply.S)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      "errb" <-[boolT] CallTryLock (struct.loadF Clerk.S "primary" "ck") (![refT (struct.t TryLockRequest.S)] "args") "reply";;
      (if: (![boolT] "errb" = #false)
      then Break
      else Continue));;
    struct.loadF TryLockReply.S "Ret" "reply".

(* ask the lock service to unlock a lock.
   returns true if the lock was previously held,
   false otherwise. *)
Definition Clerk__Unlock: val :=
  rec: "Clerk__Unlock" "ck" "lockname" :=
    overflow_guard_incr (struct.loadF Clerk.S "seq" "ck");;
    let: "args" := struct.new UnlockRequest.S [
      "Args" ::= "lockname";
      "CID" ::= struct.loadF Clerk.S "cid" "ck";
      "Seq" ::= struct.loadF Clerk.S "seq" "ck"
    ] in
    struct.storeF Clerk.S "seq" "ck" (struct.loadF Clerk.S "seq" "ck" + #1);;
    let: "errb" := ref (zero_val boolT) in
    let: "reply" := struct.alloc TryLockReply.S (zero_val (struct.t TryLockReply.S)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      "errb" <-[boolT] CallUnlock (struct.loadF Clerk.S "primary" "ck") "args" "reply";;
      (if: (![boolT] "errb" = #false)
      then Break
      else Continue));;
    struct.loadF TryLockReply.S "Ret" "reply".

(* Spins until we have the lock *)
Definition Clerk__Lock: val :=
  rec: "Clerk__Lock" "ck" "lockname" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: Clerk__TryLock "ck" "lockname"
      then Break
      else Continue));;
    #true.
