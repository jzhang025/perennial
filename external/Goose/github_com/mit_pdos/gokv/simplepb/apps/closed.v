(* autogenerated from github.com/mit-pdos/gokv/simplepb/apps/closed *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.simplepb.apps.kv.
From Goose Require github_com.mit_pdos.gokv.simplepb.config.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition r1 : expr := #1.

Definition r2 : expr := #2.

Definition configHost : expr := #10.

Definition config_main: val :=
  rec: "config_main" <> :=
    let: "servers" := ref_to (slice.T uint64T) (NewSlice uint64T #0) in
    "servers" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "servers") r1);;
    "servers" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "servers") r2);;
    config.Server__Serve (config.MakeServer (![slice.T uint64T] "servers")) configHost;;
    #().

Definition kv_replica_main: val :=
  rec: "kv_replica_main" "fname" "me" :=
    let: "x" := ref (zero_val uint64T) in
    "x" <-[uint64T] #1;;
    kv.Start "fname" "me" configHost;;
    #().

Definition kv_client_main: val :=
  rec: "kv_client_main" "fname" "me" :=
    let: "ck" := kv.MakeClerk configHost in
    kv.Clerk__Put "ck" #(str"a") #(str"ABCD");;
    let: "v1" := kv.Clerk__Get "ck" #(str"a") in
    control.impl.Assert ((StringLength "v1") = #4);;
    kv.Clerk__Put "ck" #(str"a") #(str"EFG");;
    let: "v2" := kv.Clerk__Get "ck" #(str"a") in
    control.impl.Assert ((StringLength "v2") = #3);;
    #().
