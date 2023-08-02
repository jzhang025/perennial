(* autogenerated from github.com/mit-pdos/vmvcc/examples *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.vmvcc.examples.strnum.
From Goose Require github_com.mit_pdos.vmvcc.vmvcc.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* hello.go *)

Definition hello: val :=
  rec: "hello" "txn" :=
    vmvcc.Txn__Write "txn" #0 #(str"hello");;
    vmvcc.Txn__Read "txn" #0;;
    vmvcc.Txn__Delete "txn" #0;;
    #true.

Definition Hello: val :=
  rec: "Hello" "txno" :=
    let: "body" := (λ: "txni",
      hello "txni"
      ) in
    vmvcc.Txn__Run "txno" "body";;
    #().

Definition CallHello: val :=
  rec: "CallHello" <> :=
    let: "db" := vmvcc.MkDB #() in
    vmvcc.DB__ActivateGC "db";;
    let: "txn" := vmvcc.DB__NewTxn "db" in
    Hello "txn";;
    #().

(* xfer.go *)

Definition xfer: val :=
  rec: "xfer" "txn" "src" "dst" "amt" :=
    let: ("sbalx", <>) := vmvcc.Txn__Read "txn" "src" in
    let: "sbal" := strnum.StringToU64 "sbalx" in
    (if: "sbal" < "amt"
    then #false
    else
      let: "sbaly" := strnum.U64ToString ("sbal" - "amt") in
      vmvcc.Txn__Write "txn" "src" "sbaly";;
      let: ("dbalx", <>) := vmvcc.Txn__Read "txn" "dst" in
      let: "dbal" := strnum.StringToU64 "dbalx" in
      (if: "dbal" + "amt" < "dbal"
      then #false
      else
        let: "dbaly" := strnum.U64ToString ("dbal" + "amt") in
        vmvcc.Txn__Write "txn" "dst" "dbaly";;
        #true)).

Definition AtomicXfer: val :=
  rec: "AtomicXfer" "txno" "src" "dst" "amt" :=
    let: "body" := (λ: "txni",
      xfer "txni" "src" "dst" "amt"
      ) in
    vmvcc.Txn__Run "txno" "body".
