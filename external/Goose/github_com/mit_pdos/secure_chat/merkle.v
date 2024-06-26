(* autogenerated from github.com/mit-pdos/secure-chat/merkle *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.secure_chat.merkle.merkle_shim.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition ErrNone : expr := #0.

Definition ErrFound : expr := #1.

Definition ErrNotFound : expr := #2.

Definition ErrBadInput : expr := #3.

Definition ErrPathProof : expr := #4.

Definition HashLen : expr := #32.

Definition NumChildren : expr := #256.

Definition EmptyNodeId : expr := #(U8 0).

Definition LeafNodeId : expr := #(U8 1).

Definition InteriorNodeId : expr := #(U8 2).

Definition Hasher: ty := slice.T byteT.

(* Goose doesn't support non-struct types that well, so until that exists,
   use type aliases and non-method funcs. *)
Definition HasherWrite: val :=
  rec: "HasherWrite" "h" "data" :=
    ForSlice byteT <> "b" "data"
      ("h" <-[slice.T byteT] (SliceAppend byteT (![slice.T byteT] "h") "b"));;
    #().

Definition HasherWriteSl: val :=
  rec: "HasherWriteSl" "h" "data" :=
    ForSlice (slice.T byteT) <> "hash" "data"
      (HasherWrite "h" "hash");;
    #().

Definition HasherSum: val :=
  rec: "HasherSum" "h" "b" :=
    let: "b1" := ref_to (slice.T byteT) "b" in
    let: "hash" := merkle_shim.Hash "h" in
    ForSlice byteT <> "byt" "hash"
      ("b1" <-[slice.T byteT] (SliceAppend byteT (![slice.T byteT] "b1") "byt"));;
    ![slice.T byteT] "b1".

Definition CopySlice: val :=
  rec: "CopySlice" "b1" :=
    let: "b2" := NewSlice byteT (slice.len "b1") in
    SliceCopy byteT "b2" "b1";;
    "b2".

Definition Id: ty := slice.T byteT.

Definition Val: ty := slice.T byteT.

Definition Node := struct.decl [
  "Val" :: Val;
  "hash" :: slice.T byteT;
  "Children" :: slice.T ptrT
].

Definition Node__Hash: val :=
  rec: "Node__Hash" "n" :=
    (if: "n" = #null
    then merkle_shim.Hash (SliceSingleton EmptyNodeId)
    else struct.loadF Node "hash" "n").

Definition Node__UpdateLeafHash: val :=
  rec: "Node__UpdateLeafHash" "n" :=
    let: "h" := ref (zero_val (slice.T byteT)) in
    HasherWrite "h" (struct.loadF Node "Val" "n");;
    HasherWrite "h" (SliceSingleton LeafNodeId);;
    struct.storeF Node "hash" "n" (HasherSum (![slice.T byteT] "h") slice.nil);;
    #().

(* Assumes recursive child hashes are already up-to-date. *)
Definition Node__UpdateInteriorHash: val :=
  rec: "Node__UpdateInteriorHash" "n" :=
    let: "h" := ref (zero_val (slice.T byteT)) in
    ForSlice ptrT <> "n" (struct.loadF Node "Children" "n")
      (HasherWrite "h" (Node__Hash "n"));;
    HasherWrite "h" (SliceSingleton InteriorNodeId);;
    struct.storeF Node "hash" "n" (HasherSum (![slice.T byteT] "h") slice.nil);;
    #().

(* These nodes are neither interior nodes nor leaf nodes.
   They'll be specialized after adding them to the tree. *)
Definition NewGenericNode: val :=
  rec: "NewGenericNode" <> :=
    let: "v" := ref (zero_val (slice.T byteT)) in
    let: "c" := NewSlice ptrT NumChildren in
    struct.new Node [
      "Val" ::= ![slice.T byteT] "v";
      "hash" ::= slice.nil;
      "Children" ::= "c"
    ].

Definition Digest: ty := slice.T byteT.

(* General proof object.
   Binds an id down the tree to a particular node hash. *)
Definition PathProof := struct.decl [
  "Id" :: Id;
  "NodeHash" :: slice.T byteT;
  "Digest" :: Digest;
  "ChildHashes" :: slice.T (slice.T (slice.T byteT))
].

Definition MembProof: ty := slice.T (slice.T (slice.T byteT)).

Definition NonmembProof: ty := slice.T (slice.T (slice.T byteT)).

Definition IsValidHashSl: val :=
  rec: "IsValidHashSl" "data" :=
    let: "ok" := ref_to boolT #true in
    ForSlice (slice.T byteT) <> "hash" "data"
      ((if: (slice.len "hash") ≠ HashLen
      then "ok" <-[boolT] #false
      else #()));;
    ![boolT] "ok".

Definition PathProof__Check: val :=
  rec: "PathProof__Check" "p" :=
    let: "err" := ref_to uint64T ErrNone in
    let: "currHash" := ref_to (slice.T byteT) (struct.loadF PathProof "NodeHash" "p") in
    let: "proofLen" := slice.len (struct.loadF PathProof "ChildHashes" "p") in
    let: "loopIdx" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "loopIdx") < "proofLen"); (λ: <>, "loopIdx" <-[uint64T] ((![uint64T] "loopIdx") + #1)) := λ: <>,
      let: "pathIdx" := ("proofLen" - #1) - (![uint64T] "loopIdx") in
      let: "children" := SliceGet (slice.T (slice.T byteT)) (struct.loadF PathProof "ChildHashes" "p") "pathIdx" in
      (if: (slice.len "children") ≠ (NumChildren - #1)
      then
        "err" <-[uint64T] ErrPathProof;;
        Continue
      else
        (if: (~ (IsValidHashSl "children"))
        then
          "err" <-[uint64T] ErrPathProof;;
          Continue
        else
          let: "pos" := to_u64 (SliceGet byteT (struct.loadF PathProof "Id" "p") "pathIdx") in
          let: "before" := SliceTake "children" "pos" in
          let: "after" := SliceSkip (slice.T byteT) "children" "pos" in
          let: "hr" := ref (zero_val (slice.T byteT)) in
          HasherWriteSl "hr" "before";;
          HasherWrite "hr" (![slice.T byteT] "currHash");;
          HasherWriteSl "hr" "after";;
          HasherWrite "hr" (SliceSingleton InteriorNodeId);;
          "currHash" <-[slice.T byteT] (HasherSum (![slice.T byteT] "hr") slice.nil);;
          Continue)));;
    (if: (![uint64T] "err") ≠ ErrNone
    then ErrPathProof
    else
      (if: (~ (std.BytesEqual (![slice.T byteT] "currHash") (struct.loadF PathProof "Digest" "p")))
      then ErrPathProof
      else ErrNone)).

Definition MembProofCheck: val :=
  rec: "MembProofCheck" "proof" "id" "val" "digest" :=
    (if: (slice.len "id") ≠ HashLen
    then ErrBadInput
    else
      (if: (slice.len "proof") ≠ HashLen
      then ErrBadInput
      else
        let: "hr" := ref (zero_val (slice.T byteT)) in
        HasherWrite "hr" "val";;
        HasherWrite "hr" (SliceSingleton LeafNodeId);;
        let: "pathProof" := struct.new PathProof [
          "Id" ::= "id";
          "NodeHash" ::= HasherSum (![slice.T byteT] "hr") slice.nil;
          "Digest" ::= "digest";
          "ChildHashes" ::= "proof"
        ] in
        PathProof__Check "pathProof")).

Definition NonmembProofCheck: val :=
  rec: "NonmembProofCheck" "proof" "id" "digest" :=
    (if: HashLen < (slice.len "proof")
    then ErrBadInput
    else
      (if: (slice.len "id") < (slice.len "proof")
      then ErrBadInput
      else
        let: "idPref" := SliceTake (CopySlice "id") (slice.len "proof") in
        let: "hr" := ref (zero_val (slice.T byteT)) in
        HasherWrite "hr" (SliceSingleton EmptyNodeId);;
        let: "pathProof" := struct.new PathProof [
          "Id" ::= "idPref";
          "NodeHash" ::= HasherSum (![slice.T byteT] "hr") slice.nil;
          "Digest" ::= "digest";
          "ChildHashes" ::= "proof"
        ] in
        PathProof__Check "pathProof")).

(* Having a separate Tree type makes the API more clear compared to if it
   was just a Node. *)
Definition Tree := struct.decl [
  "Root" :: ptrT
].

Definition Tree__Print: val :=
  rec: "Tree__Print" "t" :=
    let: "qCurr" := ref (zero_val (slice.T ptrT)) in
    let: "qNext" := ref (zero_val (slice.T ptrT)) in
    "qCurr" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "qCurr") (struct.loadF Tree "Root" "t"));;
    Skip;;
    (for: (λ: <>, (slice.len (![slice.T ptrT] "qCurr")) > #0); (λ: <>, Skip) := λ: <>,
      Skip;;
      (for: (λ: <>, (slice.len (![slice.T ptrT] "qCurr")) > #0); (λ: <>, Skip) := λ: <>,
        let: "top" := SliceGet ptrT (![slice.T ptrT] "qCurr") #0 in
        "qCurr" <-[slice.T ptrT] (SliceSkip ptrT (![slice.T ptrT] "qCurr") #1);;
        (if: "top" = #null
        then
          (* log.Print("nil | ") *)
          Continue
        else
          (if: (struct.loadF Node "Val" "top") ≠ slice.nil
          then
            (* log.Print(top.Hash(), top.Val, " | ") *)
            #()
          else
            (* log.Print(top.Hash(), " | ") *)
            #());;
          ForSlice ptrT <> "child" (struct.loadF Node "Children" "top")
            ("qNext" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "qNext") "child"));;
          Continue));;
      "qCurr" <-[slice.T ptrT] (![slice.T ptrT] "qNext");;
      "qNext" <-[slice.T ptrT] slice.nil;;
      (* log.Println() *)
      Continue);;
    #().

Definition GetChildHashes: val :=
  rec: "GetChildHashes" "nodePath" "id" :=
    let: "childHashes" := NewSlice (slice.T (slice.T byteT)) ((slice.len "nodePath") - #1) in
    let: "pathIdx" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "pathIdx") < ((slice.len "nodePath") - #1)); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
      let: "children" := struct.loadF Node "Children" (SliceGet ptrT "nodePath" (![uint64T] "pathIdx")) in
      let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
      let: "proofChildren" := NewSlice (slice.T byteT) (NumChildren - #1) in
      SliceSet (slice.T (slice.T byteT)) "childHashes" (![uint64T] "pathIdx") "proofChildren";;
      let: "beforeIdx" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "beforeIdx") < (to_u64 "pos")); (λ: <>, "beforeIdx" <-[uint64T] ((![uint64T] "beforeIdx") + #1)) := λ: <>,
        SliceSet (slice.T byteT) "proofChildren" (![uint64T] "beforeIdx") (CopySlice (Node__Hash (SliceGet ptrT "children" (![uint64T] "beforeIdx"))));;
        Continue);;
      let: "afterIdx" := ref_to uint64T ((to_u64 "pos") + #1) in
      (for: (λ: <>, (![uint64T] "afterIdx") < NumChildren); (λ: <>, "afterIdx" <-[uint64T] ((![uint64T] "afterIdx") + #1)) := λ: <>,
        SliceSet (slice.T byteT) "proofChildren" ((![uint64T] "afterIdx") - #1) (CopySlice (Node__Hash (SliceGet ptrT "children" (![uint64T] "afterIdx"))));;
        Continue);;
      Continue);;
    "childHashes".

(* Get the maximal path corresponding to Id.
   If the full path to a leaf node doesn't exist,
   return the partial path that ends in an empty node,
   and set found to true. *)
Definition Tree__GetPath: val :=
  rec: "Tree__GetPath" "t" "id" :=
    let: "nodePath" := ref (zero_val (slice.T ptrT)) in
    "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (struct.loadF Tree "Root" "t"));;
    (if: (struct.loadF Tree "Root" "t") = #null
    then (![slice.T ptrT] "nodePath", #false)
    else
      let: "found" := ref_to boolT #true in
      let: "pathIdx" := ref_to uint64T #0 in
      (for: (λ: <>, ((![uint64T] "pathIdx") < HashLen) && (![boolT] "found")); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
        let: "currNode" := SliceGet ptrT (![slice.T ptrT] "nodePath") (![uint64T] "pathIdx") in
        let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
        let: "nextNode" := SliceGet ptrT (struct.loadF Node "Children" "currNode") "pos" in
        "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") "nextNode");;
        (if: "nextNode" = #null
        then
          "found" <-[boolT] #false;;
          Continue
        else Continue));;
      (![slice.T ptrT] "nodePath", ![boolT] "found")).

Definition Tree__GetPathAddNodes: val :=
  rec: "Tree__GetPathAddNodes" "t" "id" :=
    (if: (struct.loadF Tree "Root" "t") = #null
    then struct.storeF Tree "Root" "t" (NewGenericNode #())
    else #());;
    let: "nodePath" := ref (zero_val (slice.T ptrT)) in
    "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (struct.loadF Tree "Root" "t"));;
    let: "pathIdx" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "pathIdx") < HashLen); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") + #1)) := λ: <>,
      let: "currNode" := SliceGet ptrT (![slice.T ptrT] "nodePath") (![uint64T] "pathIdx") in
      let: "pos" := SliceGet byteT "id" (![uint64T] "pathIdx") in
      (if: (SliceGet ptrT (struct.loadF Node "Children" "currNode") "pos") = #null
      then SliceSet ptrT (struct.loadF Node "Children" "currNode") "pos" (NewGenericNode #())
      else #());;
      "nodePath" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "nodePath") (SliceGet ptrT (struct.loadF Node "Children" "currNode") "pos"));;
      Continue);;
    ![slice.T ptrT] "nodePath".

Definition Tree__Put: val :=
  rec: "Tree__Put" "t" "id" "v" :=
    (if: (slice.len "id") ≠ HashLen
    then (slice.nil, slice.nil, ErrBadInput)
    else
      let: "nodePath" := Tree__GetPathAddNodes "t" "id" in
      struct.storeF Node "Val" (SliceGet ptrT "nodePath" HashLen) "v";;
      Node__UpdateLeafHash (SliceGet ptrT "nodePath" HashLen);;
      let: "pathIdx" := ref_to uint64T HashLen in
      (for: (λ: <>, (![uint64T] "pathIdx") ≥ #1); (λ: <>, "pathIdx" <-[uint64T] ((![uint64T] "pathIdx") - #1)) := λ: <>,
        Node__UpdateInteriorHash (SliceGet ptrT "nodePath" ((![uint64T] "pathIdx") - #1));;
        Continue);;
      let: "digest" := CopySlice (Node__Hash (SliceGet ptrT "nodePath" #0)) in
      let: "proof" := GetChildHashes "nodePath" "id" in
      ("digest", "proof", ErrNone)).

Definition Tree__Get: val :=
  rec: "Tree__Get" "t" "id" :=
    (if: (slice.len "id") ≠ HashLen
    then (slice.nil, slice.nil, slice.nil, ErrBadInput)
    else
      let: ("nodePath", "found") := Tree__GetPath "t" "id" in
      (if: (~ "found")
      then (slice.nil, slice.nil, slice.nil, ErrNotFound)
      else
        let: "val" := CopySlice (struct.loadF Node "Val" (SliceGet ptrT "nodePath" HashLen)) in
        let: "digest" := CopySlice (Node__Hash (SliceGet ptrT "nodePath" #0)) in
        let: "proof" := GetChildHashes "nodePath" "id" in
        ("val", "digest", "proof", ErrNone))).

Definition Tree__GetNil: val :=
  rec: "Tree__GetNil" "t" "id" :=
    (if: (slice.len "id") ≠ HashLen
    then (slice.nil, slice.nil, ErrBadInput)
    else
      let: ("nodePath", "found") := Tree__GetPath "t" "id" in
      (if: "found"
      then (slice.nil, slice.nil, ErrFound)
      else
        let: "digest" := CopySlice (Node__Hash (SliceGet ptrT "nodePath" #0)) in
        let: "proof" := GetChildHashes "nodePath" "id" in
        ("digest", "proof", ErrNone))).

End code.
