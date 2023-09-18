(* autogenerated from github.com/mit-pdos/gokv/map_string_marshal *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition EncodeStringMap: val :=
  rec: "EncodeStringMap" "kvs" :=
    let: "enc" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (MapLen "kvs"));;
    MapIter "kvs" (λ: "k" "v",
      "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (StringLength "k"));;
      "enc" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes "k"));;
      "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (StringLength "v"));;
      "enc" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes "v")));;
    ![slice.T byteT] "enc".

Definition DecodeStringMap: val :=
  rec: "DecodeStringMap" "enc_in" :=
    let: "enc" := ref_to (slice.T byteT) "enc_in" in
    let: "numEntries" := ref (zero_val uint64T) in
    let: "kvs" := NewMap stringT stringT #() in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "numEntries" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "numEntries2" := ![uint64T] "numEntries" in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "numEntries2"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      let: "ln" := ref (zero_val uint64T) in
      let: "key" := ref (zero_val (slice.T byteT)) in
      let: "val" := ref (zero_val (slice.T byteT)) in
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      "ln" <-[uint64T] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      let: ("0_ret", "1_ret") := marshal.ReadBytes (![slice.T byteT] "enc") (![uint64T] "ln") in
      "key" <-[slice.T byteT] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
      "ln" <-[uint64T] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      let: ("0_ret", "1_ret") := marshal.ReadBytes (![slice.T byteT] "enc") (![uint64T] "ln") in
      "val" <-[slice.T byteT] "0_ret";;
      "enc" <-[slice.T byteT] "1_ret";;
      MapInsert "kvs" (StringFromBytes (![slice.T byteT] "key")) (StringFromBytes (![slice.T byteT] "val"));;
      Continue);;
    "kvs".

End code.