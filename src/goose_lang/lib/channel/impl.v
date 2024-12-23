From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang.lib Require Import control.impl.
From Perennial.goose_lang.lib Require Import lock.impl.

(** * Channel library *)
Notation NilChannelV := (InjLV #()) (only parsing).
Notation ChannelV chanref lock := (InjRV (PairV chanref lock)) (only parsing).

Notation ChanStructV cap eff_cap closed content: (PairV (PairV (PairV cap eff_cap) closed) content) (only parsing).

(* Notation ChannelClosedV cap content := (InjLV (PairV cap content)) (only parsing). *)
(* Notation ChannelOpenV cap eff_cap content := (InjRV (cap, eff_cap, content)) (only parsing). *)

Notation ChanConsEmptyV zero_val := (InjLV zero_val) (only parsing).
Notation ChanConsV elem cons:= (InjRV (elem, cons)) (only parsing).

Section goose_lang.
Context {ext:ffi_syntax}.
Context `{ext_ty: ext_types}.
Local Coercion Var' (s:string) : expr := Var s.

  (* 
  infinite loop for nil channels
  
  Definition Assume: val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #(). *)

Definition CloseChan: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => Panic("close of nil channel")
    | InjR "chan" =>
      match: "chan" with
        InjL "closed" => Panic("close of closed channel")
      | InjR "capcon" => 
          let: "cap" := Fst (Fst "capcon") in
          let: "con" := Snd "capcon" in
          "channel" <- InjL ("cap", "con")
      end
    end.

Definition ChanCap: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => #0
    | InjR "chan" =>
      match: "chan" with
        InjL "closed" => Fst "closed"
      | InjR "capcon" => Fst (Fst "capcon")
      end
    end.


(* return value: (return element, channel is open, return is valid) *)
Definition InnerReceive: val :=
  λ: "chanref",
  (rec: "chanRec" "c" :=
    match: "c" with
      InjL "closed" => 
        let: "cap" := Fst "closed" in
        let: "con" := Snd "closed" in
        match: "con" with
          InjL "nullV" => ("nullV", #false, #true)
        | InjR "elemcon" => 
            let: "elem" := Fst "elemcon" in
            let: "con2" := Snd "elemcon" in
              "chanref" <- InjL ("cap", "con2");;
              ("elem", #true, #true)
        end
    | InjR "capcon" =>
        let: "cap" := Fst (Fst "capcon") in
        let: "eff_cap" := Snd (Fst "capcon") in
        let: "con" := Snd "capcon" in
        match: "con" with
          InjL "nullV" => ("nullV", #true, #false)
        | InjR "elemcon" =>
          let: "elem" := Fst "elemcon" in
          let: "con" := Snd "elemcon" in
          "chanref" <- InjR ("cap", "eff_cap", "con");;
          ("elem", #true, #true)
        end
  end) (!"chanref").

Definition IncCap: val :=
  λ: "chanref",
    let: "c" := !"chanref" in
    match: "c" with 
      InjL "nullV" => #()
    | InjR "capcon" =>
      let: "cap" := Fst (Fst "capcon") in
      let: "eff_cap" := Snd (Fst "capcon") in
      let: "con" := Snd "capcon" in
      "chanref" <- InjR ("cap", (#1 + "eff_cap"), "con")
    end.

Definition DecCap: val :=
  λ: "chanref",
    let: "c" := !"chanref" in
    match: "c" with 
      InjL "nullV" => #()
    | InjR "capcon" =>
      let: "cap" := Fst (Fst "capcon") in
      let: "eff_cap" := Snd (Fst "capcon") in
      let: "con" := Snd "capcon" in
      "chanref" <- InjR ("cap", "eff_cap" - #1, "con")
    end.

Definition TryReceive: val :=
  λ: "chanref" "lock",
    lock.acquire "lock";;
    IncCap "chanref";;
    lock.release "lock";;
    lock.acquire "lock";;
    let: "r" := InnerReceive "chanref" in
      DecCap "chanref";;
      lock.release "lock";;
      "r".

Definition ChannelReceive: val :=
  λ: "channel",
  match: "channel" with
    InjL "nullV" => Assume
  | InjR "chan" =>
      let: "chanref" := Fst "chan" in
      let: "lock" := Snd "chan" in
      (rec: "chanRec" "c" :=
        let: "r" := TryReceive "c" "lock" in
        let: "v" := Fst (Fst ("r")) in
        let: "open" := Snd (Fst ("r")) in
        let: "valid" := Snd "r" in
          if: "valid" then ("v", "open")
          else "chanRec" "c"
      ) ("chanref")
  end.

Definition ChanLen': val :=
  λ: "chancon",
    (rec: "chanLen" "c" :=
      match: "c" with
        InjL "empty" => #0
      | InjR "content" => #1 + "chanLen" (Snd "content")
     end) ("chancon").

Definition ChanEffLen: val :=
  λ: "channel",
    let: "chanref" := Fst "channel" in
    let: "lock" := Snd "channel" in
      lock.acquire "lock";;
      let: "r" := (rec: "chanLen" "c" :=
        match: "c" with
          InjL "closed" => 
            let: "con" := (Snd "closed") in (ChanLen' "con")
        | InjR "capcon" =>
            let: "con" := (Snd "capcon") in (ChanLen' "con")
        end) (!"chanref") in (lock.release "lock";; "r").

Definition ChanLen: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => #0
    | InjR "chan" =>
        let: "cap" := ChanCap "channel" in
        let: "con" := Snd "chan" in
        let: "eff_len" := ChanEffLen "con" in
          if: "eff_len" < "cap" then "eff_len"
          else "cap"
    end.

Definition ChanAppend: val :=
  λ: "con" "v",
  (rec: "chanAppend" "con" :=
    match: "con" with
      InjL "empty" => InjR ("v", InjL "empty")
    | InjR "elemCon" => 
      let: "elem" := Fst "elemCon" in
      let: "con2" := Snd "elemCon" in
        InjR ("elem", "chanAppend" "con2")
    end
  ) ("con").

Definition TrySend: val :=
  λ: "chanref" "lock" "v",
    lock.acquire "lock";;
    match: (! "chanref") with 
      InjL "nullV" => Panic ("send on closed channel")
    | InjR "capcon" =>
        let: "cap" := Fst (Fst "capcon") in
        let: "eff_cap" := Snd (Fst "capcon") in
        let: "con" := Snd "capcon" in
        let: "len" := ChanLen' "con" in
          if: "eff_cap" > "len" then 
            "chanref" <- InjR ("cap", "eff_cap", ChanAppend "con" "v");;
            lock.release "lock";;#true
          else lock.release "lock";;#false
    end.

Definition Assume: val :=
  λ: "cond", if: Var "cond" then #()
              else (rec: "loop" <> := Var "loop" #()) #().

Definition ChannelSend: val :=
  λ: "channel" "v",
  match: "channel" with
    InjL "nullV" => Assume
  | InjR "chan" =>
      let: "chanref" := Fst "chan" in
      let: "lock" := Snd "chan" in
      (rec: "chanSend" "c" :=
        let: "r" := TrySend "c" "lock" "v" in
          if: "r" then #true
          else "chanSend" "c"
      ) ("chanref")
  end.


End goose_lang.