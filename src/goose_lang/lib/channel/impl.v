From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang.lib Require Import control.impl.
From Perennial.goose_lang.lib Require Import lock.impl.

(** * Channel library *)
Notation NilChannelV := (InjLV #()) (only parsing).
Notation ChannelV cap chanref lock := (InjRV (cap, chanref, lock)) (only parsing).

Notation ChannelClosedV content := (InjLV content) (only parsing).
Notation ChannelOpenV eff_cap content := (InjRV (eff_cap, content)) (only parsing).

Notation ChanConsEmptyV zero_val := (InjLV zero_val) (only parsing).
Notation ChanConsV elem cons:= (InjRV (elem, cons)) (only parsing).

Section goose_lang.
Context {ext:ffi_syntax}.
Context `{ext_ty: ext_types}.
Local Coercion Var' (s:string) : expr := Var s.

Definition CloseChan: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => Panic("close of nil channel")
    | InjR "chan" =>
        let: "cap" := Fst (Fst "chan") in
        let: "chanref" := Snd (Fst "chan") in
        let: "lock" := Snd "chan" in
        lock.acquire "lock";;
        match: !"chanref" with
          InjL "empty" => Panic ("close closed channel")
        | InjR "open" =>
            let: "con" := Snd "open" in
              "chanref" <- InjL "con";;
              lock.release "lock"
        end
    end.

Definition ChanCap: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => #0
    | InjR "chan" => Fst (Fst "chan")
    end.

(* return value: (return element, channel is non-empty, return is valid) *)
Definition InnerReceive: val :=
  λ: "chanref",
    match: !"chanref" with
      InjL "closed" =>
        match: "closed" with
          InjL "empty" => ("empty", #false, #true)
        | InjR "con" =>
            let: "elem" := Fst "con" in
            let: "rest" := Snd "con" in
              "chanref" <- InjL("rest");;
              ("elem", #true, #true)
        end
    | InjR "open" =>
        let: "eff_cap" := Fst "open" in
        let: "con" := Snd "open" in
        match: "con" with
          InjL "empty" => ("empty", #false, #false)
        | InjR "con" =>
            let: "elem" := Fst "con" in
            let: "rest" := Snd "con" in
              "chanref" <- InjR("eff_cap", "rest");;
              ("elem", #true, #true)
        end
    end.

Definition IncCap: val :=
  λ: "chanref",
    match: !"chanref" with
      InjL "closed" => #()
    | InjR "open" =>
        let: "eff_cap" := Fst "open" in
        let: "con" := Snd "open" in
        "chanref" <- InjR (#1 + "eff_cap", "con")
    end.

Definition DecCap: val :=
  λ: "chanref",
    match: !"chanref" with
      InjL "closed" => #()
    | InjR "open" =>
      let: "eff_cap" := Fst "open" in
      let: "con" := Snd "open" in
      "chanref" <- InjR("eff_cap" - #1, "con")
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
      let: "cap" := Fst (Fst "chan") in
      let: "chanref" := Snd (Fst "chan") in
      let: "lock" := Snd "chan" in
      (rec: "chanRec" "c" :=
        let: "r" := TryReceive "c" "lock" in
        let: "v" := Fst (Fst ("r")) in
        let: "non-empty" := Snd (Fst ("r")) in
        let: "valid" := Snd "r" in
          if: "valid" then ("v", "non-empty")
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

Definition ChanLen: val :=
  λ: "channel",
    match: "channel" with
      InjL "nullv" => #0
    | InjR "chan" =>
        let: "cap" := Fst (Fst "chan") in
        let: "chanref" := Snd (Fst "chan") in
        let: "lock" := Snd "chan" in
          lock.acquire "lock";;
          let: "eff_len" := (let: "con" := Snd "chanref" in  ChanLen' "con") in
            lock.release "lock";; 
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
    match: !"chanref" with
      InjL "empty" => Panic ("send on closed channel")
    | InjR "open" =>
        let: "eff_cap" := Fst "open" in
        let: "con" := Snd "open" in
        let: "len" := ChanLen' "con" in
        if: "eff_cap" > "len" then
          "chanref" <- InjR ("eff_cap", ChanAppend "con" "v");;
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
      let: "cap" := Fst (Fst "chan") in
      let: "chanref" := Snd (Fst "chan") in
      let: "lock" := Snd "chan" in
      (rec: "chanSend" "c" :=
        let: "r" := TrySend "c" "lock" "v" in
          if: "r" then #()
          else "chanSend" "c"
      ) ("chanref")
  end.

End goose_lang.