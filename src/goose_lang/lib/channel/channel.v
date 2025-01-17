From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import wp_store.
(* From Perennial.goose_lang.lib Require Import control. *)
From Perennial.goose_lang.lib Require Export channel.impl.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.program_proof Require Import proof_prelude.
Import uPred.


Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Fixpoint chan_contents (zero: val) (l : list val): val :=
    match l with
    | nil => InjLV zero
    | cons x l' => InjRV (x, (chan_contents zero l'))
    end.

Definition peek (zero: val) (l : list val): val :=
    match l with
    | nil => zero
    | cons x l' => x
    end.

Definition non_empty (l : list val): bool :=
  match l with
  | nil => false
  | cons x l' => true
  end.

Definition valid_return (closed : bool) (l : list val): bool :=
    orb closed (non_empty l).

Definition tail (l : list val): list val :=
    match l with
    | nil => l
    | cons x l' => l'
    end.


Definition own_chan (chanref: loc) (eff_cap: Z) (closed: bool) ty (l: list val) (P : val -> iProp Σ): iProp Σ :=
  ⌜has_zero ty⌝ ∗ (if closed then chanref ↦ ChannelClosedV (chan_contents (zero_val ty) l)
  else chanref ↦ ChannelOpenV #eff_cap (chan_contents (zero_val ty) l))%I
  ∗ ([∗ list] _ ↦ elem ∈ l, P elem ∗ ⌜val_ty elem ty⌝).

Definition is_channel_alloc (chanref: loc) lk (closed: bool) ty (P : val -> iProp Σ): iProp Σ :=
  is_lock nroot lk (∃ eff_cap l, own_chan chanref eff_cap closed ty l P).

Definition is_channel c closed ty (P : val -> iProp Σ): iProp Σ :=
  ⌜c = InjLV #()⌝ ∗ ⌜has_zero ty⌝ ∨ (∃ cap chanref lk, is_channel_alloc chanref lk closed ty P ∗ ⌜c = InjRV (cap, #chanref, lk)⌝).

Theorem nil_chan ty P:
  ⊢(⌜has_zero ty⌝ -∗ is_channel (InjLV #()) false ty P)%I.
Proof.
  iIntros.
  unfold is_channel.
  iLeft.
  done.
Qed.

Theorem wp_NewChan E ty (cap : Z) P:
  {{{ ⌜has_zero ty⌝ }}}
    NewChan ty #(cap) @ E
  {{{ c chanref lk, RET (c);
    is_channel_alloc chanref lk false ty P ∗
    ⌜c = InjRV (#cap, #chanref, lk)⌝}}}.
Proof.
  iIntros (Φ) "%Ht HΦ".
  wp_lam.
  wp_pures.
  wp_apply wp_alloc_untyped.
  { eauto. }
  iIntros (chanref) "Hc".
  wp_pures.
  wp_apply (newlock_spec with "[Hc]").
  2: { 
    iIntros (lk) "Hlk".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    unfold is_channel_alloc.
    iFrame.
    eauto.
  }
  iExists cap, nil.
  unfold own_chan.
  iModIntro.
  unfold chan_contents.
  iFrame.
  eauto.
Qed.

Theorem wp_ChanCap c closed ty (P : val -> iProp Σ):
  {{{ is_channel c closed ty P }}}
    ChanCap c
  {{{ (cap: val), RET (cap); (⌜cap = #0⌝ ∗ ⌜c = InjLV #()⌝) ∨ (∃ chanref lk, ⌜c = InjRV (cap, #chanref, lk)⌝)}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  unfold is_channel.
  iDestruct "HPre" as "[HPre | HPre]".
  - iDestruct "HPre" as "[%Hc Hty]".
    subst.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto.
  - iNamed "HPre".
    iDestruct "HPre" as "[Hchan %Hc]".
    subst.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto.
Qed.

Lemma wp_IncCap chanref (eff_cap: Z) closed ty l (P : val -> iProp Σ):
  {{{ own_chan chanref eff_cap closed ty l P}}}
      IncCap #chanref
  {{{ RET #(); own_chan chanref (int.Z (word.add 1 eff_cap)) closed ty l P}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  iDestruct "HPre" as "[%H1 [H2 H3]]".
  destruct closed.
  - wp_untyped_load.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame.
    eauto.
  - wp_untyped_load.
    wp_pures.
    wp_untyped_store.
    iApply "HΦ".
    iModIntro.
    unfold own_chan.
    rewrite u64_Z.
    iFrame.
    eauto.
Qed.

Lemma wp_DecCap chanref (eff_cap: Z) closed ty l (P : val -> iProp Σ):
  {{{ own_chan chanref eff_cap closed ty l P}}}
      DecCap #chanref
  {{{ RET #(); own_chan chanref (int.Z (word.sub eff_cap 1)) closed ty l P}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  iDestruct "HPre" as "[%H1 [H2 H3]]".
  destruct closed.
  - wp_untyped_load.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame.
    eauto.
  - wp_untyped_load.
    wp_pures.
    wp_untyped_store.
    iApply "HΦ".
    iModIntro.
    unfold own_chan.
    rewrite u64_Z.
    iFrame.
    eauto.
Qed.

Theorem wp_InnerReceive chanref eff_cap closed ty l (P : val -> iProp Σ):
  {{{ own_chan chanref eff_cap closed ty l P}}}
      InnerReceive #chanref
  {{{RET ((peek (zero_val ty) l, #(non_empty l), #(valid_return closed l))); 
      own_chan chanref eff_cap closed ty (tail l) P ∗ 
      ⌜val_ty (peek (zero_val ty) l) ty⌝ ∗ if (andb (non_empty l) (valid_return closed l)) then P (peek (zero_val ty) l) else ⌜(peek (zero_val ty) l) = zero_val ty⌝}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  unfold own_chan.
  iDestruct "HPre" as "[%H1 [H2 H3]]".
  destruct closed.
  - wp_untyped_load.
    wp_pures.
    destruct l.
    + simpl.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
      eauto.
    + simpl.
      wp_pures.
      subst.
      wp_untyped_store.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iDestruct "H3" as "[[H3 H4] H5]".
      iFrame.
      eauto.
  - wp_untyped_load.
    wp_pures.
    destruct l.
    + simpl.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
      eauto.
    + simpl.
      wp_pures.
      wp_untyped_store.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iDestruct "H3" as "[[H3 H4] H5]".
      iFrame.
      eauto.
Qed.

Theorem wp_TryReceive (chanref : loc) lk closed ty P:
    {{{ is_channel_alloc chanref lk closed ty P}}}
        TryReceive #chanref lk
    {{{(a : val) (ok : bool) (valid : bool),
        RET ((a, #(ok), #(valid))); ⌜val_ty a ty⌝ ∗ if (andb valid ok) then P a else ⌜a = zero_val ty⌝}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  iDestruct "HPre" as "#Hlock".
  wp_lam.
  wp_pures.
  wp_apply acquire_spec.
  - iFrame "Hlock".
  - iIntros "[H0 H1]".
    wp_pures.
    iNamed "H1".
    destruct closed.
    + wp_apply (wp_IncCap chanref eff_cap true ty l P with "H1").
      iIntros "H1".
      wp_pures.
      wp_apply (release_spec with "[H0 H1]").
      { unfold is_channel_alloc. iFrame "Hlock". iFrame. }
      wp_pures.
      wp_apply acquire_spec.
      { unfold is_channel_alloc. iFrame "Hlock". }
      iIntros "[H0 H1]".
      wp_pures.
      iNamed "H1".
      destruct l0.
      * wp_apply (wp_InnerReceive _ _ true _ _ _ with "[H1]").
        { iFrame. }
        iIntros "H1".
        simpl.
        wp_pures.
        iDestruct "H1" as "[H1 [H2 H3]]".
        wp_apply (wp_DecCap chanref _ _ ty _ with "[H1]").
        { iFrame. }
        iIntros "H1".
        wp_pures.
        wp_apply (release_spec with "[H0 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        simpl.
        eauto.
      * wp_apply (wp_InnerReceive chanref eff_cap0 true ty _ P with "[H1]").
        { iFrame. }
        iIntros "H1".
        wp_pures.
        iDestruct "H1" as "[H1 [H2 H3]]".
        wp_apply (wp_DecCap chanref _ _ ty _ with "[H1]").
        { iFrame. }
        iIntros "H1".
        wp_pures.
        wp_apply (release_spec with "[H0 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
    + 
      wp_apply (wp_IncCap chanref eff_cap false ty l P with "H1").
      iIntros "H1".
      wp_pures.
      wp_apply (release_spec with "[H0 H1]").
      { unfold is_channel_alloc. iFrame "Hlock". iFrame. }
      wp_pures.
      wp_apply acquire_spec.
      { unfold is_channel_alloc. iFrame "Hlock". }
      iIntros "[H0 H1]".
      wp_pures.
      iNamed "H1".
      wp_apply (wp_InnerReceive _ _ _ _ _ _ with "[H1]").
      { iFrame. }
      iIntros "H1".
      wp_pures.
      iDestruct "H1" as "[H1 [H2 H3]]".
      wp_apply (wp_DecCap chanref _ _ ty _ with "[H1]").
      { iFrame. }
      iIntros "H1".
      wp_pures.
      destruct l0.
      * wp_apply (release_spec with "[H0 H3 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        eauto.
      * simpl.
        wp_apply (release_spec with "[H0 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
Qed.

Theorem wp_ChannelReceive cap (chanref : loc) lk closed ty P:
    {{{ is_channel_alloc chanref lk closed ty P}}}
      ChannelReceive (InjRV(cap, #chanref, lk))
    {{{(a : val) (ok : bool),
      RET ((a, #(ok))); ⌜val_ty a ty⌝ ∗ if (ok) then P a else ⌜a = zero_val ty⌝}}}.
Proof.
  iIntros (Φ) "#HPre HΦ".
  wp_lam.
  wp_pures.
  iLöb as "IH" forall (Φ).
  wp_apply (wp_TryReceive with "[HPre]").
  - eauto.
  - iIntros (a open valid) "Ha".
    wp_pures.
    destruct valid.
    + wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
    + wp_pures.
      wp_apply ("IH" with "[Ha HΦ]").
      iApply "HΦ".
Qed.

Lemma wp_ChanLen' ty (l : list val):
    {{{ True }}}
        ChanLen' (chan_contents (zero_val ty) l)
    {{{(len : Z), RET (#(len)); ⌜len = length l⌝}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  wp_pures.
  iInduction l as [|] "IH" forall (Φ).
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  - wp_pures.
    wp_apply "IH".
    iIntros (len) "%Hlen".
    subst.
    wp_pures.
    iModIntro.
    rewrite -word.ring_morph_add.
    iApply "HΦ".
    iPureIntro.
    simpl.
    lia.
Qed.

Lemma wp_ChanLen c closed ty P:
  {{{ is_channel c closed ty P }}}
    ChanLen c
  {{{ (len: Z), RET #(len); (⌜#len = #0⌝ ∗ ⌜c = InjLV #()⌝) ∨ (∃ (cap: Z) chanref lk, ⌜c = InjRV (#cap, #chanref, lk)⌝ ∗ ⌜0 <= len <= cap⌝)}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  unfold is_channel.
  iDestruct "HPre" as "[HPre | HPre]".
  - iNamed "HPre".
    iDestruct "HPre" as "[%Hc %Hty]".
    subst.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto.
  - iNamed "HPre".
    iDestruct "HPre" as "[#Hlock %Hc]".
    subst.
    wp_pures.
    wp_apply acquire_spec.
    { iFrame "Hlock". }
    unfold is_channel_alloc.
    iIntros "[H0 H1]".
    wp_pures.
    iNamed "H1".
    destruct closed.
    + unfold own_chan.
      iDestruct "H1" as "[%H1 [H2 H3]]".
      wp_untyped_load.
      wp_pures.
      wp_apply wp_ChanLen'.
      iIntros (len) "%Hlen".
      wp_pures.
      wp_apply (release_spec with "[Hlock H0 H2 H3]").
      { iFrame "Hlock".
        iFrame.
        eauto.
      }
      wp_pures.
      (* wp_if_destruct. *)
  Admitted.
  (* wp_pures.
  iDestruct "HPre" as "#Hlock".
  wp_apply acquire_spec.
  - iFrame "Hlock".
  - iIntros "[H0 H1]".
    wp_pures.
    iNamed "H1".
    iDestruct "H1" as "[H1 H2]".
    destruct closed.
    + unfold own_chan.
      iDestruct "H1" as "[H1 H3]".
      wp_untyped_load.
      wp_pures.
      wp_apply (release_spec with "[Hlock H0 H1 H3 H2]").
      * iFrame "Hlock".
        iFrame.
        iNext.
        iExists _, _.
        done.
      * wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
    + unfold own_chan.
      wp_untyped_load.
      wp_pures.
      wp_apply wp_ChanLen'.
      iIntros (len) "Hlen".
      wp_pures.
      wp_apply (release_spec with "[Hlock H0 H1 H2]").
      { iFrame "Hlock".
        iFrame.
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
      Unshelve.
      { eauto. }
      eauto.
Qed. *)

Lemma wp_ChanAppend ty (l : list val) v:
    {{{ True }}}
        ChanAppend (chan_contents (zero_val ty) l) v
    {{{RET (chan_contents (zero_val ty) (l ++ [v])); True}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_lam.
  wp_pures.
  iInduction l as [|] "IH" forall (Φ).
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  - wp_pures.
    wp_apply "IH".
    unfold chan_contents.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
Qed.

Theorem wp_TrySend (chanref : loc) (v : val) lk ty P:
    {{{ is_channel_alloc chanref lk false ty P ∗ P v ∗ ⌜val_ty v ty⌝}}}
        TrySend #chanref lk v
    {{{(success : bool), RET (#(success)); if success then True else P v ∗ ⌜val_ty v ty⌝}}}.
Proof.
  iIntros (Φ) "[HPre Hv] HΦ".
  wp_lam.
  wp_pures.
  iDestruct "HPre" as "#Hlock".
  wp_apply acquire_spec.
    - iFrame "Hlock".
    - iIntros "[H0 H1]".
      wp_pures.
      iNamed "H1".
      iDestruct "H1" as "[H1 [H2 H3]]".
      wp_untyped_load.
      wp_pures.
      wp_apply wp_ChanLen'.
      iIntros (len) "Hlen".
      wp_pures.
      wp_if_destruct.
      + wp_apply wp_ChanAppend.
        wp_pures.
        wp_untyped_store.
        wp_apply (release_spec with "[Hlock Hv H0 H1 H2 H3]").
        { iFrame "Hlock H0".
          iNext.
          iExists eff_cap, (l ++ [v]).
          iFrame.
          eauto.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
      + wp_apply (release_spec with "[Hlock H0 H1 H2 H3]").
        { iFrame "H0".
          iFrame "Hlock".
          iNext.
          iExists eff_cap, l.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
Qed.

(* Try iLob induction *)
Theorem wp_ChannelSend cap (chanref : loc) (v : val) lk ty P:
    {{{ is_channel_alloc chanref lk false ty P ∗ P v ∗ ⌜val_ty v ty⌝ }}}
        ChannelSend (InjRV(cap, #chanref, lk)) v
    {{{RET #(); True}}}.
Proof.
  iIntros (Φ) "[#HPre Hv] HΦ".
  wp_lam.
  wp_pures.
  iLöb as "IH" forall (Φ).
  wp_apply (wp_TrySend with "[HPre Hv]").
  - eauto.
  - iIntros (success) "Hv".
    wp_pures.
    destruct success.
    + wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
    + wp_pures.
      wp_apply ("IH" with "Hv").
      iApply "HΦ".
      done.
Qed.

End heap.