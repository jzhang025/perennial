From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Import txn.invariant.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Section goose_lang.
Context `{!txnG Σ}.

Implicit Types (γ: @txn_names Σ).

Definition txn_init_ghost_state γ : iProp Σ :=
  let logm0 := Build_async (∅: gmap addr object) [] in
  "logheap" ∷ log_heap_ctx (hG:=γ.(txn_logheap)) logm0 ∗
  "crashstates" ∷ ghost_var γ.(txn_crashstates) 1 logm0 ∗
  "metaheap" ∷ map_ctx γ.(txn_metaheap) 1 (∅ : gmap addr gname).

Lemma alloc_txn_init_ghost_state (γtxn_walnames: wal_heap_gnames) kinds :
  ⊢ |==> ∃ γ, ⌜γ.(txn_walnames) = γtxn_walnames⌝ ∗
              ⌜γ.(txn_kinds) = kinds⌝ ∗
              txn_init_ghost_state γ.
Proof.
  set (logm:=Build_async (∅: gmap addr object) []).
  iMod (seq_heap_init logm) as (txn_logheap) "[? _]".
  iMod (ghost_var_alloc logm) as (txn_crashstates) "?".
  iMod (map_init (∅ : gmap addr gname)) as (txn_metaheap) "?".
  iModIntro.
  iExists (Build_txn_names _ _ _ _ _ _).
  rewrite /txn_init_ghost_state /=.
  by iFrame.
Qed.

(* Definitely missing the durable invariant of the heapspec layer, which should
say something more complete about [γ.(txn_walnames)]. Otherwise there probably
isn't enough to relate the state inside [is_txn_always] to that in
[is_wal_inner_durable]. *)

Definition is_txn_durable γ dinit : iProp Σ :=
  ∃ ls' logm crash_heaps,
  "His_wal_inner_durable" ∷ is_wal_inner_durable γ.(txn_walnames).(wal_heap_walnames) ls' dinit ∗
  "Hwal_res" ∷ wal_resources γ.(txn_walnames).(wal_heap_walnames) ∗
  "Hwal_heap_inv" ∷ wal_heap_inv γ.(txn_walnames) ls' ∗
  "Hlocked_walheap" ∷ is_locked_walheap γ.(txn_walnames) {| locked_wh_σd := ls'.(log_state.d);
                        locked_wh_σtxns := ls'.(log_state.txns);
                    |} ∗
  "His_txn_always" ∷ is_txn_state γ logm crash_heaps ∗
  (* ⌜ lb < length ls'.(log_state.txns) ⌝%nat ∗ *)
  (* XXX this is already in is_txn_state
     "Hcrash_heaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (3/4) crash_heaps ∗ *)
  "Hgh_ptsto" ∷ ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
    ⌜hb_latest_update hb = b⌝ ∗
    mapsto (hG:=γ.(txn_walnames).(wal_heap_h)) a 1 hb).

Definition txn_pre_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ'.(txn_crashstates) (3/4) σs ∗
              heapspec_durable_exchanger γ.(txn_walnames) (length (possible σs) - 1)).

Definition txn_post_exchange γ γ' : iProp Σ :=
 (∃ σs : async (gmap addr object), "H◯async" ∷ ghost_var γ.(txn_crashstates) (3/4) σs).

Definition txn_exchanger (γ γ' : @txn_names Σ) : iProp Σ :=
  ∃ ls ls', heapspec_exchanger ls ls' γ.(txn_walnames) γ'.(txn_walnames) ∗
  (txn_pre_exchange γ γ' ∨ txn_post_exchange γ γ').

Global Instance is_txn_always_discretizable γ :
  Discretizable (is_txn_always γ).
Proof. apply _. Qed.

Global Instance is_txn_durable_discretizable γ dinit :
  Discretizable (is_txn_durable γ dinit).
Proof. apply _. Qed.

Lemma log_crash_txns_length ls1 ls2 :
  relation.denote log_crash ls1 ls2 () →
  (length ls2.(log_state.txns) ≤ length ls1.(log_state.txns))%nat.
Proof.
  rewrite log_crash_unfold. intros (?&?&?).
  subst. rewrite /=.
  rewrite -{2}(take_drop (S x) (ls1.(log_state.txns))).
  rewrite app_length. lia.
Qed.

Lemma wal_heap_inv_wf names ls:
  wal_heap_inv names ls -∗
  ⌜ wal_wf ls ⌝.
Proof. iNamed 1. eauto. Qed.

Theorem wpc_MkTxn (d:loc) dinit (γ:txn_names) logm k :
  {{{ is_txn_durable γ dinit ∗ ghost_var γ.(txn_crashstates) (3/4) logm }}}
    MkTxn #d @ k; ⊤
  {{{ (l: loc), RET #l; is_txn l γ dinit ∗ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ a v)
      (* cfupd stuff *) }}}
  {{{ is_txn_durable γ dinit ∗ ghost_var γ.(txn_crashstates) (3/4) logm  ∨
      (∃ γ', ⌜ txn_kinds γ' = txn_kinds γ ⌝ ∗ is_txn_durable γ' dinit ∗ txn_exchanger γ γ') }}}.
Proof.
  iIntros (Φ Φc) "(Hdur&Hlogm) HΦ".
  rewrite /MkTxn. wpc_pures.
  { crash_case. iLeft; by iFrame. }

  iCache with "Hdur HΦ Hlogm".
  { crash_case. iLeft; by iFrame. }
  wpc_bind (lock.new _).
  wpc_frame; wp_apply (wp_new_free_lock).
  iIntros (lk) "Hlock". iNamed 1.
  wpc_bind (MkLog #d).
  iNamed "Hdur".
  iMod (alloc_heapspec_init_ghost_state (γ.(txn_walnames).(wal_heap_walnames)))
         as (γ'_txn_walnames ?) "Hheapspec_init".
  iMod (alloc_txn_init_ghost_state γ'_txn_walnames γ.(txn_kinds)) as
      (γ' Hwalnames_eq Hkinds_eq) "Htxn_init".
  set (P := λ ls, (wal_heap_inv γ.(txn_walnames) ls ∗ heapspec_init_ghost_state γ'_txn_walnames)%I).
  set (Prec (ls ls': log_state.t) :=
         (wal_heap_inv γ'.(txn_walnames) ls' ∗
          heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) ls ls')%I).
  set (Pcrash (ls ls' : log_state.t) := (True)%I : iProp Σ).
  iApply wpc_cfupd.
  wpc_apply (wpc_MkLog_recover dinit P _ _ _ _ Prec Pcrash
            with "[] [$His_wal_inner_durable Hwal_res Hwal_heap_inv Hheapspec_init]").
  - iIntros "!>" (???) ">HP".
    iDestruct "HP" as "[Hinv Hinit]".
    iMod (wal_heap_inv_crash_transform with "Hinv Hinit") as "[Hinv Hres]"; eauto.
    rewrite /Prec /Pcrash.
    rewrite Hwalnames_eq.
    iModIntro.
    by iFrame.
  - iFrame.
  - iSplit.
    { iLeft in "HΦ".
      iModIntro.
      iIntros "Hcrash".
      iModIntro.
      iApply "HΦ".
      iDestruct "Hcrash" as (ls2) "[HP|HP]".
      - iDestruct "HP" as "(Hdur' & Hres' & HP)".
        iLeft. iFrame "Hlogm".
        iExists _. iFrame "Hdur' Hres'".
        admit.
      - iDestruct "HP" as (ls1 γ'walnames Hcrashls12) "(Hdur' & Hres' & HP)".
        iNamed "His_txn_always".

        iAssert (C -∗ |0={⊤}=>
                  ∃ γ'0, ⌜γ'0.(txn_kinds) = γ.(txn_kinds)⌝ ∗ is_txn_durable γ'0 dinit ∗ txn_exchanger γ γ'0)%I
        with "[-]" as "Hgoal".
        {

        rewrite /Prec. iDestruct "HP" as "(>Hheap_inv&Hheap_res)".
        rewrite /is_txn_durable.
        iIntros "C".
        iExists (γ'<|txn_walnames;wal_heap_walnames := γ'walnames|>). iSplitL ""; first eauto.

        iClear "Hlocked_walheap".
        rewrite /heapspec_resources.
        iDestruct "Hheap_res" as "(>Hheap_exchanger&>Hlocked_walheap)".
        iDestruct (heapspec_exchange_crash_heaps with "[$] [$]") as "(Hheap_exchange&Hnew)".
        iDestruct "Hnew" as "(Hheap_lb_exchange&Hcrash_heaps0)".
        iNamed "Hcrash_heaps0".

        iDestruct (wal_heap_inv_wf with "Hheap_inv") as %Hls2wf.
        iNamed "Htxn_init".
        iDestruct (ghost_var_agree with "Hcrashstates Hlogm") as %->.
        iDestruct (big_sepL2_length with "Hcrashheapsmatch") as %Hlen_logm.
        iMod (ghost_var_update (async_take (length ls2.(log_state.txns)) logm) with "crashstates")
             as "crashstates".
        iEval (rewrite -Qp_quarter_three_quarter) in "crashstates".
        iDestruct (fractional.fractional_split_1 with "crashstates") as
            "[crashstates1 crashstates2]".
        iDestruct (heapspec_durable_exchanger_dup with "[$]")
                  as "(Hheap_lb_exchange1&Hheap_lb_exchange2)".
        iSplitR "crashstates2 Hheap_lb_exchange2 Hheap_exchange"; last first.
        { iModIntro. rewrite /txn_exchanger. iFrame.
          iExists _, _. iFrame.
          iLeft.
          rewrite /txn_pre_exchange. iExists _.
          iFrame.
          iExactEq "Hheap_lb_exchange2".
          f_equal. rewrite /async_take.
          assert (length ls2.(log_state.txns) ≤ length (possible logm))%nat.
          { rewrite Hlen_logm -Hlenold //=.
            apply log_crash_txns_length. auto. }
          rewrite possible_list_to_async //=; len.
          destruct Hls2wf. lia.
        }
        iExists ls2, _, _. simpl. iFrame "Hheap_inv Hres' Hdur'".

        iFrame "Hcrash_heaps".
        iFrame.
        (*
        { iExists _. iFrame. eauto. }
         *)

        rewrite /is_txn_always/is_txn_state.
        (* this is a bunch of work *)
        admit. }
        (* TODO: need to fix up modalities so assert above makes sense *)
        admit. }

    iNext. iIntros (γ'' l) "(#Hwal & Hwal_cfupd & #Hwal_cinv)".
    wpc_frame_compl "Hlock Hlocked_walheap His_txn_always".
    { admit. }
    rewrite -wp_fupd.
    wp_apply wp_allocStruct; first by val_ty.
    iIntros (txn_l) "Htxn".
    iApply struct_fields_split in "Htxn". iNamed "Htxn".
    wp_pures.
    iMod (readonly_alloc_1 with "mu") as "#mu".
    iMod (readonly_alloc_1 with "log") as "#log".
    iMod (alloc_lock lockN _ _ (is_txn_locked txn_l γ.(txn_walnames))
            with "Hlock [pos Hlocked_walheap]") as "#Htxn_lock".
    { iNext. rewrite /is_txn_locked.
      iExists _, _, _; iFrame. }
    iMod (inv_alloc invN _ (is_txn_always γ) with "[His_txn_always]") as "#Htxn_inv".
    { iNext. iExists _, _; iFrame. }
    iModIntro.
    iNamed 1.
    iRight in "HΦ".
    iApply "HΦ".
    iSplitR ""; last first.
    { admit. (* TODO: get mapsto_txn facts from allocating all of them *) }
    rewrite /is_txn.
    iExists _, _; iFrame "#".
    iApply (is_wal_alter with "Hwal").
    iModIntro. iClear "#".
    rewrite /P.
    iIntros (?) "[$ $]".
    iIntros (?) "$".
    all: fail "goals remaining".
Admitted.

End goose_lang.
