From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config2.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof std_proof.
From Perennial.program_proof.simplepb Require Import config_marshal_proof renewable_lease.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From Perennial.program_proof.mpaxos Require Import tryacquire_proof weakread_proof.

Module state.
Section state.
Record t :=
  mk {
      epoch : u64 ;
      reservedEpoch : u64 ;
      leaseExpiration : u64 ;
      wantLeaseToExpire : bool ;
      config : list u64 ;
    }.

Definition encode (x:t) : list u8.
Admitted.

Global Instance encode_inj : Inj eq eq encode.
Proof.
Admitted.

Context `{!heapGS Σ}.
Definition own (l:loc) (x:t) : iProp Σ :=
  ∃ conf_sl,
  "Hepoch" ∷ l ↦[state :: "epoch"] #x.(epoch) ∗
  "HreservedEpoch" ∷ l ↦[state :: "reservedEpoch"] #x.(reservedEpoch) ∗
  "HleaseExpiration" ∷ l ↦[state :: "leaseExpiration"] #x.(leaseExpiration) ∗
  "HwantLeaseToExpire" ∷ l ↦[state :: "wantLeaseToExpire"] #x.(wantLeaseToExpire) ∗
  "Hconf" ∷ l ↦[state :: "config"] (slice_val conf_sl) ∗
  "#Hconf_sl" ∷ readonly (own_slice_small conf_sl uint64T 1 x.(config))
.

Lemma wp_decode (x:t) sl q :
  {{{
        own_slice_small sl byteT q (encode x)
  }}}
    decodeState (slice_val sl)
  {{{
        l, RET #l; own l x
  }}}
.
Proof.
Admitted.

Lemma wp_encode l (x:t) :
  {{{
        own l x
  }}}
    encodeState #l
  {{{
        sl, RET (slice_val sl);  own_slice_small sl byteT 1 (encode x) ∗
        own l x
  }}}
.
Proof.
Admitted.

End state.
End state.

Module configParams.
Class t Σ :=
  mk {
      config:list mp_server_names ;
      Pwf:list u64 → iProp Σ ;
      N: namespace ;
    }.
End configParams.
Import configParams.

Section config_global.

Record config_names :=
{
  epoch_gn:gname ;
  repoch_gn:gname ;
  config_val_gn:gname;
}.

Class configG Σ := {
    config_configG :> ghost_varG Σ (list u64) ;
    config_urpcG :> urpcregG Σ ;
    config_epochG :> mono_natG Σ ;
    config_mpG :> mpG Σ ;
    config_leaseG :> renewable_leaseG Σ ;
}.

Definition configΣ := #[mono_natΣ ; ghost_varΣ (list u64) ; urpcregΣ ; renewable_leaseΣ ].

Global Instance subG_configΣ {Σ} : subG configΣ Σ → configG Σ.
Proof. intros. (* solve_inG. Qed. *)
       Admitted. (* FIXME: mpΣ *)

Implicit Type γ : config_names.

Context `{!gooseGlobalGS Σ}.
Context `{!configG Σ}.
Context `{params:!configParams.t Σ}.

Definition own_latest_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (int.nat epoch).

Definition own_reserved_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(repoch_gn) (1/2) (int.nat epoch).

Definition is_reserved_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(repoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  ghost_var γ.(config_val_gn) (1/2) conf
.

Definition epochLeaseN := N .@ "epochLeaseN".

Program Definition ReserveEpochAndGetConfig_core_spec γ Φ :=
  (
    £ 1 -∗
    (|={⊤∖↑N,∅}=> ∃ reservedEpoch conf, own_reserved_epoch γ reservedEpoch ∗ own_config γ conf ∗
    (⌜int.nat reservedEpoch < int.nat (word.add reservedEpoch (U64 1))⌝ -∗
      own_reserved_epoch γ (word.add reservedEpoch (U64 1)) -∗ own_config γ conf ={∅,⊤∖↑N}=∗
      Φ (word.add reservedEpoch 1) conf
      ))
    )%I.

Program Definition GetConfig_core_spec γ Φ :=
  (∀ conf, Pwf conf -∗ Φ conf)%I.

Program Definition TryWriteConfig_core_spec γ (epoch:u64) (new_conf:list u64) Φ : iProp Σ :=
  is_reserved_epoch_lb γ epoch ∗
  (□ Pwf new_conf) ∗
  (£ 1 -∗ |={⊤∖↑N,∅}=> ∃ latest_epoch reserved_epoch conf,
   own_latest_epoch γ latest_epoch ∗
   own_reserved_epoch γ reserved_epoch ∗
   own_config γ conf ∗
   (⌜ reserved_epoch = epoch ⌝ -∗
    own_config γ new_conf -∗
    own_reserved_epoch γ reserved_epoch -∗
    own_latest_epoch γ epoch ={∅,⊤∖↑N}=∗ Φ (U64 0))
  ) ∗
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err)
.

Program Definition GetLease_core_spec γ (epoch:u64) Φ : iProp Σ :=
  (∀ (leaseExpiration:u64) γl,
    is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
    is_lease_valid_lb γl leaseExpiration -∗ Φ (U64 0) leaseExpiration
  ) ∧
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err (U64 0))
.

Program Definition ReserveEpochAndGetConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    ReserveEpochAndGetConfig_core_spec γ (λ newEpoch conf,
                                  ∀ enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   Φ (u64_le 0 ++ u64_le newEpoch ++ enc_conf)
                                  ) ∗
    (∀ err, ⌜ err ≠ U64 0 ⌝ -∗ Φ (u64_le err))
    )%I.
Next Obligation.
  rewrite /ReserveEpochAndGetConfig_core_spec.
  solve_proper.
Defined.

Program Definition GetConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    GetConfig_core_spec γ (λ conf, ∀ reply,
                                   ⌜Config.has_encoding reply conf⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  solve_proper.
Defined.

Program Definition TryWriteConfig_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( ∃ epoch new_conf enc_new_conf,
    ⌜enc_args = u64_le epoch ++ enc_new_conf⌝ ∗
    ⌜Config.has_encoding enc_new_conf new_conf⌝ ∗
    TryWriteConfig_core_spec γ epoch new_conf (λ err, ∀ reply,
                                   ⌜reply = u64_le err⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  unfold TryWriteConfig_core_spec.
  solve_proper.
Defined.

Program Definition GetLease_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( ∃ epoch ,
    ⌜enc_args = u64_le epoch⌝ ∗
    GetLease_core_spec γ epoch (λ (err:u64) (leaseExpiration:u64), ∀ reply,
                                   ⌜reply = u64_le err ++ u64_le leaseExpiration⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  unfold GetLease_core_spec.
  solve_proper.
Defined.

Definition is_config_host (host:u64) γ : iProp Σ :=
  ∃ γrpc,
  is_urpc_spec_pred γrpc host (U64 0) (ReserveEpochAndGetConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 1) (GetConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 2) (TryWriteConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 3) (GetLease_spec γ) ∗
  is_urpc_dom γrpc {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ]}
.

End config_global.

Section config_proof.

Context `{!heapGS Σ}.
Context `{!configG Σ}.
Context `{params:configParams.t Σ}.

Definition own_Config_ghost γ (st:state.t) : iProp Σ :=
  ∃ γl,
  "Hconf_ghost" ∷ own_config γ st.(state.config) ∗
  "Hreserved_ghost" ∷ own_reserved_epoch γ st.(state.reservedEpoch) ∗
  "Hlatest_epoch" ∷ post_lease epochLeaseN γl (own_latest_epoch γ st.(state.epoch)) ∗
  "HleaseExp" ∷ own_lease_expiration γl st.(state.leaseExpiration) ∗
  "%HresIneq" ∷ ⌜ int.nat st.(state.epoch) <= int.nat st.(state.reservedEpoch) ⌝
.

Definition configWf (a:list u8) : iProp Σ :=
  ∃ st, ⌜ a = state.encode st ⌝ ∗ □ Pwf st.(state.config)
.

Definition configN := N .@ "paxos".
Definition configPaxosN := configN .@ "paxos".
Definition configInvN := configN .@ "inv".

Instance c : mpaxosParams.t Σ :=
  mpaxosParams.mk Σ config configWf configPaxosN.

Definition is_config_inv γ γst : iProp Σ :=
  inv configInvN (∃ st,
        "Hst" ∷ own_state γst (state.encode st) ∗
        "Hghost" ∷ own_Config_ghost γ st
      )
.

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (p:loc) γp γsrv γst,
  "#Hs" ∷ readonly (s ↦[config2.Server :: "s"] #p) ∗
  "#Hsrv" ∷ is_Server p γp γsrv ∗
  "#Hst_inv" ∷ is_state_inv γst γp ∗
  "#Hconfig_inv" ∷ is_config_inv γ γst
.

Definition own_tryRelease (f:val) γ (st_ptr:loc) (oldst:state.t) : iProp Σ :=
  ∀ (newst:state.t) Φ,
  (
    "Hvol" ∷ state.own st_ptr newst ∗
    "#Hwf" ∷ □ Pwf newst.(state.config) ∗
    "Hupd" ∷ (own_Config_ghost γ oldst ={⊤∖↑configN}=∗ own_Config_ghost γ newst ∗ Φ #true)
  ) -∗
  (Φ #false) -∗
  WP f #() {{ Φ }}
.

Lemma wp_Server__tryAcquire s γ :
  {{{
        is_Server s γ
  }}}
    config2.Server__tryAcquire #s
  {{{
        (ok:bool) (st_ptr:loc) (f:val), RET (#ok, #st_ptr, f);
        if ok then
          ∃ st,
          □ Pwf st.(state.config) ∗
          state.own st_ptr st ∗
          own_tryRelease f γ st_ptr st
        else
          True
  }}}
.
Proof.
  iIntros (Φ) "Hsrv HΦ".
  wp_lam.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Server__TryAcquire with "[$]").
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  {
    iClear "Hpost".
    wp_apply wp_ref_of_zero.
    { done. }
    iIntros (?) "Hl".
    wp_pures. wp_load.
    wp_pures.
    iApply "HΦ".
    done.
  }
  setoid_rewrite decide_True.
  2:{ done. }
  iDestruct "Hpost" as (??) "(Hsl_ptr & #Hsl & HP & Hwp)".
  wp_load.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  iDestruct "HP" as (?) "[%Henc #HP]".
  subst.
  wp_apply (state.wp_decode with "[$Hsl2]").
  iIntros (?) "Hst".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _; iFrame "∗#".
  clear.
  iIntros (??). iNamed 1.
  iIntros "HΦ".
  wp_pures.
  wp_apply (state.wp_encode with "[$]").
  iClear "Hsl".
  iIntros (?) "[Hsl _]".
  wp_pure1_credit "Hlc".
  wp_store.
  iMod (readonly_alloc_1 with "Hsl") as "Hsl".
  wp_apply ("Hwp" with "[-HΦ]").
  {
    iFrame "∗#".
    iSplitR.
    { iModIntro. iExists _; iFrame "#%". done. }
    iInv "Hconfig_inv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame.
    iIntros "%Heq".
    eapply inj in Heq.
    2:{ apply _. }
    subst.
    iIntros "Hst".
    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("Hupd" with "[$]") as "[Hghost Hupd]".
    { simpl. solve_ndisj. }
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hghost Hst]").
    { repeat iExists _; iFrame. }
    iModIntro.
    wp_pures.
    iApply "Hupd".
  }
  {
    iIntros.
    wp_pures.
    rewrite bool_decide_false.
    { iApply "HΦ". }
    naive_solver.
  }
Qed.

Lemma wp_Server__ReserveEpochAndGetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config2.Server__ReserveEpochAndGetConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (ReserveEpochAndGetConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.

  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (rep_sl) "Hrep_sl".
  wp_store.
  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros (???) "Hpost".
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* if not ok from tryAcquire *)
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "$".
    iFrame.
    Opaque u64_le.
    rewrite /ReserveEpochAndGetConfig_spec /ReserveEpochAndGetConfig_core_spec /=.
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
  iNamed "Hvol".
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros "%HnoOverflow".
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.
  iDestruct "HΨ" as "[HΨ1 Hfail]".
  wp_bind (f #()).
  wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl]").
  { iNamedAccu. }
  wp_apply ("Hwp" with "[-Hfail] [Hfail]").
  {
    iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf Hconf_sl".
    {
      instantiate (1:=state.mk _ _ _ _ _).
      repeat iExists _; simpl; iFrame "∗#".
    }
    iSplitR.
    { simpl.  iFrame "#". }
    iIntros "Hghost".

    (* start ghost reasoning *)
    iNamed "Hghost".
    rewrite /ReserveEpochAndGetConfig_core_spec.
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("HΨ1" with "[$]") as (??) "(Hres & Hconf & Hupd)".
    { solve_ndisj. }
    iCombine "Hconf Hconf_ghost" gives %[_ H]. subst.

    rewrite /own_reserved_epoch.
    iDestruct (mono_nat_auth_own_agree with "Hres [$]") as %[? H].
    apply Z2Nat.inj in H; try word.
    eapply (inj (R:=eq)) in H.
    2:{ apply _. }
    subst.
    iCombine "Hres Hreserved_ghost" as "Hres".
    (* FIXME: combine instance for mono_nat_auth_own *)
    iMod (mono_nat_own_update with "Hres") as "[[Hres1 Hres2] _]".
    { shelve. }
    iMod ("Hupd" with "[%] [$] [$]") as "HΨ".
    { word. }
    Unshelve.
    2:{ word. }
    iMod "Hmask".
    iModIntro.
    rewrite sep_exist_r. iExists _.
    iFrame.
    iSplitR.
    { iPureIntro. simpl. word. }
    (* end ghost reasoning *)

    iNamed 1.

    wp_pures.

    iClear "Hrep_sl".
    wp_apply (wp_slice_len).
    wp_apply (wp_NewSliceWithCap).
    { apply encoding.unsigned_64_nonneg. }
    iIntros (ptr) "Hsl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (enc_sl) "Hrep_sl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_apply (Config.wp_Encode with "[Hconf_sl]").
    { iFrame "#". }
    iIntros (enc_conf enc_conf_sl) "(%Hconf_enc & _ & Henc_conf_sl)".
    wp_load.
    wp_apply (wp_WriteBytes with "[$Hrep_sl Henc_conf_sl]").
    {
      iDestruct (own_slice_to_small with "Henc_conf_sl") as "$".
    }
    iIntros (?) "[Hrep_sl Henc_conf_sl]".
    replace (int.nat 0%Z) with 0%nat by word.
    wp_store.
    iApply "HΦ".
    iFrame "Hrep".
    iDestruct (own_slice_to_small with "Hrep_sl") as "?".
    iFrame.
    iModIntro.
    simpl.
    iApply "HΨ".
    done.
  }
  {
    simpl.
    iNamed 1.
    wp_pures.
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    iApply "Hfail".
    done.
  }
Qed.

Lemma wp_Server__GetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config2.Server__GetConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (GetConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.

  iNamed "His_srv".
  wp_loadField.
  wp_apply (wp_Server__WeakRead with "[$]").
  iIntros (??) "[#Hsl HP]".
  cbn.
  iDestruct "HP" as (?) "[%H HP]".
  subst.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  wp_apply (state.wp_decode with "[$]").
  iIntros (?) "Hvol".
  wp_pures.
  iNamed "Hvol".
  wp_loadField.
  wp_apply (Config.wp_Encode with "[$]").
  iIntros (??) "(%Henc & _ & Henc)".
  wp_store.
  iDestruct (own_slice_to_small with "Henc") as "Henc".
  iApply "HΦ".
  iFrame.
  iApply ("HΨ" with "HP [//]").
Qed.

Lemma wp_Server__TryWriteConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config2.Server__TryWriteConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (TryWriteConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.
  iDestruct "HΨ" as (new_epoch new_conf enc_new_conf) "(%Henc & %Henc_conf & HΨ)".
  rewrite Henc.
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_pure1_credit "Hlc".
  wp_pures.
  wp_apply (Config.wp_Decode with "[$Hargs_sl]").
  { done. }
  iIntros (?) "Hconf_own".
  wp_pures.
  wp_forBreak.
  wp_pures.

  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros (???) "Hpost".
  wp_pures.
  iDestruct "HΨ" as "(#Hepoch_lb & #HP_new & HΨ)".
  wp_if_destruct.
  {
    iModIntro.
    iRight. iSplitR; first done.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    simpl.
    iRight in "HΨ".
    iApply "HΨ".
    2:{ done. }
    { done. }
  }
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
  iNamed "Hvol".
  wp_loadField.
  wp_if_destruct.
  { (* case: higher epoch is reserved *)
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep_sl Hrep]").
    { iNamedAccu. }
    wp_apply ("Hwp" with "[-]").
    { (* case: committed update, which was actually not even an update. *)
      iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf".
      { repeat iExists _; iFrame "∗#". }
      iFrame "#".
      iIntros "$ !#".
      iNamed 1.
      wp_pures.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iIntros (rep_sl) "Hrep_sl2".
      wp_store.
      iModIntro.
      iRight. iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl2") as "Hrep_sl2".
      iFrame. simpl.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
    { (* case: (non-)update failed to be committed *)
      iNamed 1.
      wp_pures.
      iModIntro.
      iRight. iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame. simpl.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
  wp_loadField.
  wp_if_destruct.
  { (* case: try to enter new epoch *)
    wp_apply wp_GetTimeRange.
    iIntros "* % % Htime".
    iDestruct (own_time_get_lb with "Htime") as "#Hlb".
    iModIntro.
    iFrame "Htime".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { (* case: lease is expired, so can activate new epoch right now *)
      wp_storeField.
      wp_storeField.
      wp_storeField.
      iClear "Hconf_sl".
      rewrite /Config.own.
      iNamed "Hconf_own".
      iDestruct "Hargs_state_sl" as "#Hconf_sl".
      iDestruct "HΨ" as "[HΨ Hfail]".
      wp_bind (f #()).
      wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl]"); first iNamedAccu.
      wp_apply ("Hwp" with "[-Hfail]").
      { (* case: committed update. *)
        iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf".
        {
          instantiate (1:=state.mk _ _ _ _ _).
          repeat iExists _; simpl; iFrame "∗#".
        }
        simpl.
        iFrame "#".

        (* start ghost reasoning *)
        iIntros "Hghost".
        iNamed "Hghost".
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod (lease_expire with "[$] [$] []") as ">Hepoch_ghost".
        { solve_ndisj. }
        { iApply (is_time_lb_mono with "[$]"). word. }
        iMod "Hmask" as "_".
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod ("HΨ" with "Hlc") as "HΨ".
        { solve_ndisj. }
        iDestruct "HΨ" as (???) "(Hepoch_ghost2 & Hres2 & Hconf_ghost2 & Hupd)".
        iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
        assert (reserved_epoch = st.(state.reservedEpoch)) by word; subst.
        iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
        assert (latest_epoch = st.(state.epoch)) by word; subst.
        iCombine "Hepoch_ghost Hepoch_ghost2" as "Hepoch_ghost".
        iMod (mono_nat_own_update (int.nat new_epoch) with "Hepoch_ghost") as "[[Hepoch_ghost Hepoch_ghost2] _]".
        { word. }
        iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
        iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
        iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
        iDestruct (mono_nat_lb_own_valid with "Hreserved_ghost Hepoch_lb") as %[_ Hineq].
        iMod ("Hupd" with "[] Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
        { iPureIntro. word. }
        iMod "Hmask" as "_".
        clear γl.
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod (lease_alloc _ epochLeaseN with "Hepoch_ghost") as (?) "(_ & Hlatest_epoch & HleaseExp)".
        { solve_ndisj. }
        iMod "Hmask" as "_".
        iModIntro.
        repeat rewrite sep_exist_r.
        repeat iExists _.
        iFrame.
        iSplitR.
        { iPureIntro. simpl. word. }
        (* end ghost reasoning *)

        iNamed 1.
        wp_pures.
        wp_apply (wp_WriteInt with "[]").
        { iApply own_slice_zero. }
        iClear "Hrep_sl".
        iIntros (?) "Hrep_sl".
        wp_store. iModIntro.
        iRight. iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame. iApply "HΨ". done.
      }
      { (* case: unable to commit update *)
        iNamed 1.
        wp_pures.
        iRight. iModIntro.
        iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame.
        iApply "Hfail"; last done; done.
      }
    }
    { (* case: lease is not expired, so mark that we want to expire it and sleep *)
      wp_storeField.
      wp_loadField.
      wp_pures.
      iDestruct "HΨ" as "[HΨ Hfail]".
      wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl Hfail]"); first iNamedAccu.
      wp_apply ("Hwp" with "[-]").
      { (* rsm update successful *)
        repeat rewrite sep_exist_r.
        instantiate (1:=state.mk _ _ _ _ _).
        iExists _; simpl; iFrame "∗#".
        iIntros "$ !#".
        wp_pures.
        wp_apply wp_Sleep.
        wp_pures.
        iModIntro.
        iNamed 1.
        iLeft.
        iSplitR; first done.
        iFrame.
      }
      { (* unable to update rsm *)
        wp_pures.
        iModIntro.
        iNamed 1.
        iRight. iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame.
        iApply "Hfail"; last done; done.
      }
    }
  }
  { (* case: already entered the new epoch *)
    wp_storeField.
    iDestruct "HΨ" as "[HΨ Hfail]".
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΦ Hfail Hrep Hrep_sl]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* case: successful paxos write *)
      repeat rewrite sep_exist_r.
      instantiate (1:=state.mk _ _ _ _ _).
      iExists _; simpl; iFrame "∗#".
      iIntros "Hghost".
      iNamed "Hghost".
      iMod (post_lease_acc with "Hlatest_epoch") as "[>Hlatest_epoch Hclose]".
      { solve_ndisj. }
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod ("HΨ" with "[$]") as "HΨ".
      { solve_ndisj. }
      iDestruct "HΨ" as (???) "(Hepoch_ghost2 & Hres2 & Hconf_ghost2 & HΨ)".
      iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
      assert (reserved_epoch = st.(state.reservedEpoch)) by word; subst.
      iDestruct (mono_nat_auth_own_agree with "Hlatest_epoch Hepoch_ghost2") as %[_ ?].
      assert (latest_epoch = st.(state.epoch)) by word; subst.
      iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
      iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
      iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
      replace (new_epoch) with (st.(state.epoch)) by word.
      iMod ("HΨ" with "[] Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
      { iPureIntro. word. }
      iMod "Hmask".
      iMod ("Hclose" with "[$]") as "Hlatest_epoch".
      iModIntro.
      repeat rewrite sep_exist_r.
      iExists _; simpl; iFrame "∗#".
      iSplitR.
      { iPureIntro. word. }
      iNamed 1.
      wp_pures.
      iClear "Hrep_sl".
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro. iRight.
      iSplitR; first done.
      wp_pures.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ".
      iFrame.
      iApply "HΨ". done.
    }
    { (* case: paxos write failed *)
      iNamed 1.
      wp_pures.
      iModIntro. iRight.
      iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iApply "Hfail"; last done; done.
    }
  }
Qed.

Lemma wp_Server__GetLease (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config2.Server__GetLease #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (GetLease_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.
  iDestruct "HΨ" as (?) "[% HΨ]".
  subst.
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_load.
  wp_apply (wp_WriteInt with "[$Hrep_sl]").
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (?) "Hargs_sl".
  wp_pures.
  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  { (* case: not leader *)
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    iRight in "HΨ".
    iApply "HΨ"; last done.
    done.
  }
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
  iNamed "Hvol".
  wp_loadField.
  wp_apply (wp_or with "[HwantLeaseToExpire]").
  { iNamedAccu. }
  { wp_pures. iPureIntro. by rewrite -bool_decide_not. }
  { iIntros. wp_loadField. iFrame. iPureIntro.
    repeat f_equal.
    instantiate (2:=(st.(state.wantLeaseToExpire) = true)).
    Unshelve. 2:{ apply _. }
    by destruct st, wantLeaseToExpire.
  }
  iNamed 1.
  wp_if_destruct.
  { (* case: epoch number that the caller wants is not the latest epoch, or wantToExpireLease *)
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep_sl Hrep]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* case: committed (non-)update *)
      repeat rewrite sep_exist_r.
      repeat iExists _. iFrame "∗#".
      iIntros "$ !#".
      wp_pures.
      iNamed 1.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_store.
      wp_load.
      wp_apply (wp_WriteInt with "[$Hrep_sl]").
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
    {
      iNamed 1.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
  { (* case: epoch matches *)

    assert (epoch = st.(state.epoch)); last subst.
    {
      apply Decidable.not_or in Heqb.
      destruct Heqb as [? ?].
      apply dec_stable in H.
      by injection H.
    }
    wp_apply wp_GetTimeRange.
    iIntros "* % % $".
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_bind (if: #_ then _ else _)%E.
    wp_apply (wp_wand with "[HleaseExpiration]").
    {
      instantiate (1:=(λ _, ∃ (newLeaseExpiration:u64),
                        "%Hineq1" ∷ ⌜ int.nat st.(state.leaseExpiration) <= int.nat newLeaseExpiration⌝ ∗
                        "%Hineq2" ∷ ⌜ int.nat (word.add l 1000000000%Z) <=
                          int.nat newLeaseExpiration⌝ ∗
                        "HleaseExpiration" ∷ st_ptr ↦[state :: "leaseExpiration"] #newLeaseExpiration )%I).
      wp_if_destruct.
      {
        wp_storeField.
        iExists _; iFrame. iPureIntro.
        split.
        { apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia. }
        { apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia. }
      }
      { iExists _; iFrame. iPureIntro.
        split; first done.
        apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia.
      }
    }
    iIntros (?).
    iNamed 1.
    wp_pures.
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep Hrep_sl]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* successfully commit paxos write *)
      repeat rewrite sep_exist_r.
      instantiate (1:=state.mk _ _ _ _ _).
      Opaque u64_le.
      iExists _; simpl.
      iFrame "∗#".
      Transparent u64_le.

      (* start ghost reasoning *)
      iNamed 1.
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod (lease_renew newLeaseExpiration with "[$] [$]") as "[Hlatest_epoch HleaseExp]".
      { solve_ndisj. }
      { word. }
      iMod "Hmask" as "_".
      iDestruct (post_get_lease with "[$]") as "#Hlease".
      iDestruct (lease_get_lb with "[$]") as "#Hlb".
      iDestruct (lease_lb_mono with "[$]") as "#Hlb2".
      { exact Hineq2. }
      iClear "Hlb".
      repeat rewrite sep_exist_r.
      iExists _. iFrame.
      iSplitR.
      { iPureIntro. simpl. done. }
      iModIntro.
      (* end ghost reasoning *)

      iNamed 1.
      iLeft in "HΨ".
      iDestruct ("HΨ" with "[$] [$]") as "HΨ".
      wp_pures.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_store.
      wp_load.
      wp_apply (wp_WriteInt with "[$Hrep_sl]").
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iApply "HΨ".
      iPureIntro. done.
    }
    { (* case: paxos write failed *)
      iNamed 1.
      wp_pures.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
Qed.

Definition own_Clerk_inv (ck:loc) l : iProp Σ :=
  ∃ (leader:u64),
  "Hleader" ∷ ck ↦[config2.Clerk :: "leader"] #leader ∗
  "%HleaderBound" ∷ ⌜ int.nat leader < l ⌝
.

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ mu cls_sl (cls:list loc),
  "#Hmu" ∷ readonly (ck ↦[config2.Clerk :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock N mu (own_Clerk_inv ck (length cls)) ∗
  "#Hcls" ∷ readonly (ck ↦[config2.Clerk :: "cls"] (slice_val cls_sl)) ∗
  "#Hcls_sl" ∷ readonly (own_slice_small cls_sl ptrT 1 cls) ∗
  "#Hrpc" ∷ ([∗ list] cl ∈ cls, ∃ srv, is_ReconnectingClient cl srv ∗ is_config_host srv γ) ∗
  "%HszNonzero" ∷ ⌜ length cls > 0 ⌝
.

(* FIXME: copied from pb_apply_proof. *)
Lemma wp_forSlice' {V} {H:IntoVal V} I ϕ sl ty q (l:list V) (body:val) :
  (∀ (i:u64) (v:V),
    {{{
          ⌜int.nat i < length l⌝ ∗ ⌜l !! (int.nat i) = Some v⌝ ∗ ϕ (int.nat i) v ∗ I i
    }}}
      body #i (to_val v)
    {{{
          RET #(); I (word.add i 1)
    }}}
  ) -∗
  {{{
        own_slice_small sl ty q l ∗
        ([∗ list] i ↦ v ∈ l, ϕ i v) ∗
        I 0
  }}}
    forSlice ty body (slice_val sl)
  {{{
        RET #(); I (length l)
  }}}
.
Proof.
  iIntros "#Hwp".
  iIntros (?) "!# (Hsl & Hl & HI) HΦ".
  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_forSlice (λ i, I i ∗ [∗ list] j ↦ v ∈ (drop (int.nat i) l), ϕ (j + int.nat i) v) %I
             with "[] [$Hsl Hl HI]").
  2: { rewrite drop_0.
       replace (int.nat (U64 0)) with (0) by word.
       setoid_rewrite <- plus_n_O. iFrame. }
  {
    clear Φ.
    iIntros (???Φ) "!# ([HI Hl] & % & %) HΦ".
    assert ((drop (int.nat i) l) !! 0 = Some x) as ?.
    {
      rewrite lookup_drop. rewrite <- H1.
      f_equal. word.
    }
    iDestruct (big_sepL_take_drop _ _ 1 with "Hl") as "[Hϕ Hl]".
    wp_apply ("Hwp" with "[HI Hϕ]").
    {
      iFrame "∗%".
      iSplit. 1: iPureIntro; word.
      iDestruct (big_sepL_lookup_acc with "Hϕ") as "[H _]".
      {
        rewrite lookup_take.
        { done. }
        lia.
      }
      iExactEq "H". repeat f_equal.
    }
    iIntros "HI".
    iApply "HΦ".
    iFrame.
    rewrite drop_drop.
    replace (int.nat (u64_instance.u64.(word.add) i 1%Z)) with (int.nat i + 1) by word.
    iApply (big_sepL_impl with "Hl").
    iModIntro.
    iIntros.
    replace (k + (int.nat i + 1)) with (1 + k + int.nat i) by word.
    done.
  }
  iIntros "[[HI _] _]".
  iApply "HΦ".
  rewrite Hsz.
  iExactEq "HI". f_equal. word.
Qed.

Lemma wp_MakeClerk hosts hosts_sl γ:
  {{{
      "Hhosts_sl" ∷ readonly (own_slice_small hosts_sl uint64T 1 hosts) ∗
      "#Hhosts" ∷ ([∗ list] host ∈ hosts, is_config_host host γ) ∗
      "%Hnonempty" ∷ ⌜ 0 < length hosts ⌝
  }}}
    config2.MakeClerk (slice_val hosts_sl)
  {{{
      ck, RET #ck; is_Clerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply wp_NewSlice.
  iIntros (?) "Hcls_sl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (cls_ptr) "Hcls".
  wp_pures.
  iMod (readonly_load with "Hhosts_sl") as (?) "Hhosts_sl".
  iDestruct (own_slice_small_sz with "Hhosts_sl") as %Hsz.
  wp_apply (wp_forSlice'
              (λ i,
               ∃ sl cls,
               "Hcls" ∷ cls_ptr ↦[slice.T ptrT] (slice_val sl) ∗
               "Hcls_sl" ∷ own_slice sl ptrT 1 (cls) ∗
               "#Hrpc" ∷ ([∗ list] cl ∈ cls, ∃ srv : u64, is_ReconnectingClient cl srv ∗ is_config_host srv γ) ∗
               "%Hsz" ∷ ⌜ length cls = int.nat i ⌝
               )%I
             with "[] [Hcls Hcls_sl $Hhosts_sl]").
  2:{
    iSplitL "Hhosts".
    { iExact "Hhosts". }
    repeat iExists _.
    iFrame.
    iSplitR; last done.
    by iApply big_sepL_nil.
  }
  {
    clear Φ.
    iIntros (???) "!# Hpre HΦ".
    wp_pures.
    iDestruct "Hpre" as "(%Hineq & %Hlookup & #Hhost & Hpre)".
    iNamed "Hpre".
    wp_apply wp_MakeReconnectingClient.
    iIntros (?) "#Hcl".
    wp_load.
    wp_bind (SliceAppend _ _ _).
    change (#cl_ptr) with (loc_IntoVal.(to_val) cl_ptr).
    wp_apply (wp_SliceAppend with "[$Hcls_sl]").
    iIntros (?) "Hcls_sl".
    wp_store.
    iApply "HΦ".
    iModIntro. repeat iExists _; iFrame.
    iSplitL.
    2:{ iPureIntro. rewrite app_length. simpl. word. }
    iApply (big_sepL_app with "[]").
    iFrame "Hrpc".
    iApply big_sepL_singleton.
    iExists _; iFrame "#".
  }
  iNamed 1.
  wp_pures.
  wp_apply wp_new_free_lock.
  iIntros (?) "HmuInv".
  wp_load.
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { eauto 20. }
  iIntros (?) "Hc".
  iDestruct (struct_fields_split with "Hc") as "HH".
  iNamed "HH".
  iApply "HΦ".
  repeat iExists _.
  iMod (readonly_alloc_1 with "mu") as "$".
  iMod (readonly_alloc_1 with "cls") as "$".
  iDestruct (own_slice_to_small with "Hcls_sl") as "Hcls_sl".
  iMod (readonly_alloc_1 with "Hcls_sl") as "$".
  iFrame "Hrpc".
  rewrite Hsz0.
  iMod (alloc_lock with "HmuInv [leader]") as "$".
  { iNext. repeat iExists _; iFrame. iPureIntro. word. }
  iPureIntro. word.
Qed.

Lemma wp_Clerk__ReserveEpochAndGetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 -∗
      (|={⊤∖↑N,∅}=> ∃ epoch conf, own_reserved_epoch γ epoch ∗ own_config γ conf ∗
       (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗
        own_reserved_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤∖↑N}=∗
         (∀ conf_sl, readonly (own_slice_small conf_sl uint64T 1 conf) -∗
           Φ (#(LitInt $ word.add epoch (U64 1)), slice_val conf_sl)%V)))
  ) -∗
  WP config2.Clerk__ReserveEpochAndGetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[-]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "#∗". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_apply wp_NewSlice.
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iDestruct "Hhost" as "[$ _]". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /ReserveEpochAndGetConfig_spec /ReserveEpochAndGetConfig_core_spec /=.
    Transparent u64_le.
    iSplitR.
    { (* case: successfully reserved epoch *)
      iIntros "Hlc".
      iDestruct ("HΦ" with "Hlc") as "Hupd".
      (* case: got a new epoch, no error *)
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (??) "(H1&H2&Hupd)".
      iExists _, _.
      iFrame "H1 H2".
      iIntros.
      iMod ("Hupd" with "[% //] [$] [$]") as "Hupd".
      iModIntro.
      iIntros (?) "%Hconf_enc Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (?) "Herr".
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      iRight. iModIntro.
      iSplitR; first done.
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (epoch_ptr) "Hepoch".
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_apply (Config.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (?) "Hconf_own".
      wp_pures.
      wp_load.
      wp_pures.
      iModIntro.
      iApply "Hupd".
      iFrame.
    }
    { (* case: RPC ran, but was not able to reserve an epoch *)
      iIntros (?) "%Herr _".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_apply wp_ref_of_zero.
      { done. }
      iIntros (?) "Herr".
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iLeft.
          iModIntro. iSplitR; first done.
          repeat iExists _.
          iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iLeft.
          iModIntro. iSplitR; first done.
          repeat iExists _.
          iFrame.
        }
      }
      { (* case: some other error, still retry *)
        wp_load.
        wp_pures.
        wp_if_destruct.
        { exfalso. done. }
        iModIntro.
        iLeft. iSplitR; first done.
        iExists _; iFrame.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iLeft.
    iSplitR; first done.
    iExists _. iFrame.
  }
Qed.

Lemma wp_Clerk__GetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (∀ conf conf_sl, Pwf conf -∗ readonly (own_slice_small conf_sl uint64T 1 conf)
                                 -∗ Φ (slice_val conf_sl)%V) -∗
  WP config2.Clerk__GetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[-]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_RandomUint64).
  iIntros (?) "_".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply wp_NewSlice.
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_loadField.

  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  set (idx:=(u64_instance.u64.(word.modu) r cls_sl.(Slice.sz))).
  assert (int.nat idx < length cls) as Hlookup.
  {
    subst idx.
    rewrite Hsl_sz.
    rewrite word.unsigned_modu_nowrap; last lia.
    { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
      { apply Z.mod_pos; lia. }
      { apply Z_mod_lt; lia. }
    }
  }
  apply list_lookup_lt in Hlookup as [? Hlookup].
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iDestruct "Hhost" as "(_ & $ & _)". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    iIntros (?) "HP".
    iIntros (?) "%Henc _".
    iIntros (?) "Hrep Hreply_sl".
    wp_pures.
    iRight.
    iModIntro. iSplitR; first done.
    wp_pures.
    wp_load.
    wp_apply (Config.wp_Decode with "[$Hreply_sl //]").
    iIntros (?) "Hconf".
    wp_pures.
    iApply ("HΦ" with "[$]").
    iFrame.
    done.
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    { exfalso. done. }
    iModIntro. iLeft.
    iSplitR; first done.
    iExists _. iFrame.
  }
Qed.

Lemma wp_Clerk__TryWriteConfig (ck:loc) new_conf new_conf_sl epoch γ Φ :
  is_Clerk ck γ -∗
  readonly (own_slice_small new_conf_sl uint64T 1 new_conf) -∗
  is_reserved_epoch_lb γ epoch -∗
  (□ Pwf new_conf) -∗
  □ (£ 1 -∗ |={⊤∖↑N,∅}=> ∃ latest_epoch reserved_epoch conf,
    own_latest_epoch γ latest_epoch ∗
    own_reserved_epoch γ reserved_epoch ∗
    own_config γ conf ∗ (⌜ epoch = reserved_epoch ⌝ -∗ own_config γ new_conf -∗
                         own_reserved_epoch γ reserved_epoch -∗
                         own_latest_epoch γ epoch
                         ={∅,⊤∖↑N}=∗
                         Φ #0)
  ) -∗
  (∀ (err:u64) , ⌜err ≠ 0⌝ -∗ Φ #err) -∗
  WP config2.Clerk__TryWriteConfig #ck #epoch (slice_val new_conf_sl)
  {{ Φ }}
.
Proof.
  iIntros "#Hck #Hconf_sl #Hlb #HP_new #HΦ Hfail".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl".
  wp_store.
  wp_apply (Config.wp_Encode with "[$]").
  iIntros (??) "(%HconfEnc & _ & Henc_sl)".
  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Henc_sl]").
  iIntros (?) "[Hargs_sl _]".
  wp_store.
  wp_pures.
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  replace (int.nat 0%Z) with (0%nat) by word.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[Hreply]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "#∗". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_load.
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_frame_wand with "[Hfail Hargs]"); first iNamedAccu.
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iDestruct "Hhost" as "(_ & _ & $ & _)". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /TryWriteConfig_spec /TryWriteConfig_core_spec /=.
    repeat iExists _.
    iSplitR.
    { iPureIntro. done. }
    iSplitR.
    { iPureIntro. done. }
    iFrame "#".
    Transparent u64_le.
    iSplitR.
    { (* case: successfully wrote new config and epoch *)
      iIntros "Hlc".
      iDestruct ("HΦ" with "Hlc") as "Hupd".
      (* case: got a new epoch, no error *)
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (???) "(H1&H2&H3&Hupd)".
      repeat iExists _.
      iFrame "H1 H2 H3".
      iIntros.
      iMod ("Hupd" with "[% //] [$] [$] [$]") as "Hupd".
      iModIntro.
      iIntros (?) "%Hconf_enc Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct ("Hrep_sl") as "[Hrep_sl1 Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      iModIntro.
      iNamed 1.
      iRight. iSplitR; first done.
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iApply "Hupd".
    }
    { (* case: RPC ran, but was not able to write *)
      iIntros (?) "%Herr".
      iIntros (?) "%HrepEnc Harg_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct "Hrep_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iModIntro. iNamed 1. iLeft.
          iSplitR; first done.
          iFrame. repeat iExists _. iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iModIntro. iNamed 1.
          iLeft. iSplitR; first done.
          iFrame.
          repeat iExists _.
          iFrame.
        }
      }
      { (* case: some other error, don't retry *)
        iModIntro. iNamed 1.
        iRight.
        iSplitR; first done.
        wp_pures.
        wp_load.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "_".
        wp_pures.
        iApply "Hfail".
        done.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iNamed 1. iLeft.
    iSplitR; first done.
    iFrame. repeat iExists _. iFrame.
  }
Qed.

Lemma wp_Clerk__GetLease (ck:loc) γ epoch Φ :
  is_Clerk ck γ -∗
  □ ((∀ (leaseExpiration:u64) γl,
      is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
      is_lease_valid_lb γl leaseExpiration -∗ Φ (#0, #leaseExpiration)%V) ∧
    (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ (#err, #0)%V)
  ) -∗
  WP config2.Clerk__GetLease #ck #epoch {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_store.
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[Hreply]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "#∗". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_load.
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_frame_wand with "[Hargs]"); first iNamedAccu.
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iDestruct "Hhost" as "(_ & _ & _ & $ & _)". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /GetLease_spec /GetLease_core_spec /=.
    repeat iExists _.
    iSplitR.
    { iPureIntro. done. }
    iSplit.
    { (* case: got a lease *)
      iIntros (??) "H1 H2".
      iIntros (?) "%Henc Hargs_sl".
      iIntros (?) "Hrep Hreply_sl".
      wp_pures.
      iLeft in "HΦ".
      iDestruct ("HΦ" with "[$] [$]") as "Hupd".
      wp_load.
      subst.
      iDestruct "Hreply_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iNamed 1.
      iRight.
      iSplitR; first done.
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "?".
      wp_pures.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iApply "Hupd".
    }
    { (* case: RPC ran, but server gave an error *)
      iIntros (?) "%Herr".
      iIntros (?) "%HrepEnc Harg_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct "Hrep_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iModIntro. iNamed 1. iLeft.
          iSplitR; first done.
          iFrame. repeat iExists _. iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "#∗".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iModIntro. iNamed 1.
          iLeft. iSplitR; first done.
          iFrame.
          repeat iExists _.
          iFrame.
        }
      }
      { (* case: some other error, don't retry *)
        iModIntro. iNamed 1.
        iRight.
        iSplitR; first done.
        wp_pures.
        wp_load.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "?".
        wp_pures.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "_".
        wp_pures.
        iRight in "HΦ".
        iApply "HΦ".
        done.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iNamed 1. iLeft.
    iSplitR; first done.
    iFrame. repeat iExists _. iFrame.
  }
Qed.

End config_proof.
