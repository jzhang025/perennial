From Perennial.program_proof Require Import grove_prelude.
(* From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb. *)
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list csum.
From Perennial.Helpers Require Import ListSolver.

Section mpaxos_protocol.

Context `{!heapGS Σ}.

Record mp_system_names :=
{
  mp_proposal_gn : gname ;
  mp_state_gn : gname ;
}.

Record mp_server_names :=
{
  mp_urpc_gn : urpc_proof.server_chan_gnames ;
  mp_accepted_gn : gname ;
  mp_vote_gn : gname ; (* token for granting vote to a node in a particular epoch *)
}.

Context `{EntryType:Type}.

Local Definition logR := mono_listR (leibnizO EntryType).

Context (config: list mp_server_names).

Class mp_ghostG Σ := {
    mp_ghost_epochG :> mono_natG Σ ;
    mp_ghost_proposalG :> inG Σ (gmapR (u64) (csumR (exclR unitO) logR)) ;
    mp_ghost_acceptedG :> inG Σ (gmapR (u64) logR) ;
    mp_ghost_commitG :> inG Σ logR ;
    mp_proposal_escrowG :> inG Σ (gmapR (u64) (dfrac_agreeR unitO)) ;
}.

Context `{!mp_ghostG Σ}.

Implicit Type γsrv : mp_server_names.
Implicit Type γsys : mp_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_proposal_unused γsys epoch : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinl (Excl ()) ]}.
Definition own_proposal γsys epoch σ : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinr (●ML (σ : list (leibnizO (EntryType))))]}.
Definition is_proposal_lb γsys epoch σ : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinr (◯ML (σ : list (leibnizO (EntryType))))]}.

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

Definition own_vote_tok γsrv epoch : iProp Σ :=
  own γsrv.(mp_vote_gn) {[ epoch := to_dfrac_agree (DfracOwn 1) ()]}.

Definition own_accepted γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ●ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_lb γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ◯ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_ro γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ●ML□ (σ : list (leibnizO (EntryType)))]}.

(* TODO: if desired, can make these exclusive by adding an exclusive token to each *)
Definition own_ghost γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition own_commit γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition is_ghost_lb γ σ : iProp Σ :=
  own γ.(mp_state_gn) (◯ML (σ : list (leibnizO (EntryType)))).

(* FIXME: this definition needs to only require a quorum *)
Definition committed_by γsys epoch σ : iProp Σ :=
  ∀ γsrv, ⌜γsrv ∈ config⌝ → is_accepted_lb γsrv epoch σ.

Definition old_proposal_max γsys epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜int.nat epoch_old < int.nat epoch⌝ →
   committed_by γsys epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition mpN := nroot .@ "mp".
Definition ghostN := mpN .@ "ghost".

Definition sysN := ghostN .@ "sys".
Definition opN := ghostN .@ "op".

(* XXX(namespaces):
   The update for the ghost state is fired while the sys_inv is open.
   Additionally, the update is fired while the is_valid_inv is open, so we need
   the initial mask to exclude those invariants.
*)
Definition is_valid_inv γsys σ op : iProp Σ :=
  inv opN (
    £ 1 ∗
    (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_ghost γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γsys (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True)) ∨
    is_ghost_lb γsys (σ ++ [op])
  )
.

Definition is_proposal_valid γ σ : iProp Σ :=
  □(∀ σ', ⌜σ' ⪯ σ⌝ → own_commit γ σ' ={⊤∖↑sysN}=∗ own_commit γ σ).

Definition is_proposal_facts γ epoch σ: iProp Σ :=
  old_proposal_max γ epoch σ ∗
  is_proposal_valid γ σ.

(* FIXME: these definitions need to change *)
Definition own_escrow_toks γsrv epoch : iProp Σ :=
  [∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch' ≤ int.nat epoch⌝ ∨ own_vote_tok γsrv epoch'
.

Record MPaxosState :=
  mkMPaxosState
    {
      mp_epoch:u64 ;
      mp_acceptedEpoch:u64 ;
      mp_log:list EntryType ;
    }.

Definition own_replica_ghost γsys γsrv (st:MPaxosState) : iProp Σ.
Admitted.

Definition own_leader_ghost γsys γsrv (st:MPaxosState): iProp Σ.
Admitted.

End mpaxos_protocol.
