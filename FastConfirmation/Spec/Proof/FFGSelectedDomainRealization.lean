module
public import FastConfirmation.Spec.Proof.FFGGlobalCheckpointTrajectory

@[expose] public section

/-!
# Selected-domain facts from the common FFG trajectory

This file derives the endpoint root and honest-vote walk domains from the
handler-driven common `ChainFFGState`.  It also records, as a theorem rather
than a comment, why the checkpoint-cache half of `SelectedMarginDomain` is
not a plain invariant of the current executable model.

No `JustificationInterface` field is used below.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact cache-write obstruction -/

/-- The local cache property requested by `SelectedMarginDomain`. -/
def JustifiedCheckpointCached (store : Store Root) : Prop :=
  store.justified_checkpoint ∈ store.checkpoint_state_keys

/-- `update_checkpoints` changes no cache key.  Consequently its output is
cached exactly when either the winning candidate was already keyed, or the
old justified checkpoint remains cached. -/
theorem justifiedCheckpointCached_update_checkpoints_iff
    (store : Store Root) (jc fc : Checkpoint Root) :
    JustifiedCheckpointCached
        (FastConfirmation.Spec.update_checkpoints store jc fc) ↔
      if jc.epoch > store.justified_checkpoint.epoch then
        jc ∈ store.checkpoint_state_keys
      else JustifiedCheckpointCached store := by
  have hj :
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  unfold JustifiedCheckpointCached
  rw [hj, FastConfirmation.Spec.update_checkpoints_checkpoint_state_keys]
  split_ifs <;> rfl

/-- Weakest handler-local postcondition which closes the cache induction at
an `update_checkpoints` call: a candidate which actually wins must already be
present in the checkpoint-state key set. -/
def WinningJustifiedCandidateCached
    (store : Store Root) (jc : Checkpoint Root) : Prop :=
  jc.epoch > store.justified_checkpoint.epoch →
    jc ∈ store.checkpoint_state_keys

theorem justifiedCheckpointCached_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root)
    (hold : JustifiedCheckpointCached store)
    (hwinning : WinningJustifiedCandidateCached store jc) :
    JustifiedCheckpointCached
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  rw [justifiedCheckpointCached_update_checkpoints_iff]
  split_ifs with hwinner
  · exact hwinning hwinner
  · exact hold

/-- Formal failure mode: a strictly newer unkeyed candidate becomes the
global justified checkpoint while the cache-key set is unchanged. -/
theorem update_checkpoints_uncaches_winning_unkeyed
    (store : Store Root) (jc fc : Checkpoint Root)
    (hwinner : jc.epoch > store.justified_checkpoint.epoch)
    (hunkeyed : jc ∉ store.checkpoint_state_keys) :
    ¬ JustifiedCheckpointCached
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  rw [justifiedCheckpointCached_update_checkpoints_iff, if_pos hwinner]
  exact hunkeyed

namespace Execution

variable (E : Execution Root)

/-! ## Realized justified-root knownness -/

/-- The realized global justified root is a concrete known checkpoint block.

The trusted-anchor boundary premise is necessary for checkpoint-sync
executions: it lets the retained anchor-root walk continue to every later
certified checkpoint boundary. -/
theorem justifiedRootKnown_of_globalTrajectory
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hHm : E.WithinHorizon cfg m) :
    (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : anchor.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext w m).blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hwf hgenEq w m
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hparentSlots : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w m
  rcases globalJustified_anchor_or_known_AU (cfg := cfg) (ext := ext)
      (E := E) hcoh hgenShort hanchor w m with
    hjustAnchor | ⟨carrier, hcarrier, hAU⟩
  · rw [hjustAnchor]
    exact hanchorMem
  · have hanchorEpochLe : anchor.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch := by
      obtain ⟨hcert⟩ := S.certifiedJustified_of_AU cfg hAU
      exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
    have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks anchor.root).slot carrier :=
      E.store_walkKnownK cfg ext hwf hec
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
        anchor.root hanchorMem carrier hcarrier
    have hwalk : WalkKnown (E.store cfg ext w m)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch) carrier := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    have hcheckpoint := hcoh.au_checkpoint_of_known w hw m hHm carrier
      hcarrier (E.store cfg ext w m).justified_checkpoint hAU
    rw [hcheckpoint]
    simp only [get_checkpoint_for_block, get_checkpoint_block]
    exact (get_ancestor_spec hparentSlots hwalk).1

/-! ## Honest vote-target walk domain -/

/-- For every actual post-anchor honest vote, the source store's head walk to
the vote's FFG target boundary stays in the concrete store domain.

This is fork-choice geometry, not a new adequacy assumption.  Boundary
alignment is the same checkpoint-sync premise needed for global finalized and
justified checkpoint roots: a mid-epoch trusted anchor cannot support a walk
to the earlier boundary of its own epoch. -/
theorem postAnchorHonestVoteTargetWalkDomain_of_globalTrajectory
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    E.PostAnchorHonestVoteTargetWalkDomain cfg ext := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorEpoch : anchor.epoch = compute_epoch_at_slot cfg ast.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at he
    simpa only [get_forkchoice_store, get_current_epoch] using he
  have hanchorMem0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  intro i hi s n index hs0 hnH hnSlot _hvote
  have hanchorMem : anchor.root ∈
      (E.store cfg ext i n).block_roots :=
    (E.store_storeLE cfg ext i (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext i n).blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hwf hgenEq i n
      (hanchorRoot ▸ hanchorMem)
  have hheadKnown : (get_head cfg (E.store cfg ext i n)).root ∈
      (E.store cfg ext i n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i n) with hhead | hfallback
    · exact hhead
    · rw [hfallback]
      exact E.justifiedRootKnown_of_globalTrajectory cfg ext hwf hec
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary hi n hnH
  have hheadStateSlot :
      ((E.store cfg ext i n).block_states
        (get_head cfg (E.store cfg ext i n)).root).slot ≤ s := by
    have hcore := E.store_wellFormedStoreCore cfg ext
      hec.state_transition_slot hgws.core i n
    rw [hcore.2 _ hheadKnown]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext hdiv
      hgenShort i n _ hheadKnown
    rwa [E.store_current_slot cfg ext i n, hnSlot] at hblockSlot
  have htargetEpoch :
      (honest_attestation cfg ext
        (E.store cfg ext i n) s index i).data.target.epoch =
        compute_epoch_at_slot cfg s :=
    honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext i n) s index hec.process_slots_slot hheadStateSlot
  have hslotAtZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext i 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg hdiv] at hcurrent0
    exact hcurrent0.symm
  have hanchorEpochLeTarget : anchor.epoch ≤
      (honest_attestation cfg ext
        (E.store cfg ext i n) s index i).data.target.epoch := by
    calc
      anchor.epoch = compute_epoch_at_slot cfg ast.slot := hanchorEpoch
      _ ≤ compute_epoch_at_slot cfg s := by
        exact Nat.div_le_div_right (by rwa [hslotAtZero] at hs0)
      _ = (honest_attestation cfg ext
          (E.store cfg ext i n) s index i).data.target.epoch :=
        htargetEpoch.symm
  have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
      compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext i n) s index i).data.target.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLeTarget
  have hwalkAnchor : WalkKnown (E.store cfg ext i n)
      ((E.store cfg ext i n).blocks anchor.root).slot
      (get_head cfg (E.store cfg ext i n)).root :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ i n
      anchor.root hanchorMem _ hheadKnown
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary'.trans hstartLe

end Execution

end FastConfirmation.Spec

end
