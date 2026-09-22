module
public import FastConfirmation.Spec.Proof.FCRCallContracts
public import FastConfirmation.Spec.Proof.TrustedAnchorGeometry

@[expose] public section

/-!
# Concrete realization of the two actual FCR reset checkpoints

The finalized reset is reconstructed from the executable global-checkpoint
ledger.  The observed reset is reconstructed from the exact
`update_fast_confirmation_variables` rotation, with a ghost invariant for the
two checkpoint fields retained by `Execution.fcr`.

Only root knownness and a conditional certificate for the root's current-epoch
checkpoint are exported.  No FCR ancestry, safety, historical conclusion, or
`JustificationInterface` premise enters this construction.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact FCR field rotation -/

/-- Exact source selected for the carried greatest-unrealized field. -/
theorem update_fcv_previous_greatest_exact
    (fcrStore : FastConfirmationStore Root) :
    FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
        (update_fast_confirmation_variables cfg fcrStore) =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store + 1) then
        fcrStore.store.unrealized_justified_checkpoint
      else fcrStore.previous_epoch_greatest_unrealized_checkpoint := by
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- Exact source selected for the observed checkpoint, including the ordered
write through the possibly just-updated greatest-unrealized field. -/
theorem update_fcv_observed_exact
    (fcrStore : FastConfirmationStore Root) :
    (update_fast_confirmation_variables cfg fcrStore).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg fcrStore.store + 1) then
          fcrStore.store.unrealized_justified_checkpoint
        else fcrStore.previous_epoch_greatest_unrealized_checkpoint
      else fcrStore.current_epoch_observed_justified_checkpoint := by
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

namespace Execution

variable (E : Execution Root)

/-! ## Store-local checkpoint realization -/

/-- Internal evidence retained while a reset checkpoint is carried through
the FCR trajectory.  The boundary inequality is the concrete geometry needed
to identify `c` with the checkpoint of `c.root` when that root is in the
store's current epoch. -/
structure ResetCheckpointRealizedAt
    (anchor : Checkpoint Root) (store : Store Root)
    (c : Checkpoint Root) : Prop where
  root_known : c.root ∈ store.block_roots
  root_slot_le_boundary :
    (store.blocks c.root).slot ≤ compute_start_slot_at_epoch cfg c.epoch
  epoch_le_current : c.epoch ≤ get_current_store_epoch cfg store
  certified : Nonempty (CertifiedJustified cfg E anchor c)

omit [LinearOrder Root] [Inhabited Root] in
/-- A realized checkpoint supplies exactly the root/certificate pair exported
by `ActualResetInputCheckpointRealization`. -/
theorem ResetCheckpointRealizedAt.root_and_current_certificate
    {anchor c : Checkpoint Root} {store : Store Root}
    (h : E.ResetCheckpointRealizedAt cfg anchor store c) :
    c.root ∈ store.block_roots ∧
      (get_block_epoch cfg store c.root = get_current_store_epoch cfg store →
        Nonempty (CertifiedJustified cfg E anchor
          (get_checkpoint_for_block cfg store c.root
            (get_block_epoch cfg store c.root)))) := by
  refine ⟨h.root_known, ?_⟩
  intro hcurrent
  have hscaled :
      get_block_epoch cfg store c.root * cfg.slots_per_epoch ≤
        c.epoch * cfg.slots_per_epoch := by
    simpa only [compute_start_slot_at_epoch] using
      (start_slot_at_block_epoch_le cfg store c.root).trans
        h.root_slot_le_boundary
  have hepochUpper : get_block_epoch cfg store c.root ≤ c.epoch :=
    Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hepochLower : c.epoch ≤ get_block_epoch cfg store c.root := by
    rw [hcurrent]
    exact h.epoch_le_current
  have hepoch : get_block_epoch cfg store c.root = c.epoch :=
    Nat.le_antisymm hepochUpper hepochLower
  have hslotLower : compute_start_slot_at_epoch cfg c.epoch ≤
      (store.blocks c.root).slot := by
    rw [← hepoch]
    exact start_slot_at_block_epoch_le cfg store c.root
  have hslot : (store.blocks c.root).slot =
      compute_start_slot_at_epoch cfg c.epoch :=
    Nat.le_antisymm h.root_slot_le_boundary hslotLower
  have hcheckpoint : get_checkpoint_for_block cfg store c.root
        (get_block_epoch cfg store c.root) = c := by
    apply checkpoint_eq_of_epoch_root_eq
    · simpa only [get_checkpoint_for_block] using hepoch
    · simp only [get_checkpoint_for_block, get_checkpoint_block]
      rw [hepoch, ← hslot, get_ancestor_stop (Nat.le_refl _)]
  rw [hcheckpoint]
  exact h.certified

/-- Realization is stable under growth along one node's execution-store
trajectory. -/
theorem ResetCheckpointRealizedAt.mono
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor c : Checkpoint Root} {v : ValidatorIndex} {n m : ℕ}
    (hnm : n ≤ m)
    (h : E.ResetCheckpointRealizedAt cfg anchor
      (E.store cfg ext v n) c) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v m) c := by
  have hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext v m).block_roots :=
    (E.store_storeLE cfg ext v hnm).1
  have hknownM : c.root ∈ (E.store cfg ext v m).block_roots :=
    hsub h.root_known
  have hagree : (E.store cfg ext v n).blocks c.root =
      (E.store cfg ext v m).blocks c.root :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v m) h.root_known hknownM
  have hcurrentMono :
      get_current_store_epoch cfg (E.store cfg ext v n) ≤
        get_current_store_epoch cfg (E.store cfg ext v m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg hnm)
  exact {
    root_known := hknownM
    root_slot_le_boundary := by
      rw [← hagree]
      exact h.root_slot_le_boundary
    epoch_le_current := h.epoch_le_current.trans hcurrentMono
    certified := h.certified
  }

/-- The boundary-aligned trusted anchor has a realization in every reachable
store. -/
theorem resetCheckpointRealizedAt_anchor
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v n) anchor := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hanchorRoot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hknown0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hknownN : anchor.root ∈ (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hknown0
  have hagree : E.genesis_store.blocks anchor.root =
      (E.store cfg ext v n).blocks anchor.root :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v 0)
      (E.blockProvenance cfg ext v n) hknown0 hknownN
  have hslot0 := E.trustedAnchor_slot_eq_start cfg ext hA
    hanchor hboundary
  exact {
    root_known := hknownN
    root_slot_le_boundary := by
      rw [← hagree, hslot0]
    epoch_le_current :=
      E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary v n
    certified := ⟨CertifiedJustified.anchor⟩
  }

/-- An AU checkpoint at a known carrier has a concrete realization in the
same horizon-bounded honest store. -/
theorem resetCheckpointRealizedAt_of_known_AU
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    {carrier : Root}
    (hcarrier : carrier ∈ (E.store cfg ext w m).block_roots)
    {c : Checkpoint Root} (hAU : S.AU cfg carrier c) :
    E.ResetCheckpointRealizedAt cfg anchor
      (E.store cfg ext w m) c := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  obtain ⟨hcert⟩ := S.certifiedJustified_of_AU cfg hAU
  have hanchorEpochLe : anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
  have hwalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg c.epoch) carrier :=
    E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      w m hanchorEpochLe hcarrier
  have hwf : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      hgen hA.wellFormed.anchor_parent_unscheduled w m
  have hcheckpoint := hcoh.au_checkpoint_of_known w hw m hHm carrier
    hcarrier c hAU
  have hroot : c.root = get_checkpoint_block cfg
      (E.store cfg ext w m) carrier c.epoch := by
    have := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block] using this
  have hspec := get_ancestor_spec hwf hwalk
  have hcarrierSlotUpper :
      ((E.store cfg ext w m).blocks carrier).slot ≤
        get_current_slot cfg (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenShort
      w m carrier hcarrier
  have hcarrierAt : E.BlockAt carrier
      ((E.store cfg ext w m).blocks carrier) :=
    E.blockAt_of_store_known cfg ext hcarrier
  have hepochLe : c.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    calc
      c.epoch ≤ compute_epoch_at_slot cfg
          ((E.store cfg ext w m).blocks carrier).slot :=
        S.au_epoch_le_block hcarrierAt hAU
      _ ≤ compute_epoch_at_slot cfg
          (get_current_slot cfg (E.store cfg ext w m)) :=
        ce_mono cfg hcarrierSlotUpper
      _ = get_current_store_epoch cfg (E.store cfg ext w m) := rfl
  exact {
    root_known := by rw [hroot]; exact hspec.1
    root_slot_le_boundary := by rw [hroot]; exact hspec.2
    epoch_le_current := hepochLe
    certified := ⟨hcert⟩
  }

/-- Common constructor for the exact origin shape emitted by the global
checkpoint trajectory. -/
theorem resetCheckpointRealizedAt_of_anchor_or_known_AU
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m) {c : Checkpoint Root}
    (horigin : c = anchor ∨
      ∃ carrier ∈ (E.store cfg ext w m).block_roots,
        S.AU cfg carrier c) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext w m) c := by
  rcases horigin with rfl | ⟨carrier, hcarrier, hAU⟩
  · exact E.resetCheckpointRealizedAt_anchor cfg ext hA
      hanchor hboundary w m
  · exact E.resetCheckpointRealizedAt_of_known_AU cfg ext hA hcoh
      hanchor hboundary hw hHm hcarrier hAU

/-- The unrealized-justified field has the same anchor/AU form as the two
realized global checkpoint fields. -/
theorem globalUnrealizedJustified_anchor_or_known_AU
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext w n).unrealized_justified_checkpoint = anchor ∨
      ∃ r ∈ (E.store cfg ext w n).block_roots,
        S.AU cfg r
          (E.store cfg ext w n).unrealized_justified_checkpoint := by
  have horigins := E.globalCheckpointOrigins cfg ext hcoh hgen hanchor w n
  rcases horigins.unrealized_justified with hanchor' | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor'
  · right
    refine ⟨r, hr, ?_⟩
    rw [hgu]
    exact S.gu_AU cfg r ⟨(E.store cfg ext w n).blocks r,
      E.blockAt_of_store_known cfg ext hr⟩

/-! ## Global field realizations -/

/-- Concrete realization of the store-global finalized checkpoint. -/
theorem finalizedCheckpoint_resetRealizedAt_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext w m)
      (E.store cfg ext w m).finalized_checkpoint := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  apply E.resetCheckpointRealizedAt_of_anchor_or_known_AU cfg ext hA hcoh
    hanchor hboundary hw hHm
  exact E.globalFinalized_anchor_or_known_AU cfg ext hcoh hgen hanchor w m

/-- Concrete realization of the store-global unrealized-justified
checkpoint, the fresh source written into the FCR cache. -/
theorem unrealizedJustifiedCheckpoint_resetRealizedAt_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext w m)
      (E.store cfg ext w m).unrealized_justified_checkpoint := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  apply E.resetCheckpointRealizedAt_of_anchor_or_known_AU cfg ext hA hcoh
    hanchor hboundary hw hHm
  exact E.globalUnrealizedJustified_anchor_or_known_AU cfg ext hcoh
    hgen hanchor w m

/-! ## The retained FCR checkpoint history -/

/-- Ghost evidence for the two FCR fields from which an observed checkpoint
can be sourced at the next query. -/
structure ResetCheckpointHistoryAt
    (anchor : Checkpoint Root) (v : ValidatorIndex) (n : ℕ) : Prop where
  observed : E.ResetCheckpointRealizedAt cfg anchor
    (E.store cfg ext v n)
    (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint
  previous_greatest : E.ResetCheckpointRealizedAt cfg anchor
    (E.store cfg ext v n)
    (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint

/-- At a real slot advance, the retained greatest-unrealized field is either
the current store's UJ checkpoint or the previous retained value. -/
theorem fcr_previous_greatest_succ_of_advance
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  exact update_fcv_previous_greatest_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- At a real slot advance, the observed field follows the exact ordered
two-stage rotation. -/
theorem fcr_observed_succ_of_advance
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcr cfg ext v (n + 1)).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1))) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
        else
          (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint
      else
        (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.current_epoch_observed_justified_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  exact update_fcv_observed_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- The actual query's observed checkpoint follows the same exact rotation,
whether or not that speculative query is a real slot call. -/
theorem fcrStep_observed_exact (v : ValidatorIndex) (n : ℕ) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1))) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
        else
          (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint
      else
        (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStep]
  exact update_fcv_observed_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- Both retained FCR checkpoint fields remain concretely realized throughout
the finite honest trajectory. -/
theorem resetCheckpointHistoryAt_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.ResetCheckpointHistoryAt cfg ext anchor v n := by
  intro n
  induction n with
  | zero =>
      intro hH0
      have hfinal :=
        E.finalizedCheckpoint_resetRealizedAt_of_globalTrajectory cfg ext
          hA hcoh hanchor hboundary hv hH0
      constructor <;>
        simpa only [Execution.fcr, get_fast_confirmation_store] using hfinal
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hhistory := ih hHn
      have hobserved := hhistory.observed.mono cfg ext E hA (Nat.le_succ n)
      have hprevious :=
        hhistory.previous_greatest.mono cfg ext E hA (Nat.le_succ n)
      have huj :=
        E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_globalTrajectory
          cfg ext hA hcoh hanchor hboundary hv hHn1
      by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · constructor
        · rw [E.fcr_observed_succ_of_advance cfg ext v n hadv]
          split_ifs <;> assumption
        · rw [E.fcr_previous_greatest_succ_of_advance cfg ext v n hadv]
          split_ifs <;> assumption
      · constructor
        · simpa only [Execution.fcr, if_neg hadv] using hobserved
        · simpa only [Execution.fcr, if_neg hadv] using hprevious

/-- Concrete realization of the observed checkpoint in the actual query
store, reconstructed from retained history and the current UJ field. -/
theorem fcrStep_observed_resetRealizedAt_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v (n + 1))
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint := by
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hhistory := E.resetCheckpointHistoryAt_of_globalTrajectory cfg ext
    hA hcoh hanchor hboundary hv n hHn
  have hobserved := hhistory.observed.mono cfg ext E hA (Nat.le_succ n)
  have hprevious :=
    hhistory.previous_greatest.mono cfg ext E hA (Nat.le_succ n)
  have huj :=
    E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_globalTrajectory
      cfg ext hA hcoh hanchor hboundary hv hHn1
  rw [E.fcrStep_observed_exact cfg ext v n]
  split_ifs <;> assumption

/-! ## Public reset producer -/

/-- Global FFG origins plus the exact FCR rotation construct the lower reset
interface consumed by the historical current-target trajectory. -/
theorem actualResetInputCheckpointRealization_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    E.ActualResetInputCheckpointRealization cfg ext anchor v := by
  intro n hHn1 input hkind
  have hfinal :=
    E.finalizedCheckpoint_resetRealizedAt_of_globalTrajectory cfg ext
      hA hcoh hanchor hboundary hv hHn1
  have hobservedRealized :=
    E.fcrStep_observed_resetRealizedAt_of_globalTrajectory cfg ext
      hA hcoh hanchor hboundary hv hHn1
  rcases hkind with hfinalized | hobserved
  · subst input
    simpa only [E.fcrStep_store] using
      hfinal.root_and_current_certificate (cfg := cfg)
  · subst input
    simpa only [E.fcrStep_store] using
      hobservedRealized.root_and_current_certificate (cfg := cfg)

end Execution

end FastConfirmation.Spec

end
