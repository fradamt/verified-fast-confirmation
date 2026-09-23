module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionCarriedBranch
public import FastConfirmationProofs.ModelFacts
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness

@[expose] public section

/-!
# Fresh historical A3.2 lineage at a retained current-target crossing

This file handles the payload-producing complement of the carried/current/
no-crossing branch.  A retained tentative crossing exposes the exact helper
gate and its call-site honest-target support.  The accepted fixed-source gate
producer turns those executable facts into the concrete A3.2 quorum payload.

The new lineage starts at the selector result itself.  Its accepted segment is
therefore reflexive: the path from the carried input to the result crosses an
epoch boundary and is deliberately not mislabeled as a same-epoch segment.
Finalized and observed-reset branches remain separate.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

namespace AcceptedCurrentTargetA32GateRealization

/-- Retie an accepted target-local gate realization to a later carrier in the
same accepted epoch segment.

This is a lossless source rewrite.  The concrete quorum, its votes, deadline,
weight bound, and certificate are unchanged.  Accepted phase-0 coherence
makes `GJ` constant along the segment; the two exact block-epoch equations
then reduce both paper `VSAt` selectors to those `GJ` values. -/
def fixedSource_of_acceptedSameEpochSegment
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} {b : Root}
    (htargetEpoch : get_block_epoch cfg store
      (get_current_target cfg store).root =
        (get_current_target cfg store).epoch)
    (hbEpoch : get_block_epoch cfg store b =
      (get_current_target cfg store).epoch)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_current_target cfg store).root b)
    (hgate : AcceptedCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store) :
    AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store b := by
  refine ⟨hgate.certified, ?_⟩
  rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
  · exact Or.inl hanchor
  · refine Or.inr ⟨hne, Q, ?_⟩
    have hgj : B.state.GJ b =
        B.state.GJ (get_current_target cfg store).root :=
      hsegment.gj_eq_first hphase
        B.coherence.toAcceptedFFGSelectorCoherence
    calc
      Q.source = B.state.VSAt cfg ext store
          (get_current_target cfg store).root
          (get_current_target cfg store).epoch := hsource
      _ = B.state.GJ (get_current_target cfg store).root := by
        simp only [AcceptedChainFFGState.VSAt, htargetEpoch, if_pos]
      _ = B.state.GJ b := hgj.symm
      _ = B.state.VSAt cfg ext store b
          (get_current_target cfg store).epoch := by
        simp only [AcceptedChainFFGState.VSAt, hbEpoch, if_pos]

end AcceptedCurrentTargetA32GateRealization

/-! ## Target-local gate source retie from the concrete selector path -/




end Execution


end FastConfirmation.Spec

/-!
# Historical A3.2 evaluator branches over accepted global trajectory data

These are the preferred action-facing wrappers for the carried current-epoch
branches.  They use one accepted-prefix FFG semantics and the narrow scheduled
trajectory assumptions.  Store geometry, head knownness, and exact causal
well-formedness come from the accepted global lower contracts; no
`SelectedMarginAssumptions`, selected-margin domain, or legacy justification
interface is reconstructed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Narrow trusted-anchor geometry from scheduled trajectory data -/

/-- Boundary alignment identifies the trusted anchor block slot using only
the scheduled trajectory's genesis facts. -/
theorem trustedAnchor_slot_eq_start_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    (E.genesis_store.blocks anchor.root).slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hepoch : get_block_epoch cfg E.genesis_store anchor.root =
      anchor.epoch := by
    rw [hgen, hroot]
    have h := congrArg Checkpoint.epoch hanchor
    rw [hgen] at h
    simp only [get_block_epoch, get_forkchoice_store,
      Function.update_self, get_current_epoch, hslot] at h ⊢
    exact h.symm
  apply Nat.le_antisymm hboundary
  rw [← hepoch]
  exact start_slot_at_block_epoch_le cfg E.genesis_store anchor.root

/-- The trusted anchor epoch is no later than a concrete execution store's
clock epoch, using only trajectory timing and accepted-message provenance. -/
theorem trustedAnchor_epoch_le_currentEpoch_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) :
    anchor.epoch ≤ get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgen v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start_of_trajectory cfg ext hT
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgen, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  have hslotUpper : ((E.store cfg ext v n).blocks anchor.root).slot ≤
      get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n anchor.root hanchorN
  simp only [get_current_store_epoch, compute_epoch_at_slot]
  apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
  change compute_start_slot_at_epoch cfg anchor.epoch ≤
    get_current_slot cfg (E.store cfg ext v n)
  rw [← hanchorStart, ← hanchorBlock]
  exact hslotUpper

/-- The trusted anchor supplies a walk to every later epoch boundary under
the narrow scheduled trajectory assumptions. -/
theorem trustedAnchor_boundaryWalkAtEpoch_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) {e : Epoch}
    (hae : anchor.epoch ≤ e)
    {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots) :
    WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg e) r := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hwalkAnchor : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks anchor.root).slot r :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgen, hslot, hparent⟩ v n
        anchor.root hanchorN r hr
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgen v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start_of_trajectory cfg ext hT
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgen, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  apply hwalkAnchor.mono
  rw [hanchorBlock, hanchorStart]
  simpa only [compute_start_slot_at_epoch] using
    Nat.mul_le_mul_right cfg.slots_per_epoch hae

/-! ## Accepted-global carried/no-crossing wrapper -/





end Execution


end FastConfirmation.Spec

end
