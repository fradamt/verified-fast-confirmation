module
public import FastConfirmationStatements.Premises.FFGCertificates
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationInternal.FFG.Certificates
public import FastConfirmationInternal.FFG.AnchorNormalization
public import FastConfirmationInternal.FFG.ScheduledState
public import FastConfirmationInternal.FFG.CheckpointLinks
public import FastConfirmationInternal.Network.SynchronyConversion
public import FastConfirmationProofs.ModelFacts.ScheduledPrefixes

@[expose] public section

/-!
# ModelFacts / FFGState

Proofs about Model/FFGCertificates. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
namespace Execution
variable (E : Execution Root)
theorem RootDescends.trans {a b c : Root}
    (hab : E.RootDescends a b) (hbc : E.RootDescends b c) :
    E.RootDescends a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)

end Execution
end FastConfirmation.Spec

/-!
# FFGStateSemantics model facts

Proofs about Model/FFGStateSemantics. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
namespace AcceptedBlockAttestationInclusion

end AcceptedBlockAttestationInclusion
end Execution

namespace IncludedSupermajorityLink
end IncludedSupermajorityLink
namespace IncludedCertifiedJustified

/-- A certified checkpoint is the anchor or is newer than it. -/
theorem eq_anchor_or_epoch_gt {E : Execution Root}
    {included : Root → Attestation Root → Prop}
    {anchor : Checkpoint Root} {carrier : Root} {c : Checkpoint Root}
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    c = anchor ∨ anchor.epoch < c.epoch := by
  induction h with
  | anchor => exact Or.inl rfl
  | link _ L ih =>
    right
    rcases ih with h | h
    · subst h
      exact L.source_before_target
    · exact lt_trans h L.source_before_target

end IncludedCertifiedJustified
namespace IncludedCertifiedFinalized

/-- The finalizing link of a `k = 2` certificate ends at least one epoch
after the finalized checkpoint. -/
theorem epoch_succ_le_child {E : Execution Root}
    {included : Root → Attestation Root → Prop}
    {anchor : Checkpoint Root} {carrier : Root} {c : Checkpoint Root}
    (F : IncludedCertifiedFinalized cfg E included anchor carrier c) :
    c.epoch + 1 ≤ F.child.epoch := by
  have key : ∀ x y : ℕ, (y = x + 1 ∨ y = x + 2) → x + 1 ≤ y := by omega
  exact key _ _ F.child_epoch

end IncludedCertifiedFinalized
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}



/-- Every AU checkpoint has concrete certified, on-chain, causal formation
evidence at some carrier. -/
theorem AU.evidence (S : ChainFFGState cfg E anchor)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AU cfg tip c) :
    ∃ carrier : Root,
      E.RootDescends tip carrier ∧
        FormedCheckpointEvidence cfg E
          S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩






end ChainFFGState
namespace AcceptedBlockFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}

/-- An available checkpoint is the anchor or is newer than it. -/
theorem available_anchor_or_after
    (S : AcceptedBlockFFGState cfg ext E anchor) {tip : Root} {c : Checkpoint Root}
    (h : ∃ carrier, E.RootDescends tip carrier ∧ S.checkpoint_evidence_in_block carrier c) :
    c = anchor ∨ anchor.epoch < c.epoch := by
  obtain ⟨_, _, hformed⟩ := h
  obtain ⟨hc⟩ := (S.formed_evidence hformed).certified
  exact IncludedCertifiedJustified.eq_anchor_or_epoch_gt cfg hc

theorem realized_justified_anchor_or_after
    (S : AcceptedBlockFFGState cfg ext E anchor) {r : Root}
    (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.realized_justified r = anchor ∨ anchor.epoch < (S.realized_justified r).epoch :=
  S.available_anchor_or_after cfg ext (S.realized_justified_mem r hr)

theorem unrealized_justified_anchor_or_after
    (S : AcceptedBlockFFGState cfg ext E anchor) {r : Root}
    (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.unrealized_justified r = anchor ∨ anchor.epoch < (S.unrealized_justified r).epoch :=
  S.available_anchor_or_after cfg ext (S.unrealized_justified_mem r hr)

@[simp] theorem mem_slashableOnChain
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (tip : Root) (i : ValidatorIndex) :
    i ∈ S.slashableOnChain cfg ext tip ↔
      i < E.registry.length ∧ S.HasSlashablePairOnChain cfg ext tip i := by
  classical
  constructor
  · intro hi
    obtain ⟨hrange, hpair⟩ := Finset.mem_filter.mp hi
    exact ⟨Finset.mem_range.mp hrange, hpair⟩
  · rintro ⟨hlt, h⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, h⟩

theorem AvailableCheckpoint.mono (S : AcceptedBlockFFGState cfg ext E anchor)
    {old new : Root} {c : Checkpoint Root}
    (hdesc : E.RootDescends new old) (hAU : S.AvailableCheckpoint cfg ext old c) :
    S.AvailableCheckpoint cfg ext new c := by
  obtain ⟨carrier, holdCarrier, hformed⟩ := hAU
  exact ⟨carrier, Execution.RootDescends.trans E hdesc holdCarrier, hformed⟩

theorem AvailableCheckpoint.evidence (S : AcceptedBlockFFGState cfg ext E anchor)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AvailableCheckpoint cfg ext tip c) :
    ∃ carrier, E.RootDescends tip carrier ∧
      IncludedCheckpointEvidence cfg ext E
        S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩

theorem gj_AU (S : AcceptedBlockFFGState cfg ext E anchor)
    {r : Root} (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.AvailableCheckpoint cfg ext r (S.realized_justified r) :=
  S.realized_justified_mem r hr

theorem gu_AU (S : AcceptedBlockFFGState cfg ext E anchor)
    {r : Root} (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.AvailableCheckpoint cfg ext r (S.unrealized_justified r) :=
  S.unrealized_justified_mem r hr

theorem gf_AU (S : AcceptedBlockFFGState cfg ext E anchor)
    {r : Root} (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.AvailableCheckpoint cfg ext r (S.realized_finalized r) :=
  S.realized_finalized_mem r hr

theorem guf_AU (S : AcceptedBlockFFGState cfg ext E anchor)
    {r : Root} (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    S.AvailableCheckpoint cfg ext r (S.unrealized_finalized r) :=
  S.unrealized_finalized_mem r hr

theorem gj_epoch_le_gu (S : AcceptedBlockFFGState cfg ext E anchor)
    {r : Root} (hr : E.RootKnownInScheduledPrefix cfg ext r) :
    (S.realized_justified r).epoch ≤ (S.unrealized_justified r).epoch :=
  S.realized_justified_epoch_le_unrealized r hr

end AcceptedBlockFFGState


namespace CheckpointInclusionView
variable {E : Execution Root}
end CheckpointInclusionView
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
end ChainFFGState
namespace AcceptedBlockFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}


end AcceptedBlockFFGState
end FastConfirmation.Spec

end
