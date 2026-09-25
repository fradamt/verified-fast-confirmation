module
public import FastConfirmationProofs.Weak.Safety.TrustedWeakObservedResetSeedSafety
public import FastConfirmationProofs.Weak.LocalFFG.ObserverSelectedMargin
public import FastConfirmationProofs.Weak.LocalFFG.ObserverPremiseReduction
public import FastConfirmationProofs.Weak.LocalFFG.ObserverCertificateSupply

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root) (E : Execution Root)

/-- Conditional safety at a non-honest observer. The actual-run FFG laws are
stated for the same trusted interpretation that supplies the selector state. -/
theorem nonhonest_weak_confirmed_root_safe_from_next_slot_of_trustedInterpretation
    {obs : ValidatorIndex} (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs))
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n := by
  have hcoreAnchor : premises.core.semantics.anchor = B.anchor := by
    calc
      premises.core.semantics.anchor =
          (E.withoutObserver obs).genesis_store.justified_checkpoint :=
        premises.core.anchor_eq
      _ = E.genesis_store.justified_checkpoint := rfl
      _ = B.anchor := hanchor.symm
  have hboundary : E.TrustedAnchorBoundaryAligned (cfg := cfg)
      (anchor := B.anchor) := by
    have hb := premises.core.anchor_boundary
    rw [hcoreAnchor] at hb
    simpa only [Execution.TrustedAnchorBoundaryAligned,
      Execution.withoutObserver] using hb
  exact E.trusted_weak_confirmed_root_safe_from_next_slot cfg ext B
    hanchor hboundary hDelay hpaper P V
    (E.nonhonest_weakObserverPremises hobs premises)
    (E.nonhonest_completedCalls hobs premises.core)
    premises.core.epoch_ends_fit

/-- Endpoint form. The receiver remains in the original honest set. -/
theorem nonhonest_weak_confirmed_root_on_honest_heads_from_next_slot_of_trustedInterpretation
    {obs : ValidatorIndex} (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs))
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakConfirmed cfg ext obs n)) = true := by
  have hcoreAnchor : premises.core.semantics.anchor = B.anchor := by
    calc
      premises.core.semantics.anchor =
          (E.withoutObserver obs).genesis_store.justified_checkpoint :=
        premises.core.anchor_eq
      _ = E.genesis_store.justified_checkpoint := rfl
      _ = B.anchor := hanchor.symm
  have hboundary : E.TrustedAnchorBoundaryAligned (cfg := cfg)
      (anchor := B.anchor) := by
    have hb := premises.core.anchor_boundary
    rw [hcoreAnchor] at hb
    simpa only [Execution.TrustedAnchorBoundaryAligned,
      Execution.withoutObserver] using hb
  exact E.trusted_weak_confirmed_root_on_honest_heads_from_next_slot
    cfg ext B hanchor hboundary hDelay hpaper P V
    (E.nonhonest_weakObserverPremises hobs premises)
    (E.nonhonest_completedCalls hobs premises.core)
    premises.core.epoch_ends_fit hw hnm hnext hHm

end Execution
end FastConfirmation.Spec
end
