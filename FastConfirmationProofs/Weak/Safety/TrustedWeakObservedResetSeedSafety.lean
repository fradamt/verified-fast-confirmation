module
public import FastConfirmationProofs.Weak.Safety.WeakObservedResetSeedSafety
public import FastConfirmationProofs.Weak.Safety.TrustedWeakObservedRestartDynamicSafety
public import FastConfirmationProofs.Weak.Safety.WeakTrajectorySafety

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {trusted : Store Root → Prop}

theorem trusted_observedResetSeedSafety_of_acceptedDynamics
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s) :
    Weak.ObservedResetSeedSafety cfg ext E obs := by
  have hT : E.ScheduledPrefixPremises cfg ext :=
    Execution.ScheduledPrefixPremises.of_selectedMarginAssumptions
      cfg ext E hA hgen
  intro n hHn1 hcall trace hinput
  rcases Weak.trusted_weakFcrStep_certifiedBankedJustification cfg ext hA B hT hanchor
    hboundary hHn1 hcall with hgenesisArm | hcertified
  · exact Weak.ObservedResetCandidateInputAt.trusted_safeFrom_of_anchorArm cfg ext B hT
      hanchor hboundary hinput hgenesisArm
  · obtain ⟨hcert⟩ := hcertified
    have hadoption :=
      Weak.ObservedResetCandidateInputAt.trusted_guardedObservedAdoption cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hinput hcert
    rw [hinput.input_eq]
    apply E.safeFrom_of_headStep_at cfg ext
    intro w hw m hnm hHm hIH
    have hcJ : (E.weakFcrStep cfg ext obs n
          ).current_epoch_observed_justified_checkpoint.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch :=
      (hadoption w hw hHn1).trans (E.store_justified_epoch_mono cfg ext w hnm)
    rcases Nat.eq_or_lt_of_le hcJ with heq | hlt
    · exact Weak.ObservedResetCandidateInputAt.trusted_head_of_sameEpoch cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hinput (Or.inr ⟨hcert⟩) hw hnm
        hHm heq
    · exact Weak.ObservedResetCandidateInputAt.trusted_head_of_laterEpoch cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hHn1 hcall hinput
        (Or.inr ⟨hcert⟩) hw hnm hHm hIH hlt

end Weak

namespace Execution

variable (E : Execution Root)

/-! ## The weak full-rule fold with a derived reset seed -/

/-- **The weak full-rule safety theorem with a derived reset seed.**

Every root the observer's weak FCR trajectory holds, at every in-horizon
second, is an ancestor of every in-horizon honest node's fork-choice head from
the following slot onward — at an observer that is granted nothing (no honesty,
no guaranteed delivery), and whose every use of synchrony is licensed by a
broadcast certificate.

The honest head-root knownness needed by certificate dissemination follows
from `SelectedMarginDomain.justified_root_known`. No strong `E.fcr` cache
interface is required by this theorem.

`Execution.trusted_weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold` with its
last premise discharged by `Weak.trusted_observedResetSeedSafety_of_acceptedDynamics`.
Since `docs/weak-final-wave.md` W6 the call contract carries no observer-side
normative proviso, because the historical A3.2 crossing payload is manufactured
lazily at the consuming call from the fold's own strictly earlier output.  The
proviso machinery has since been deleted outright.

The premise list is exactly the conditional fold's minus
`hOR : Weak.ObservedResetSeedSafety`; the obligation's own inputs (`hW.base`,
`B`, `hanchor`, `hboundary`, and the observer's committee agreement
`hW.committees_agree`) were already carried.  The strong fold's
observer-honesty binder `hv : v ∈ E.honest` does not appear.

That list is, in full: `B` (accepted FFG semantics), `hanchor`,
`hboundary`, `hDelay`, `hpaper`, `P`, `V`, `hW`
(`WeakObserverPremises` = the selected-margin floor plus committee readback
at the observer's own store), `hCbase`
(`WeakCompletedFCRCallSupplement`: the two phase-0
coherence contracts, the balance floor, and vote-delivery lookahead) and `hfit` — **ten** premises.
Five surface duplications are gone: `hT` is *derived* from `hW.base`
(`Execution.ScheduledPrefixPremises.of_selectedMarginAssumptions`),
`hwalkDomain : PostAnchorHonestVoteTargetWalkDomain` is *derived* from
`hW.base`/`hanchor`/`hboundary`
(`Execution.postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions`),
`hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch` is *derived*
from `B`/`hT`/`hanchor`/`hboundary`
(`Execution.acceptedAnchorExact_of_trajectory` — causal checkpoint reflection at
the trusted anchor, so it restates `hboundary` through the checkpoint walk and
is not an independent premise; `docs/plumbing-spec-citations.md` P-10),
the standalone `hphase0`/`hboundaryPhase` are read off `hCbase`, and the
`synchrony`/`static_validators`/`byzantine_bound` fields of the full 7-field
call contract are read off `hW.base` when it is rebuilt internally.

Observer-wise the premise surface is exactly `hW : WeakObserverPremises` —
committee readback at the observer's own store, nothing else; `obs` is
arbitrary and may be honest.  `ObserverCoherence.justified_root_known` is
*derived* from `B`/`hT`/`hanchor`/`hboundary` inside the fold
(`WeakObserverPremises.toMarginAssumptions`), never assumed. -/
theorem trusted_weak_confirmed_root_safe_from_next_slot
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hCbase : E.WeakCompletedFCRCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n :=
  E.trusted_weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold cfg ext B
    hanchor hboundary hDelay hpaper P V hW
    hCbase hfit
    (Weak.trusted_observedResetSeedSafety_of_acceptedDynamics cfg ext hW.base hW.genesis B
      hanchor hboundary hW.committees_agree)

/-- Endpoint form of the weak full-rule theorem, matching the
paper's timing: the observer's weak confirmed root at second `n` is canonical
at every in-horizon honest endpoint in a strictly later slot.  Weak twin of
`Execution.confirmed_head_of_acceptedActualFCRFold_nextSlot`, with no honesty
binder at `obs` and no residual reset-seed obligation. Honest head-root
knownness follows from the selected-margin domain. -/
theorem trusted_weak_confirmed_root_on_honest_heads_from_next_slot
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hCbase : E.WeakCompletedFCRCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakConfirmed cfg ext obs n)) = true :=
  E.trusted_weakConfirmed_head_of_weakFullRuleFold_nextSlot cfg ext B  hanchor
    hboundary hDelay hpaper P V hW
    hCbase hfit
    (Weak.trusted_observedResetSeedSafety_of_acceptedDynamics cfg ext hW.base hW.genesis B
      hanchor hboundary hW.committees_agree)
    hw hnm hnext hHm

end Execution
end FastConfirmation.Spec
end
