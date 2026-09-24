module
public import FastConfirmationProofs.Weak.Safety.WeakOneShotSafety
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem ObserverCoherence.justified_root_known_of_trustedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      (E.store cfg ext obs n).justified_checkpoint.root ∈
        (E.store cfg ext obs n).block_roots := by
  intro n _hHn
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈
      (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
    hjustAnchor | hevidence
  · rw [hjustAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hincluded⟩ := carrier.formed_evidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor
        (E.store cfg ext obs n).justified_checkpoint :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        B.state.includedAttestations.relation hincluded
    have hanchorEpochLe : B.anchor.epoch ≤
        (E.store cfg ext obs n).justified_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext obs n).justified_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
        ((E.store cfg ext obs n).blocks B.anchor.root).slot carrier.tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
        B.anchor.root hanchorMem carrier.tip carrier.tip_carrier.known
    have hwalk : WalkKnown (E.store cfg ext obs n)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext obs n).justified_checkpoint.epoch) carrier.tip := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots hwalk

/-- Given the accepted global justified-root origin, constructing
`ObserverCoherence` reduces to supplying `committees_agree` alone:
`justified_root_known` is always derivable
(`justified_root_known_of_acceptedGlobalTrajectory` above), so it is not an
independent premise on top of the accepted FFG semantics bundle. -/
def ObserverCoherence.of_trustedTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    (hcomm : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
      E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s) :
    E.ObserverCoherence cfg ext obs where
  validity := hvalid
  committees_agree := hcomm
  justified_root_known :=
    ObserverCoherence.justified_root_known_of_trustedGlobalTrajectory
      cfg ext E B hT hanchor hboundary obs

/-- Promotion of the caller-facing premise bundle to the internal one: the
missing field, `ObserverCoherence.justified_root_known`, is *derived* from the
accepted global justified-root origin and the ordinary execution trajectory
via `ObserverCoherence.of_trustedTrajectory`. Every top-level weak theorem
already carries `B`, `hT`, `hanchor`, `hboundary`, so this promotion is always
available there and `justified_root_known` never reaches a premise list. -/
def WeakObserverPremises.toTrustedMarginAssumptions {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.WeakObserverMarginPremises cfg ext obs where
  base := hW.base
  validity := hW.validity
  coherence :=
    ObserverCoherence.of_trustedTrajectory cfg ext E B hT hanchor hboundary obs
      hW.validity hW.committees_agree


end Execution
end FastConfirmation.Spec
end
