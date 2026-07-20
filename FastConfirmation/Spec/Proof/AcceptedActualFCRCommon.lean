import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Induction
import FastConfirmation.Spec.Proof.AcceptedSelectedJustifiedOrientation
import FastConfirmation.Spec.Proof.AcceptedCandidateHistoryRecurrence

/-!
# Common accepted actual-FCR invariants

This module contains the reset-independent facts used by the primary
following-slot fold. It deliberately contains no reset-safety premise,
head conclusion, or observed source-lock law.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Causal checkpoint reflection determines the semantic checkpoint
projection at the trusted anchor.  The previously exposed `anchor_exact`
premise is therefore redundant once trajectory initialization and boundary
alignment are present. -/
theorem acceptedAnchorExact_of_trajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    B.anchor = B.state.C B.anchor.root B.anchor.epoch := by
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary 0 0
  have hreflect : B.state.C B.anchor.root B.anchor.epoch =
      get_checkpoint_for_block cfg E.genesis_store
        B.anchor.root B.anchor.epoch :=
    B.coherence.checkpoint_of_known (.genesis)
      B.anchor.root hreal.root_known B.anchor.epoch
  have htrusted := E.trustedAnchor_checkpointForBlock_of_trajectory
    cfg ext hT hanchor hboundary
  have hepoch : get_block_epoch cfg E.genesis_store B.anchor.root =
      B.anchor.epoch := by
    have := congrArg Checkpoint.epoch htrusted
    simpa only [get_checkpoint_for_block] using this
  symm
  calc
    B.state.C B.anchor.root B.anchor.epoch =
        get_checkpoint_for_block cfg E.genesis_store
          B.anchor.root B.anchor.epoch := hreflect
    _ = get_checkpoint_for_block cfg E.genesis_store B.anchor.root
          (get_block_epoch cfg E.genesis_store B.anchor.root) := by rw [hepoch]
    _ = B.anchor := htrusted

/-- Accepted endpoint certificates place the trusted anchor below every
honest endpoint's realized justified checkpoint.  Execution reflection then
turns that semantic prefix into the concrete store ancestry consumed by fork
choice. -/
theorem trustedAnchor_safeFrom_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    E.SafeFrom cfg ext B.anchor.root 0 := by
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  apply E.safeFrom_of_justified_dom_K cfg ext hdomainK
  intro w hw m _h0m hHm
  obtain ⟨_hparent, _hwalk, hjustifiedKnown⟩ := hdomainK w hw m hHm
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  obtain ⟨hjustified⟩ :=
    ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hanchorRealized :=
    E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
      cfg ext hT hanchor hboundary w m
  have hanchorRoot : E.ExecutionRoot B.anchor.root :=
    ⟨(E.store cfg ext w m).blocks B.anchor.root,
      E.blockAt_of_store_known cfg ext hanchorRealized.root_known⟩
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      hjustifiedKnown hanchorRoot (hjustified.descends_anchor cfg)

/-- The exact genesis cache field is the trusted anchor root, hence the base
case of either executable fold needs no reset or selected-helper premise. -/
theorem confirmed_zero_safeFrom_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) :
    E.SafeFrom cfg ext (E.confirmed cfg ext v 0) 0 := by
  have hconfirmedAnchor : E.confirmed cfg ext v 0 = B.anchor.root := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
    rw [E.confirmed_zero, hanchor]
    change E.genesis_store.finalized_checkpoint.root =
      E.genesis_store.justified_checkpoint.root
    rw [hgen]
    rfl
  rw [hconfirmedAnchor]
  exact E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary

/-- The exact ordered selector input is known at an actual query whenever the
previous cached confirmed root is known.  Each reset arm uses its accepted
installation realization. -/
theorem getLatestConfirmedTraceAt_input_known
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {n : ℕ}
    (hknown : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots) :
    (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknown
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hobserved :=
    E.fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary v n
  change trace.afterObserved ∈ query.store.block_roots
  cases trace.candidateHistoryCallBranch (cfg := cfg) (ext := ext) with
  | carriedUnchanged hinput _ =>
      rw [hinput.input_eq]
      simpa only [query, E.fcrStep_confirmed_root, E.fcrStep_store] using
        hknownN1
  | finalizedResetUnchanged hinput _ =>
      rw [hinput.input_eq]
      simpa only [query, E.fcrStep_store] using hfinalized.root_known
  | observedResetUnchanged hinput _ =>
      rw [hinput.input_eq]
      simpa only [query, E.fcrStep_store] using hobserved.root_known
  | strictSelected horigin _ =>
      cases horigin with
      | carried hinput =>
          rw [hinput.input_eq]
          simpa only [query, E.fcrStep_confirmed_root, E.fcrStep_store] using
            hknownN1
      | finalizedReset hinput =>
          rw [hinput.input_eq]
          simpa only [query, E.fcrStep_store] using hfinalized.root_known
      | observedReset hinput =>
          rw [hinput.input_eq]
          simpa only [query, E.fcrStep_store] using hobserved.root_known

/-- Knownness is an independent executable invariant.  A call writes back the
known result of the exact phased evaluator; between calls the cached root and
store membership are monotone. -/
theorem confirmed_known_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.confirmed cfg ext v n ∈ (E.store cfg ext v n).block_roots := by
  intro n
  induction n with
  | zero =>
      intro _hH0
      exact (E.acceptedHistoricalA32CurrentLineageAt_zero
        cfg ext B hT hanchor hboundary v).confirmed_known
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hknownN := ih hHn
      by_cases hcall : E.IsFCRCallAt cfg ext v n
      · have hresultKnown := E.getLatestConfirmedTraceAt_result_known
          cfg ext B hT hanchor hboundary hv hHn1 hknownN
        have hwrite :=
          (E.actualCandidateHistoryRecurrence cfg ext hcall).result_writeback
        rw [hwrite]
        simpa only [E.fcrStep_store] using hresultKnown
      · have hknownN1 : E.confirmed cfg ext v n ∈
            (E.store cfg ext v (n + 1)).block_roots :=
          (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
        rw [E.confirmed_succ_of_no_advance cfg ext v n hcall]
        exact hknownN1

end Execution

end FastConfirmation.Spec
