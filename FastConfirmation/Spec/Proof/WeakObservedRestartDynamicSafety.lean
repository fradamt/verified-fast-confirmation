import FastConfirmation.Spec.Proof.AcceptedActualFCRCommon
import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
import FastConfirmation.Spec.Proof.WeakObservedRestartAdoption

/-!
# Spec / Proof / WeakObservedRestartDynamicSafety

The arm-by-arm discharge of `Weak.ObservedResetSeedSafety`
(`WeakTrajectorySafety.lean`), the single open obligation of the weak
full-rule fold.  Weak twin of
`Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`
(`AcceptedObservedRestartDynamicSafety.lean`), with the querying node's
honesty binder dropped.

The strong proof splits the endpoint's realized justified epoch `J.epoch`
against the banked checkpoint's epoch `c.epoch` two ways — `c.epoch = J.epoch`
by accountable uniqueness, `c.epoch < J.epoch` by an honest formation-target
vote plus the `safeFrom_of_headStep_at` strong induction — after first using
the querying node's honesty twice, to relay the banked root and the GU carrier
tip.  Rule delta 5's head-indexed banking replaces both relays
(`Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`,
`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`), and stage 2
(`WeakObservedRestartAdoption.lean`) replaces the epoch bound that feeds the
split.

This file adds the arms that the split itself needs, in the order of
`docs/weak-full-rule.md`'s staged plan:

* **stage 3, the anchor arm** — `Weak.genesisRoot_safeFrom_of_acceptedGlobalTrajectory`
  and its call-scoped form.  The weak invariant
  `Weak.CertifiedBankedJustification` degenerates to "the banked root is a
  genesis block root", which has no supplier and no certificate at all; the
  genesis store's `block_roots` is the anchor singleton, so this arm never
  reaches the epoch split — it closes outright by
  `Execution.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`, whose honesty
  is quantified over the *receiving* endpoint only.
* **stage 4, the same-epoch arm** — `Weak.sameEpochCertified_head_at_endpoint`
  and its call-scoped form `Weak.ObservedResetCandidateInputAt.head_of_sameEpoch`.
  When the endpoint's realized justified epoch *equals* the banked checkpoint's
  epoch, accountable uniqueness (`Execution.certified_justified_unique`,
  honesty-free) identifies the two roots and
  `head_ge_of_justified_ge_K` puts the banked root below the endpoint's head.
  Both certificates are produced rather than assumed: the endpoint's by
  `ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate` at its own
  causal store, the banked checkpoint's by
  `Weak.certifiedJustified_of_acceptedAU` from the branch's own
  `observed_eq_head_unrealized` conjunct — the observer's head is a known block
  of its own store (`Weak.head_known_at_observer`), so the banked value is that
  head's `GU`, which carries accepted formation evidence.  Knownness of the
  banked root at the endpoint is the landed
  `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`; its dissemination
  gate `E.slot_at h.second ≤ E.slot_at m` is discharged, for every certificate
  witnessing the invariant, by `second_le` and `Execution.slot_at_mono` — the
  same temporal carry stage 2 uses, with no new bridge.

Stage 5 (the strictly-newer-endpoint arm, `c.epoch < J.epoch`) is not in this
file; until it lands, `Weak.ObservedResetSeedSafety` stays pinned in
`WeakTrajectorySafety.lean`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Certificate supply at a weak call

The arms below take rule delta 5's input invariant at the *query* store
`E.weakFcrStep`, indexed at the call's own boundary second `n + 1`.  That is
exactly one `certifiedBankedJustification_update` past the landed trajectory
invariant, so it is supplied rather than assumed. -/

/-- **The banking invariant at the weak query store.** The trajectory invariant
`Weak.weakFcr_certifiedBankedJustification` holds at the carried store at `n`;
re-seating it on the call second's store and applying rule delta 5's own
maintenance lemma (`Weak.certifiedBankedJustification_update`) moves it onto
`E.weakFcrStep cfg ext obs n` at index `n + 1`, which is the shape the
observed-reset arms consume.  No honesty hypothesis at `obs`. -/
theorem weakFcrStep_certifiedBankedJustification
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n) :
    Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
  have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg (Nat.le_succ n) hH
  have hseat : Weak.CertifiedBankedJustification cfg ext E obs n
      { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) } :=
    (Weak.weakFcr_certifiedBankedJustification cfg ext hA B hT hanchor hboundary
      obs n hHn).transport cfg ext (Nat.le_refl n) rfl
  exact Weak.certifiedBankedJustification_update cfg ext hA B hT hanchor
    hboundary (obs := obs) (n := n) hH hcall
    (fcr_store := { E.weakFcr cfg ext obs n with
      store := E.store cfg ext obs (n + 1) }) rfl hseat

/-! ## Stage 3 — the anchor arm -/

/-- **Every genesis block root is safe from every second.** The genesis store
built by `get_forkchoice_store` knows exactly one block, the anchor block, so a
root in `E.genesis_store.block_roots` *is* `B.anchor.root`, and the trusted
anchor is below every in-horizon honest endpoint's head from second `0`
(`Execution.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`).

This is the whole content of the anchor arm of
`Weak.CertifiedBankedJustification`: that arm records only genesis membership
of the banked root — it carries no supplier, no certificate, and hence no epoch
bound — so it cannot be routed through the adoption law of stage 2, and does
not need to be. -/
theorem genesisRoot_safeFrom_of_acceptedGlobalTrajectory
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {r : Root} (hr : r ∈ E.genesis_store.block_roots) (q : ℕ) :
    E.SafeFrom cfg ext r q := by
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hT.genesis
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hroot := congrArg Checkpoint.root hanchor
    rw [hgeq] at hroot
    simpa only [get_forkchoice_store] using hroot
  have hrEq : r = B.anchor.root := by
    rw [hgeq] at hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    rw [hr, hanchorRoot]
  rw [hrEq]
  exact (E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary).mono cfg ext E (Nat.zero_le q)

/-- **The observed-reset seed is safe whenever its banking certificate
degenerates.** Call-scoped form of the anchor arm: at a weak FCR call whose
candidate came from the epoch-start restart branch, if the banked checkpoint's
root is a genesis block root then the restarted-from root is `SafeFrom` at the
call second.

No honesty binder at `obs`, no certificate, and no epoch premise — the arm is
closed before the epoch split of the strong proof is reached. -/
theorem ObservedResetCandidateInputAt.safeFrom_of_anchorArm
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hgenesis : ((E.weakFcrStep cfg ext obs n).current_epoch_observed_justified_checkpoint).root ∈
      E.genesis_store.block_roots) :
    E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
  rw [hinput.input_eq]
  exact Weak.genesisRoot_safeFrom_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hgenesis (n + 1)

/-! ## Stage 4 — the same-epoch arm -/

/-- **Accepted AU evidence certifies a checkpoint.** The formation evidence
behind `B.state.AU` carries an included-attestation certificate, which the
accepted included-attestation relation turns into a `CertifiedJustified` chain
from the trusted anchor.

Honesty-free and node-free: `AcceptedChainFFGState.formed_evidence` and
`AcceptedIncludedAttestationRelation.relation` are facts about the semantic FFG
state, not about any node's store.  The step is currently inlined inside
`Weak.auTip_walkKnown`; it is named here because the same-epoch arm needs the
certificate itself rather than the epoch bound it implies. -/
theorem certifiedJustified_of_acceptedAU
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {tip : Root} {c : Checkpoint Root} (hAU : B.state.AU cfg ext tip c) :
    CertifiedJustified cfg E B.anchor c := by
  obtain ⟨_carrier, _hdescends, hformed⟩ := hAU
  obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
  exact IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg)
    (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
      B.state.includedAttestations) hincluded

/-- **The same-epoch arm of the endpoint head step.** A certified justified
checkpoint whose epoch equals an in-horizon honest endpoint's own realized
justified epoch is below that endpoint's fork-choice head.

Accountable same-epoch uniqueness (`Execution.certified_justified_unique`)
identifies the two roots outright, and `head_ge_of_justified_ge_K` lifts the
resulting (reflexive) justified-root ancestry to the head.  Weak twin of the
`heq` branch of `Execution.ObservedResetCandidateInputAt.
safeFrom_of_acceptedDynamics`'s internal split: the only honesty binder is on
the endpoint `w`, which the weak model keeps, and the endpoint's own
certificate is read off its causal store by
`ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate`. -/
theorem sameEpochCertified_head_at_endpoint
    {E : Execution Root} (hacc : FFGAccountabilityAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {c : Checkpoint Root} (hcCertified : CertifiedJustified cfg E B.anchor c)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hHm : E.WithinHorizon cfg m)
    (hcKnown : c.root ∈ (E.store cfg ext w m).block_roots)
    (hepoch : c.epoch = (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true := by
  obtain ⟨ast, ablk, hgeq, hslotEq, _hparentNe⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgeq, hslotEq⟩
  obtain ⟨hwfM, hwalkM, hjustM⟩ :=
    E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT hanchor hboundary
      w hw m hHm
  obtain ⟨hJCertified⟩ :=
    Execution.ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hrootEq : c.root = (E.store cfg ext w m).justified_checkpoint.root :=
    E.certified_justified_unique cfg ext hacc hcCertified hJCertified hepoch
  refine head_ge_of_justified_ge_K cfg hwfM hwalkM hjustM hcKnown ?_
  rw [hrootEq]
  exact is_ancestor_refl _ _

/-- **The banked observed checkpoint carries an accepted certificate.** The
epoch-start restart branch's own `observed_eq_head_unrealized` conjunct says
the banked value is the query head's unrealized justification; the head is a
known block of the observer's own store
(`Weak.head_known_at_observer`, honesty-free), so the accepted contracts
identify that value with the head's `GU`
(`Execution.accepted_unrealized_justification_eq`) and `gu_AU` supplies the
formation evidence.

This is the weak replacement for the strong proof's `hreal.certified`, which
reads the certificate off an observed-reset *realization* record that is only
available at an honest node. -/
theorem ObservedResetCandidateInputAt.certifiedJustified
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace) :
    CertifiedJustified cfg E B.anchor
      (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint := by
  have hheadKnown : (get_head cfg (E.store cfg ext obs (n + 1))).root ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)
  have hGU : (E.weakFcrStep cfg ext obs n
      ).current_epoch_observed_justified_checkpoint =
      B.state.GU (get_head cfg (E.store cfg ext obs (n + 1))).root := by
    rw [hinput.observed_eq_head_unrealized, E.weakFcrStep_store]
    exact E.accepted_unrealized_justification_eq
      B.coherence.toAcceptedFFGSelectorCoherence obs (n + 1) hheadKnown
  refine Weak.certifiedJustified_of_acceptedAU cfg ext B
    (tip := (get_head cfg (E.store cfg ext obs (n + 1))).root) ?_
  rw [hGU]
  exact B.state.gu_AU cfg ext
    (E.acceptedRoot_of_causal_known cfg ext
      (E.store_causal cfg ext obs (n + 1)) hheadKnown)

/-- **The same-epoch arm at a weak observed-reset call.** If an in-horizon
honest endpoint's realized justified epoch equals the banked checkpoint's own
epoch, the restarted-from root is below that endpoint's fork-choice head.

Every input is produced from the weak stack: the banked checkpoint's
certificate by `Weak.ObservedResetCandidateInputAt.certifiedJustified`, its
knownness at the endpoint by
`Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` (whose gate is
discharged from each witnessing certificate's `second_le` through
`Execution.slot_at_mono` — the installation second is carried forward to the
endpoint's second without any further temporal hypothesis), and the endpoint
step itself by `Weak.sameEpochCertified_head_at_endpoint`.  No honesty binder
at `obs`. -/
theorem ObservedResetCandidateInputAt.head_of_sameEpoch
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hnm : n + 1 ≤ m)
    (hHm : E.WithinHorizon cfg m)
    (hepoch : (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint.epoch =
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root ((E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint).root) = true := by
  have hacc : FFGAccountabilityAssumptions cfg ext E :=
    Execution.SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA
  have hcKnown := Weak.bankedRoot_known_at_all_honest_endpoints_at_observer
    cfg ext hA B hT hanchor hboundary hsync hji hA.genesis hcomm hinv hw hHm
    (fun h => (E.slot_at_mono cfg h.second_le).trans (E.slot_at_mono cfg hnm))
  exact Weak.sameEpochCertified_head_at_endpoint cfg ext hacc B hT hanchor
    hboundary
    (Weak.ObservedResetCandidateInputAt.certifiedJustified cfg ext B hT hanchor
      hboundary hinput)
    hw hHm hcKnown hepoch

end Weak

end FastConfirmation.Spec
