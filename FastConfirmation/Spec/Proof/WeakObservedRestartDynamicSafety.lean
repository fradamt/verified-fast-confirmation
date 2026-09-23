module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRCommon
public import FastConfirmation.Spec.Proof.AcceptedCurrentSameEndpointSource
public import FastConfirmation.Spec.Proof.SelectedCoveredMarginConstruction
public import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
public import FastConfirmation.Spec.Proof.WeakObservedRestartAdoption
public import FastConfirmation.Spec.Proof.WeakSelectedStrictEdgeFilterSupply

@[expose] public section

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
* **stage 5, the later-epoch arm** —
  `Weak.ObservedResetCandidateInputAt.head_of_laterEpoch`, taking the
  slot-indexed induction hypothesis of `Execution.safeFrom_of_headStep_at` as a
  premise.  When the endpoint's realized justified epoch is *strictly* greater
  than the banked checkpoint's, that justified checkpoint is past the trusted
  anchor, so `Execution.globalJustified_honestTarget` — quantified over the
  *endpoint*, honesty-free at `obs` — exposes its honest causal formation vote;
  the induction hypothesis puts the banked root on the voter's head, the
  voter's own target walk puts the endpoint's justified root on the same head
  at the epoch boundary, and walk composition orders them.  The strong proof's
  three uses of the querying node's honesty inside this arm are replaced by
  `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` (the relay),
  `Weak.weakFcrStep_observed_known` (query-store knownness) and
  `Weak.ObservedResetCandidateInputAt.banked_blockEpoch_le` (the boundary
  placement of the banked root, from the accepted `AU` geometry of the query
  head's own unrealized justification rather than from a reset-realization
  record).  Only the `≤` half of the strong proof's previous-epoch equation is
  needed, which is why the honest-only cache-installation provenance never
  appears.

The three arms are composed into `Weak.ObservedResetSeedSafety` itself in
`WeakObservedResetSeedSafety.lean`.
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
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hT.genesis_structure
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
  obtain ⟨ast, ablk, hgeq, hslotEq, _hparentNe⟩ := hT.genesis_structure
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

/-- **The banked observed checkpoint is the query head's accepted unrealized
justification.** The epoch-start restart branch's own
`observed_eq_head_unrealized` conjunct says the banked value is the query
head's unrealized justification; the head is a known block of the observer's
own store (`Weak.head_known_at_observer`, honesty-free), so the accepted
contracts identify that value with the head's `GU`
(`Execution.accepted_unrealized_justification_eq`) and `gu_AU` turns it into
accepted formation evidence at the head itself.

Named because both the same-epoch arm (for the certificate the evidence
carries) and the later-epoch arm (for the checkpoint's own chain geometry)
start from it, and neither needs any honesty at `obs`. -/
theorem ObservedResetCandidateInputAt.bankedAU
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace) :
    B.state.AU cfg ext (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1))
      (get_current_balance_source (E.weakFcrStep cfg ext obs n)))
      (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint := by
  have hheadKnown : (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1))
      (get_current_balance_source (E.weakFcrStep cfg ext obs n))) ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    Weak.get_certified_head_known cfg ext _ _
      (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1))
  have hGU : (E.weakFcrStep cfg ext obs n
      ).current_epoch_observed_justified_checkpoint =
      B.state.GU (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1))
      (get_current_balance_source (E.weakFcrStep cfg ext obs n))) := by
    rw [hinput.observed_eq_head_unrealized, E.weakFcrStep_store]
    exact E.accepted_unrealized_justification_eq
      B.coherence.toAcceptedFFGSelectorCoherence obs (n + 1) hheadKnown
  rw [hGU]
  exact B.state.gu_AU cfg ext
    (E.acceptedRoot_of_causal_known cfg ext
      (E.store_causal cfg ext obs (n + 1)) hheadKnown)

/-- **The banked observed checkpoint carries an accepted certificate.** The
formation evidence of `Weak.ObservedResetCandidateInputAt.bankedAU`, read as a
`CertifiedJustified` chain from the trusted anchor.

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
        ).current_epoch_observed_justified_checkpoint :=
  Weak.certifiedJustified_of_acceptedAU cfg ext B
    (Weak.ObservedResetCandidateInputAt.bankedAU cfg ext B hT hanchor hboundary
      hinput)

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

/-! ## Stage 5 — the later-epoch arm -/

/-- **The banked checkpoint's root block is no newer than the checkpoint's own
epoch.** `Weak.auCheckpoint_blockEpoch_le` at the query head: the banked value
is that head's accepted `AU` checkpoint
(`Weak.ObservedResetCandidateInputAt.bankedAU`), so it is the block the
observer's own ancestor walk from the head lands on at the first slot of its
epoch, which is at or below that boundary.

This is the weak, honesty-free replacement for the strong proof's
`ResetCheckpointRealizedAt.root_slot_le_boundary`, which is a field of an
observed-reset *realization* record available only at an honest node.  The
strong proof uses that field twice — once to force the checkpoint's epoch to be
exactly the previous one (`observed_checkpoint_previous_epoch`), once to place
the checkpoint's block below the endpoint's justified boundary — and the epoch
form below covers both, because the later-epoch arm needs only the `≤` half of
the previous-epoch equation. -/
theorem ObservedResetCandidateInputAt.banked_blockEpoch_le
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace) :
    get_block_epoch cfg (E.store cfg ext obs (n + 1))
        ((E.weakFcrStep cfg ext obs n
          ).current_epoch_observed_justified_checkpoint).root ≤
      (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint.epoch :=
  Weak.auCheckpoint_blockEpoch_le cfg ext B hT hanchor hboundary obs (n + 1)
    (Weak.get_certified_head_known cfg ext _ _
      (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))
    (Weak.ObservedResetCandidateInputAt.bankedAU cfg ext B hT hanchor hboundary
      hinput)

/-- **The call's boundary epoch is at most one past the banked checkpoint's own
epoch.** The branch's `observed_previous_epoch` conjunct puts the *block* epoch
of the banked root exactly one below the query store's current epoch, and
`banked_blockEpoch_le` bounds that block epoch by the checkpoint's declared
epoch.

The strong twin `observed_checkpoint_previous_epoch` proves the sharper
equation `c.epoch + 1 = e`, but its lower bound `c.epoch < e` is exactly the
half that reads the cache installation's provenance
(`ObservedResetCandidateInputAt.acceptedInstallation`) and therefore needs the
querying node to be honest.  The later-epoch arm consumes only the upper bound,
so the honest-only half is never required. -/
theorem ObservedResetCandidateInputAt.currentEpoch_le_banked_succ
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace) :
    get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) ≤
      (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint.epoch + 1 := by
  have hprev := hinput.observed_previous_epoch
  rw [E.weakFcrStep_store cfg ext obs n] at hprev
  have hle := Weak.ObservedResetCandidateInputAt.banked_blockEpoch_le cfg ext B
    hT hanchor hboundary hinput
  rw [← hprev]
  exact Nat.add_le_add_right hle 1

/-- **The later-epoch arm at a weak observed-reset call.** If an in-horizon
honest endpoint's realized justified epoch is *strictly greater* than the
banked checkpoint's own epoch, the restarted-from root is still below that
endpoint's fork-choice head — given the slot-indexed induction hypothesis of
`Execution.safeFrom_of_headStep_at`, which supplies the same conclusion at every
strictly earlier in-horizon honest store.

Weak twin of the `hlt` branch of `Execution.ObservedResetCandidateInputAt.
safeFrom_of_acceptedDynamics`'s internal split.  The endpoint's justified
checkpoint is not the trusted anchor (its epoch exceeds the banked one, which
the banked certificate already places at or above the anchor), so
`Execution.globalJustified_honestTarget` — quantified over the *endpoint*, not
over `obs` — exposes an honest causal formation vote for it.  The induction
hypothesis puts the banked root on that voter's own head, the voter's target
walk puts the endpoint's justified root on the same head at the epoch boundary,
and walk composition orders the two.  Semantic reflection then transports the
resulting descent back to the endpoint's store and
`head_ge_of_justified_ge_K` lifts it to the head.

The three places the strong proof reads the querying node's honesty are all
replaced here:

* the banked root's knownness at the voter's store, strongly
  `PaperSafetySynchrony.block_relay` with `obs` as sender, weakly
  `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` (certificate
  dissemination, gate discharged by `second_le` and `Execution.slot_at_mono`);
* the banked root's knownness at the observer's own query store, strongly
  `ResetCheckpointRealizedAt.root_known`, weakly
  `Weak.weakFcrStep_observed_known` (rule delta 5's `banked_known`);
* the banked root's boundary placement, strongly
  `ResetCheckpointRealizedAt.root_slot_le_boundary`, weakly
  `Weak.ObservedResetCandidateInputAt.banked_blockEpoch_le` (the accepted `AU`
  geometry of the query head's own unrealized justification).

The strong proof's fourth honesty site,
`ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption`, produces the
epoch bound that feeds the split rather than this arm; it is stage 2's
`Weak.bankedCheckpoint_epoch_le_honestJustified`. -/
theorem ObservedResetCandidateInputAt.head_of_laterEpoch
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
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hnm : n + 1 ≤ m)
    (hHm : E.WithinHorizon cfg m)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m → E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root ((E.weakFcrStep cfg ext obs n
          ).current_epoch_observed_justified_checkpoint).root) = true)
    (hlt : (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint.epoch <
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root ((E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint).root) = true := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  let c := (E.weakFcrStep cfg ext obs n
    ).current_epoch_observed_justified_checkpoint
  let J := (E.store cfg ext w m).justified_checkpoint
  -- The call's own boundary geometry, all honesty-free at `obs`.
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hcall
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.weakFcrStep_store, E.store_current_slot] using hinput.epoch_start
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) := by
    have hraw : E.slot_at cfg (n + 1) =
        compute_start_slot_at_epoch cfg
          (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
      simp only [compute_slots_since_epoch_start,
        compute_start_slot_at_epoch] at hstartZero ⊢
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
        (Nat.div_mul_le_self _ cfg.slots_per_epoch)
    simpa only [get_current_store_epoch, E.store_current_slot] using hraw
  -- The banked value: its certificate, its knownness, and its block epoch.
  have hcCertified : CertifiedJustified cfg E B.anchor c :=
    Weak.ObservedResetCandidateInputAt.certifiedJustified cfg ext B hT hanchor
      hboundary hinput
  have hcKnownObs : c.root ∈ (E.store cfg ext obs (n + 1)).block_roots :=
    Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
  have hcExecutionRoot : E.ExecutionRoot c.root :=
    ⟨(E.store cfg ext obs (n + 1)).blocks c.root,
      E.blockAt_of_store_known cfg ext hcKnownObs⟩
  have hcBlockEpoch : get_block_epoch cfg (E.store cfg ext obs (n + 1))
      c.root ≤ c.epoch :=
    Weak.ObservedResetCandidateInputAt.banked_blockEpoch_le cfg ext B hT hanchor
      hboundary hinput
  have hcKnownAt : ∀ k : ValidatorIndex, k ∈ E.honest → ∀ j : ℕ, n + 1 ≤ j →
      E.WithinHorizon cfg j → c.root ∈ (E.store cfg ext k j).block_roots :=
    fun k hk j hj hHj =>
      Weak.bankedRoot_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
        hanchor hboundary hsync hji hA.genesis hcomm hinv hk hHj
        (fun h => (E.slot_at_mono cfg h.second_le).trans (E.slot_at_mono cfg hj))
  -- The endpoint's own domain data.
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary
  obtain ⟨hwfM, hwalkM, hjustM⟩ := hdomainK w hw m hHm
  have hcKnownM : c.root ∈ (E.store cfg ext w m).block_roots :=
    hcKnownAt w hw m hnm hHm
  -- The endpoint's justified checkpoint is past the anchor, so it has an
  -- honest causal formation vote.
  have hanchorLeC : B.anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcCertified
  have hJne : (E.store cfg ext w m).justified_checkpoint ≠ B.anchor := by
    intro hEq
    have hEpochEq := congrArg Checkpoint.epoch hEq
    exact (Nat.ne_of_lt (hanchorLeC.trans_lt hlt)) hEpochEq.symm
  obtain ⟨htarget⟩ :=
    Execution.globalJustified_honestTarget (E := E) cfg ext B hT hanchor
      hboundary hJne
  have hstartJLeVote : compute_start_slot_at_epoch cfg J.epoch ≤
      htarget.vote_slot := by
    have hmulDiv := Nat.div_mul_le_self htarget.vote_slot cfg.slots_per_epoch
    have hdiv : htarget.vote_slot / cfg.slots_per_epoch = J.epoch := by
      simpa only [compute_epoch_at_slot] using
        htarget.target_epoch_eq_vote_epoch.symm
    rw [hdiv] at hmulDiv
    simpa only [compute_start_slot_at_epoch] using hmulDiv
  have heLeJ : get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) ≤
      J.epoch :=
    (Weak.ObservedResetCandidateInputAt.currentEpoch_le_banked_succ cfg ext B hT
      hanchor hboundary hinput).trans (Nat.succ_le_of_lt hlt)
  have hboundaryLeVote : E.slot_at cfg (n + 1) ≤ htarget.vote_slot := by
    calc
      E.slot_at cfg (n + 1) = compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) :=
        hslotBoundary
      _ ≤ compute_start_slot_at_epoch cfg J.epoch :=
        Nat.mul_le_mul_right cfg.slots_per_epoch heLeJ
      _ ≤ htarget.vote_slot := hstartJLeVote
  have hnSecond : n + 1 ≤ htarget.second := by
    have hslotStartLe := E.query_slot_start_le_of_slot_ge_minimal cfg ext hA
      (q := n + 1) (ni := htarget.second) (by
        rw [htarget.second_slot]
        exact hboundaryLeVote)
    simpa only [hstartEq] using hslotStartLe
  have hsecondLt : E.slot_at cfg htarget.second < E.slot_at cfg m := by
    rw [htarget.second_slot]
    exact htarget.before_endpoint
  -- The induction hypothesis at the formation voter's own store.
  have hheadC : is_ancestor
      (E.store cfg ext htarget.validator htarget.second)
      (get_head cfg (E.store cfg ext htarget.validator htarget.second))
      (get_node_for_root c.root) = true :=
    hIH htarget.validator htarget.validator_honest htarget.second hnSecond
      hsecondLt htarget.second_within
  obtain ⟨hwfK, hwalkK, _hjustK⟩ :=
    hdomainK htarget.validator htarget.validator_honest htarget.second
      htarget.second_within
  have hheadK : (get_head cfg
      (E.store cfg ext htarget.validator htarget.second)).root ∈
      (E.store cfg ext htarget.validator htarget.second).block_roots :=
    E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT hanchor hboundary
      htarget.validator_honest htarget.second htarget.second_within
  have hcKnownK : c.root ∈
      (E.store cfg ext htarget.validator htarget.second).block_roots :=
    hcKnownAt htarget.validator htarget.validator_honest htarget.second
      hnSecond htarget.second_within
  have hcAgree : (E.store cfg ext obs (n + 1)).blocks c.root =
      (E.store cfg ext htarget.validator htarget.second).blocks c.root :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs (n + 1))
      (E.blockProvenance cfg ext htarget.validator htarget.second)
      hcKnownObs hcKnownK
  have hcSlotLeTarget :
      ((E.store cfg ext htarget.validator htarget.second).blocks c.root).slot ≤
        compute_start_slot_at_epoch cfg J.epoch := by
    rw [← hcAgree]
    have hslotLt : ((E.store cfg ext obs (n + 1)).blocks c.root).slot <
        (c.epoch + 1) * cfg.slots_per_epoch := by
      have hdiv : ((E.store cfg ext obs (n + 1)).blocks c.root).slot /
          cfg.slots_per_epoch < c.epoch + 1 := by
        simpa only [get_block_epoch, compute_epoch_at_slot, Nat.lt_succ_iff]
          using hcBlockEpoch
      exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).1 hdiv
    have hmul : (c.epoch + 1) * cfg.slots_per_epoch ≤
        J.epoch * cfg.slots_per_epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch (Nat.succ_le_of_lt hlt)
    simpa only [compute_start_slot_at_epoch] using
      Nat.le_of_lt (hslotLt.trans_le hmul)
  -- The formation vote's target is the endpoint's justified root, reached by
  -- the voter's own boundary walk from its head.
  have htargetRoot : get_checkpoint_block cfg
      (E.store cfg ext htarget.validator htarget.second)
      (get_head cfg
        (E.store cfg ext htarget.validator htarget.second)).root J.epoch =
      J.root := by
    have htargetData : (honest_attestation_data cfg ext
        (E.store cfg ext htarget.validator htarget.second)
        htarget.vote_slot htarget.index).target = J := by
      simpa only [honest_attestation_data_eq] using htarget.target_eq
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext htarget.validator htarget.second)
      htarget.vote_slot htarget.index
    rw [htargetData] at hroot
    exact hroot.symm
  have heta : (get_ancestor
      (E.store cfg ext htarget.validator htarget.second)
      (get_node_for_root (get_head cfg
        (E.store cfg ext htarget.validator htarget.second)).root)
      (compute_start_slot_at_epoch cfg J.epoch)).root = J.root := by
    simpa only [get_checkpoint_block, get_node_for_root] using htargetRoot
  have htargetSpec := get_ancestor_spec hwfK htarget.target_walk
  simp only [get_node_for_root] at heta
  rw [heta] at htargetSpec
  have hJK : J.root ∈
      (E.store cfg ext htarget.validator htarget.second).block_roots :=
    htargetSpec.1
  have hJcK : is_ancestor
      (E.store cfg ext htarget.validator htarget.second)
      (get_node_for_root J.root) (get_node_for_root c.root) = true := by
    have hcomp := get_ancestor_comp_root hwfK hcSlotLeTarget
      (hwalkK c.root hcKnownK _ hheadK)
    rw [is_ancestor_node_root] at hheadC
    simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hheadC ⊢
    simp only [get_node_for_root] at hheadC hcomp
    rw [heta, hheadC] at hcomp
    exact hcomp
  have hsemantic : E.RootDescends J.root c.root :=
    E.rootDescends_of_store_ancestor
      (E.blockProvenance cfg ext htarget.validator htarget.second)
      hwfK (hwalkK c.root hcKnownK J.root hJK) hJcK
  refine head_ge_of_justified_ge_K cfg hwfM hwalkM hjustM hcKnownM ?_
  exact (E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
    hjustM hcExecutionRoot hsemantic).2

end Weak

end FastConfirmation.Spec

end
