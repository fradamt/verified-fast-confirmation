module
public import FastConfirmationProofs.Weak.Certificates.WeakCertifiedHead
public import FastConfirmationModel.Weak.WeakSynchrony
public import FastConfirmationProofs.Execution.StoreInvariants.CheckpointDomain
public import FastConfirmationProofs.Weak.Certificates.WeakCertificateDissemination
public import FastConfirmationProofs.Weak.Selection.WeakAncestryTransport
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Execution.Trajectory.ExecutionClock
public import FastConfirmationProofs.FCRRule.MinimalSelectedDomain
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.Weak.Common.WeakFCRCallContracts

@[expose] public section

/-!
# Spec / Proof / WeakBankedJustification

Rule delta 5's input invariant (`Weak.CertifiedBankedJustification`), its
consumption lemmas, and its maintenance along the actual weak trajectory,
stated over the **revised** rule: the gated epoch-start write banks the
certified head's *own* unrealized justification,
`store.unrealized_justifications (get_head store).root`, rather than the
store-global running maximum `previous_epoch_greatest_unrealized_checkpoint`.

## Why the rule was revised (the branch-switch finding, resolved)

An earlier form of rule delta 5 banked the store-global running maximum.  The
input invariant then had to assert `banked_below_supplier` — that the banked
root lies on the certified head's chain — and **that field is false in
general**: the running maximum is captured at the end of the previous epoch,
while the gate certifies the head at the *boundary*, and between those two
moments the store's checkpoints may move branch
(`update_unrealized_checkpoints` replaces the unrealized-justified field on
any strictly higher epoch, from any accepted carrier on any branch).  An
observer holding `C_A` (epoch `e−1`, branch A) at the capture second and then
receiving a branch-B block justifying `C_B` at epoch `e` enters epoch `e` with
a branch-B head: the gate passes and banks `C_A`, which the head's certificate
does not cover.  Placing `C_A` and `C_B` on one chain is an FFG-safety-grade
claim about conflicting certified justifications at *different* epochs; it does
not follow from the store definitions.

Francesco's revision removes the claim instead of assuming it: **bank only a
justification observed in a certified block**.  With the banked value read out
of the head's own `unrealized_justifications` entry, coverage by the head
certificate is chain-intrinsic — the accepted FFG contracts
(`AcceptedFFGTransitionCoherence.au_checkpoint_of_known`, causal-store
quantified and honesty-free) place `store.unrealized_justifications b` on `b`'s
own ancestry — so the ancestry is a *theorem* about the rule rather than a
field of the invariant.  When a side branch carried a higher justification the
revised rule banks the head-chain one instead: a lower epoch, hence strictly
stricter in every recency guard that reads the banked value, so safety-free;
the balance-source deviation is benign in-model under `StaticValidatorSet`.
`previous_epoch_greatest_unrealized_checkpoint` keeps its strong (ungated)
writes for field-for-field parity with the strong rule but is **no longer
consumed** by the weak banking; the rotation lemmas about it are retained here
for that parity and are marked as such.

## What is delivered

* `Weak.has_broadcast_certificate_span_nonempty` — a true certificate forces
  a non-empty span.
* `Weak.checkpoint_state_key_of_broadcast_certificate` — a true certificate
  forces its balance source to be a keyed checkpoint state (same route as
  `Execution.checkpoint_state_key_of_one_confirmed` /
  `Execution.get_attestation_score_unkeyed_eq_zero`, `CheckpointDomain.lean`).
* `Weak.acceptedOriginRoot_known_at_observer`,
  `Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory`,
  `Weak.justifiedRoot_known_at_observer`, `Weak.head_known_at_observer` — the
  accepted-FFG knownness facts restated at a possibly-Byzantine observer,
  copies-with-binder-dropped exactly as
  `ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`
  (`WeakOneShotSafety.lean`) was.
* `Weak.auCheckpoint_known_and_below_tip` — **the chain-intrinsic ancestry**:
  a checkpoint with accepted AU evidence at a known tip is not only known in
  the observer's own store (`AcceptedSelectorAUCarrier.checkpointRoot_known`'s
  conclusion) but sits *on that tip's chain*.  The repo had the knownness half
  only; the ancestry half is the `get_ancestor_comp` step the knownness proof
  derives and discards.
* `Weak.blockUnrealizedJustification_known_and_below` — its specialization to
  the rule's actual read, `store.unrealized_justifications (get_head store)
  .root`, which is exactly what the revised gate banks.
* `Weak.BankedJustificationCertificate` / `Weak.CertifiedBankedJustification`
  — the certified-arm evidence package and the one-shot input invariant.  The
  ancestry field is gone; in its place the structure carries the **raw
  equation** `banked_eq` ("the banked checkpoint is the supplier's own
  unrealized justification"), keeping the structure executable-flavored, with
  ancestry derived at consumption from the accepted bundle.
* `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer` and
  `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` — the
  consumption lemmas: the supplier *and* the banked root are known at every
  honest endpoint past the gate, in both arms of the invariant (anchor arm via
  genesis membership + `Execution.store_storeLE`, certified arm via
  `Execution.certificate_dissemination` plus the chain-intrinsic ancestry).
* `Weak.update_fcv_observed_exact`, `Weak.weakFcr_previousGreatest_succ_exact`,
  `Weak.weakFcr_previousGreatest_origin`,
  `Weak.weakFcr_previousGreatest_known` — the weak twins of the strong
  bookkeeping rotation lemmas, gated-rule aware (the last two now cover the
  *vestigial* field).
* `Weak.weakFcr_observed_known`, `Weak.weakFcrStep_observed_known` —
  `banked_known` discharged in full along the actual weak trajectory,
  unconditionally and with no honesty hypothesis anywhere.
* `Weak.certifiedBankedJustification_update`,
  `Weak.weakFcr_certifiedBankedJustification` — **the maintenance lemmas**,
  now closed: three cases (not an epoch start / gate false ⇒ re-index the
  existing witness; gate true ⇒ the certified arm at `second := n + 1`,
  `supplier :=` the boundary head, `banked_eq` read straight off the revised
  write), and the trajectory induction seeded at the genesis initializer
  (which banks the anchor store's `finalized_checkpoint`, in
  `E.genesis_store.block_roots` ⇒ anchor arm).

## Honesty audit of the installation-provenance machinery

Every component the maintenance lemmas need from the strong development is
honesty-free, either because there is no honesty binder at all
(`ExactPrefixAcceptedFFGSemantics.causalStoreGlobalProjection`,
`globalJustified_anchor_or_AUEvidence`,
`Execution.accepted_unrealized_justification_eq`,
`AcceptedSelectorAUCarrier.checkpointRoot_known`,
`AcceptedFFGTransitionCoherence.au_checkpoint_of_known` — quantified over
`E.CausalStore`, not `E.honest`) or because the binder is routed only into
node-generic store geometry (`store_causal`, `store_parentSlotLt`,
`store_walkKnownK`, `store_storeLE`, `store_anchor_block`,
`store_anchor_min_slot`). The one honesty-quantified route,
`ActualResetCheckpointRealization.lean`'s `ResetCheckpointHistoryAt` family,
uses the **legacy** `FFGTransitionCoherence.au_checkpoint_of_known`
(`∀ w ∈ E.honest, …`) and is bypassed here in favour of the accepted bundle.
So the honesty is dead, exactly as it was for
`justifiedRootKnown_of_acceptedGlobalTrajectory`.

## Fills beyond the ratified statements

* `BankedJustificationCertificate.second_pos` (carried over from the previous
  landing): the consumption lemma's timing gate is "same-slot capable"
  (`E.slot_at cfg second ≤ E.slot_at cfg m`) and needs
  `get_current_slot (E.store obs second) ≥ 1`.  Along a real trajectory this is
  the call's own slot advance, so `certifiedBankedJustification_update` takes
  `hcall : E.IsScheduledFCRCallAt cfg ext obs n` and discharges it; the bare structure
  does not encode that provenance, so the field stays.
* `BankedJustificationCertificate.second_epoch_start`: a *record*, not a fill.
  Rule delta 5 banks only at an epoch start, so the sole constructor
  `bankedJustificationCertificate_of_gate` already has it as its `hgate.1`;
  the field merely keeps it in the structure, where the observed-reset arm of
  `WeakSelectedStrictEdgeFilterSupply.lean` needs it to place the banking
  second on its own epoch boundary.
* `certifiedBankedJustification_update` takes the accepted-FFG bundle
  (`B`/`hT`/`hanchor`/`hboundary`) and `hA` in addition to the proposal's
  `hH`/`hstore`/`hinv`: the certified arm must *produce* `supplier_known`,
  `banked_known` and the two economic facts, which is exactly what those
  bundles supply.  No new axiom or assumption class is introduced — they are
  the same bundles `Weak.weakFcrStep_observed_known` already needed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Free bonus: a true certificate has a non-empty span -/

/-- **A true broadcast certificate has a non-empty span.** If
`start_slot > end_slot`, `Finset.Icc start_slot end_slot` is empty, so the
certificate's support is the empty sum `0`, and `0 > budget` is false for any
`budget : ℕ` — contradicting the certificate. (Composed with
`end_slot = get_current_slot store - 1` at `has_head_broadcast_certificate`
and a within-horizon call second, this is what makes the certified head a
pre-boundary block.) -/
theorem has_broadcast_certificate_span_nonempty {store : Store Root}
    {balance_source : BeaconState Root} {block_root : Root} {start_slot end_slot : Slot}
    (hcert : Weak.has_broadcast_certificate cfg ext store balance_source block_root
      start_slot end_slot = true) :
    start_slot ≤ end_slot := by
  by_contra hlt
  have hempty : Finset.Icc start_slot end_slot = (∅ : Finset Slot) :=
    Finset.Icc_eq_empty hlt
  have hsupp0 : Weak.get_broadcast_certificate_support cfg ext store balance_source
      block_root start_slot end_slot = 0 := by
    simp [Weak.get_broadcast_certificate_support, hempty]
  simp [Weak.has_broadcast_certificate, hsupp0] at hcert

/-! ## An unkeyed balance source cannot carry a true certificate -/

/-- **A true broadcast certificate forces its balance source to be keyed.**
An unkeyed checkpoint state is the default `BeaconState`, whose empty
validator registry makes every candidate inactive (`exit_epoch = 0`, so
`is_active_validator` is false for every epoch), hence the certificate's
support is the empty sum `0` — contradicting a true certificate exactly as
`Execution.checkpoint_state_key_of_one_confirmed` contradicts a true
`is_one_confirmed` call (`CheckpointDomain.lean`). -/
theorem checkpoint_state_key_of_broadcast_certificate (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (c : Checkpoint Root) (block_root : Root)
    (start_slot end_slot : Slot)
    (hcert : Weak.has_broadcast_certificate cfg ext (E.store cfg ext v n)
      ((E.store cfg ext v n).checkpoint_states c) block_root start_slot end_slot = true) :
    c ∈ (E.store cfg ext v n).checkpoint_state_keys := by
  by_contra hc
  have hz : (E.store cfg ext v n).checkpoint_states c = (default : BeaconState Root) :=
    E.checkpointStatesExact cfg ext hgen v n c hc
  rw [hz] at hcert
  have hnoactive : ∀ i : ValidatorIndex,
      is_active_validator ((default : BeaconState Root).validators.getD i default)
        (get_current_epoch cfg (default : BeaconState Root)) = false := by
    intro i
    change is_active_validator (default : Validator)
      (get_current_epoch cfg (default : BeaconState Root)) = false
    simp only [is_active_validator, decide_eq_false_iff_not]
    rintro ⟨-, hlt⟩
    exact absurd hlt (Nat.not_lt_zero _)
  have hsupp0 : Weak.get_broadcast_certificate_support cfg ext (E.store cfg ext v n)
      (default : BeaconState Root) block_root start_slot end_slot = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exfalso
    simp only [Finset.mem_filter, Bool.and_eq_true] at hi
    rw [hnoactive i] at hi
    exact absurd hi.1.2.2 (by decide)
  simp [Weak.has_broadcast_certificate, hsupp0] at hcert

/-! ## Observer-side accepted checkpoint geometry

Everything in this section is a *copy with the honesty binder dropped* of the
accepted-FFG machinery, exactly as
`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`
(`WeakOneShotSafety.lean`) was: every step is proved for an arbitrary node,
but the strong statements still take `_hw : w ∈ E.honest` as a required
explicit argument, which a possibly-Byzantine `obs` cannot supply. -/

/-- Unrealized-justified twin of
`AcceptedFFGGlobalCheckpointOrigins.justified_anchor_or_AUEvidence`
(`AcceptedFFGGlobalCheckpointTrajectory.lean` exports the justified and
finalized accessors only; the `unrealized_justified` field has the same
`anchor ∨ GU carrier` shape). -/
private theorem unrealizedJustified_anchor_or_AUEvidence {E : Execution Root}
    {anchor : Checkpoint Root} {S : AcceptedChainFFGState cfg ext E anchor}
    {store : Store Root} (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    store.unrealized_justified_checkpoint = anchor ∨
      AcceptedSelectorAUEvidence S store store.unrealized_justified_checkpoint := by
  rcases h.unrealized_justified with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hgu]
    exact S.gu_AU cfg ext hr.acceptedRoot

/-- **The boundary walk of an accepted AU tip, at a possibly-Byzantine
observer.** The tip's chain is known all the way down to the first slot of the
checkpoint's epoch: the trusted anchor is a known block at or below that
boundary (`TrustedAnchorBoundaryAligned` plus `anchor.epoch ≤ c.epoch`, which
the accepted formation evidence certifies), and `store_walkKnownK` walks any
known root down to any known block's slot. This is the step every consumer of
`AcceptedSelectorAUCarrier.checkpointRoot_known` has to supply; factored out
here so the knownness and the ancestry consumers share it. -/
private theorem auTip_walkKnown
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [Execution.TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  obtain ⟨carr, _hdesc, hformed⟩ := hAU
  obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
  have hcertified : CertifiedJustified cfg E B.anchor c :=
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
        B.state.includedAttestations) hincluded
  have hanchorEpochLe : B.anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
  have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
      compute_start_slot_at_epoch cfg c.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks B.anchor.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
      B.anchor.root hanchorMem tip htip
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary'.trans hstartLe

/-- **Accepted-origin checkpoint roots are known in the observer's own
store.** The observer-side restatement of the knownness half of
`AcceptedCurrentTargetLowerContracts.justifiedRootKnown_of_acceptedGlobalTrajectory`,
generalized from the store's justified checkpoint to *any* checkpoint with an
accepted origin at that store. -/
theorem acceptedOriginRoot_known_at_observer
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {c : Checkpoint Root}
    (horigin : c = B.anchor ∨
      AcceptedSelectorAUEvidence B.state (E.store cfg ext obs n) c) :
    c.root ∈ (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  rcases horigin with hcAnchor | hevidence
  · rw [hcAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots
      (Weak.auTip_walkKnown cfg ext B hT hanchor hboundary obs n
        carrier.tip_carrier.known carrier.au)

/-- **The observer's own unrealized-justified root is known in its own
store.** `acceptedOriginRoot_known_at_observer` at the store-global
unrealized-justified field, whose accepted origin is
`unrealizedJustified_anchor_or_AUEvidence`. -/
theorem unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).unrealized_justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  exact Weak.acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (unrealizedJustified_anchor_or_AUEvidence cfg ext
      ((B.causalStoreGlobalProjection ⟨ast, ablk, hgenEq, hslot⟩ hanchor
        (E.store_causal cfg ext obs n)).storeGlobal))

/-- **The observer's own justified root is known in its own store.**
`acceptedOriginRoot_known_at_observer` at the store-global justified field. -/
theorem justifiedRoot_known_at_observer
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  exact Weak.acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (B.globalJustified_anchor_or_AUEvidence ⟨ast, ablk, hgenEq, hslot⟩ hanchor
      (E.store_causal cfg ext obs n))

/-- **The observer's own fork-choice head is a known block.** `get_head`'s
GHOST descent either lands on a block of the filtered tree or degenerates to
the justified root; both are known in the observer's own store, the latter by
`justifiedRoot_known_at_observer`. This is `supplier_known` for the revised
rule delta 5. -/
theorem head_known_at_observer
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (get_head cfg (E.store cfg ext obs n)).root ∈ (E.store cfg ext obs n).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext obs n) with hmem | heq
  · exact hmem
  · rw [heq]
    exact Weak.justifiedRoot_known_at_observer cfg ext B hT hanchor hboundary obs n

/-! ### The chain-intrinsic ancestry of an accepted AU checkpoint -/

/-- **An accepted AU checkpoint sits on its tip's own chain.** The accepted
bundle's `au_checkpoint_of_known` (causal-store quantified, honesty-free)
identifies the checkpoint's root with `get_checkpoint_block store tip c.epoch`,
i.e. with the block the store's own ancestor walk from `tip` lands on at the
first slot of `c.epoch`. Knownness is then `get_ancestor_spec` (this is
`AcceptedSelectorAUCarrier.checkpointRoot_known`), and ancestry is the walk
composition that knownness proof derives and discards: walking from `tip` down
to the landed block's own slot lands on that block, which is precisely
`is_ancestor`.

This is the lemma that makes the revised rule delta 5 work — with the banked
value read out of the head's own `unrealized_justifications` entry, coverage of
the banked root by the head certificate is a consequence of the FFG contracts,
not an extra hypothesis. -/
theorem auCheckpoint_known_and_below_tip
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    c.root ∈ (E.store cfg ext obs n).block_roots ∧
      is_ancestor (E.store cfg ext obs n) (get_node_for_root tip)
        (get_node_for_root c.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  have hwalk : WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip :=
    Weak.auTip_walkKnown cfg ext B hT hanchor hboundary obs n htip hAU
  have hcheckpoint := B.coherence.au_checkpoint_of_known hstore tip htip c hAU
  have hroot : c.root = (get_ancestor (E.store cfg ext obs n)
      (ForkChoiceNode.mk tip .pending) (compute_start_slot_at_epoch cfg c.epoch)).root := by
    have hr := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block, get_checkpoint_block] using hr
  obtain ⟨hknown, hslotLe⟩ := get_ancestor_spec hparentSlots hwalk
  have hcKnown : c.root ∈ (E.store cfg ext obs n).block_roots := by
    rw [hroot]; exact hknown
  have hcSlot : ((E.store cfg ext obs n).blocks c.root).slot ≤
      compute_start_slot_at_epoch cfg c.epoch := by
    rw [hroot]; exact hslotLe
  have hback : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks c.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n c.root hcKnown tip htip
  have hcomp := get_ancestor_comp_root hparentSlots hcSlot hback
  rw [← hroot, get_ancestor_stop (le_refl _)] at hcomp
  refine ⟨hcKnown, ?_⟩
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
  exact hcomp.symm

/-- A known block's own unrealized justification is known and lies on its
ancestry. This applies to the selected certified carrier as well as the actual
fork-choice head. No observer-honesty assumption is used. -/
theorem blockUnrealizedJustification_known_and_below
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) (supplier : Root)
    (hhead : supplier ∈ (E.store cfg ext obs n).block_roots) :
    ((E.store cfg ext obs n).unrealized_justifications
        supplier).root ∈
      (E.store cfg ext obs n).block_roots ∧
      is_ancestor (E.store cfg ext obs n)
        (get_node_for_root supplier)
        (get_node_for_root ((E.store cfg ext obs n).unrealized_justifications
          supplier).root) = true := by
  have hgu : (E.store cfg ext obs n).unrealized_justifications
      supplier =
      B.state.GU supplier :=
    E.accepted_unrealized_justification_eq
      B.coherence.toAcceptedFFGSelectorCoherence obs n hhead
  have hAU : B.state.AU cfg ext supplier
      ((E.store cfg ext obs n).unrealized_justifications
        supplier) := by
    rw [hgu]
    exact B.state.gu_AU cfg ext
      (E.acceptedRoot_of_causal_known cfg ext (E.store_causal cfg ext obs n) hhead)
  exact Weak.auCheckpoint_known_and_below_tip cfg ext B hT hanchor hboundary obs n
    hhead hAU

/-! ### The fork-choice reduction, retained

No longer on rule delta 5's path (the revised rule's coverage is intrinsic to
the head's own `unrealized_justifications` entry), but a true and reusable
fork-choice fact at a possibly-Byzantine observer: anything on the store's
*justified* root's chain is on the head's chain. -/

/-- **`get_head` descends from the store's justified root.** `get_head` starts
its GHOST descent at `store.justified_checkpoint.root` and only ever steps into
the filtered block tree rooted there, so any block on the justified root's
chain is on the head's chain (`E5Filter.head_ge_of_justified_ge_K`). All three
of that lemma's domain conditions are node-generic and hold at the (possibly
Byzantine) observer: `store_parentSlotLt`, `store_walkKnownK`, and
`justifiedRoot_known_at_observer` above. -/
theorem bankedBelowHead_of_bankedBelowJustified
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {b : Root}
    (hb : b ∈ (E.store cfg ext obs n).block_roots)
    (hjb : is_ancestor (E.store cfg ext obs n)
      (get_node_for_root (E.store cfg ext obs n).justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext obs n)
      (get_head cfg (E.store cfg ext obs n)) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  exact head_ge_of_justified_ge_K cfg
    (E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n)
    (E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n)
    (Weak.justifiedRoot_known_at_observer cfg ext B hT hanchor hboundary obs n)
    hb hjb

/-! ## The input invariant -/

/-- Certificate evidence for the banked observed justified checkpoint (rule
delta 5's input invariant, certified arm). Exactly the package
`Execution.certificate_dissemination` consumes, plus the **raw banking
equation** that lets the banked root's own dissemination be established from
the supplier's. Field names mirror `Execution.AcceptedUJCacheInstallationAt`
(`second`/`second_le` for `originSecond`/`origin_le`) so the weak Lemma-22
history can consume both uniformly.

**The ancestry is not a field.** An earlier form of this structure carried
`banked_below_supplier : is_ancestor store supplier banked`, which the
store-global banking made false in general (module docstring). The revised
rule banks `store.unrealized_justifications supplier`, so the structure
carries that equation (`banked_eq`) instead — an executable identity,
discharged by `rfl`-shaped rewriting at construction — and the ancestry is
*derived* at consumption from the accepted FFG contracts
(`Weak.blockUnrealizedJustification_known_and_below`).

**Fill beyond the ratified statement**: `second_pos`. The consumption lemma's
timing gate is stated as `E.slot_at cfg second ≤ E.slot_at cfg m`
("same-slot capable") and needs
`get_current_slot (E.store obs second) - 1 + 1 = get_current_slot (E.store obs
second)`, which needs `get_current_slot (E.store obs second) ≥ 1` — false in
general for `ℕ` truncated subtraction when the store's current slot is `0`.
Every certificate actually produced by a real trajectory has this for free
(`certifiedBankedJustification_update` reads it off the call's slot advance),
but the bare structure does not encode that provenance, so it is recorded as
an explicit field. -/
structure BankedJustificationCertificate (E : Execution Root)
    (obs : ValidatorIndex) (n : ℕ) (fcr_store : FastConfirmationStore Root) where
  /-- the second whose gated epoch-start rotation banked the value -/
  second : ℕ
  second_le : second ≤ n
  second_within : E.WithinHorizon cfg second
  /-- fill (see docstring): the store's clock has advanced past slot `0` at
  `second`, needed for the consumption lemma's same-slot-capable timing. -/
  second_pos : 1 ≤ get_current_slot cfg (E.store cfg ext obs second)
  /-- the banking second is an epoch start.  This is free at construction —
  the only constructor is `Weak.bankedJustificationCertificate_of_gate`, whose
  gate hypothesis *is* this conjunct — and it is what lets a consumer read the
  banked value's own epoch boundary off the certificate's second. -/
  second_epoch_start :
    is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs second)) = true
  /-- The known certified block whose own justification was banked. -/
  supplier : Root
  supplier_known : supplier ∈ (E.store cfg ext obs second).block_roots
  /-- the banked root is a known block of the observer's own store -/
  banked_known :
    fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext obs second).block_roots
  /-- **the revised banking equation**: what was banked is the supplier's own
  unrealized justification, the justification observed *through* the certified
  block.  Ancestry of the banked root below the supplier is a consequence
  (`Weak.blockUnrealizedJustification_known_and_below`), not an assumption. -/
  banked_eq :
    fcr_store.current_epoch_observed_justified_checkpoint =
      (E.store cfg ext obs second).unrealized_justifications supplier
  /-- the balance source the gate was evaluated against, with the two economic
  facts `certificate_dissemination` requires (produced, not assumed: the gate
  being true forces its key to be keyed, then `registryConstant` /
  `checkpoint_states_total_active_balance` apply) -/
  balance_source : BeaconState Root
  balance_registry : balance_source.validators = E.registry
  balance_total :
    get_total_active_balance cfg balance_source = E.total_active cfg
  /-- the gate itself, verbatim -/
  certificate :
    has_broadcast_certificate cfg ext (E.store cfg ext obs second)
      balance_source supplier
      (get_block_slot (E.store cfg ext obs second) supplier)
      (get_current_slot cfg (E.store cfg ext obs second) - 1) = true
  /-- the span side conditions, discharged once here rather than at each use -/
  start_anchor :
    E.slot_at cfg 0 ≤ get_block_slot (E.store cfg ext obs second) supplier
  start_within : E.SlotWithinHorizon cfg
    (get_block_slot (E.store cfg ext obs second) supplier)
  end_within : E.SlotWithinHorizon cfg
    (get_current_slot cfg (E.store cfg ext obs second) - 1)

/-- Re-indexing a certificate: the structure constrains `fcr_store` only
through its banked checkpoint, and `second ≤ n` only from above, so a witness
transports verbatim along any later second and any store banking the same
value. This is what the "not an epoch start / gate false" cases of the
maintenance lemma use. -/
def BankedJustificationCertificate.transport {E : Execution Root}
    {obs : ValidatorIndex} {n m : ℕ} {fcr_store fcr_store' : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store) (hnm : n ≤ m)
    (heq : fcr_store'.current_epoch_observed_justified_checkpoint =
      fcr_store.current_epoch_observed_justified_checkpoint) :
    Weak.BankedJustificationCertificate cfg ext E obs m fcr_store' where
  second := h.second
  second_le := h.second_le.trans hnm
  second_within := h.second_within
  second_pos := h.second_pos
  second_epoch_start := h.second_epoch_start
  supplier := h.supplier
  supplier_known := h.supplier_known
  banked_known := by rw [heq]; exact h.banked_known
  banked_eq := heq.trans h.banked_eq
  balance_source := h.balance_source
  balance_registry := h.balance_registry
  balance_total := h.balance_total
  certificate := h.certificate
  start_anchor := h.start_anchor
  start_within := h.start_within
  end_within := h.end_within

/-- **The one-shot input invariant.** `fcr_store`'s banked observed justified
checkpoint is either the trusted anchor/initialisation value — globally
known, hence disseminated for free by `Execution.store_storeLE` — or it was
installed by a gate-passing rotation whose supplier carries a broadcast
certificate. Two arms, mirroring `AcceptedUJCacheInstallationAt.
accepted_origin`. -/
def CertifiedBankedJustification (E : Execution Root) (obs : ValidatorIndex)
    (n : ℕ) (fcr_store : FastConfirmationStore Root) : Prop :=
  fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      E.genesis_store.block_roots ∨
    Nonempty (BankedJustificationCertificate cfg ext E obs n fcr_store)

/-- `BankedJustificationCertificate.transport`, lifted to the invariant. -/
theorem CertifiedBankedJustification.transport {E : Execution Root}
    {obs : ValidatorIndex} {n m : ℕ} {fcr_store fcr_store' : FastConfirmationStore Root}
    (h : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store) (hnm : n ≤ m)
    (heq : fcr_store'.current_epoch_observed_justified_checkpoint =
      fcr_store.current_epoch_observed_justified_checkpoint) :
    Weak.CertifiedBankedJustification cfg ext E obs m fcr_store' := by
  rcases h with hanchor | hne
  · exact Or.inl (by rw [heq]; exact hanchor)
  · obtain ⟨hc⟩ := hne
    exact Or.inr ⟨hc.transport cfg ext hnm heq⟩

/-! ## Consumption -/

/-- **The consumption lemma, certified arm**: the banked twin of
`Execution.confirmed_known_at_all_honest_endpoints_at_observer`. The supplier
disseminates directly (`Execution.certificate_dissemination`, obligation 2,
applied to the certificate that names the supplier directly); the banked root then transports along the
*chain-intrinsic* ancestry — `banked_eq` plus
`Weak.blockUnrealizedJustification_known_and_below` — via
`Execution.is_ancestor_transport_closed`, using the supplier's freshly
established endpoint membership as the doubly-known witness. No second trip
through an honest supporter's store, and no `WalkKnown` side hypotheses, are
needed (unlike `Weak.certificate_chain_dissemination`, whose extra `WalkKnown`
premises are not derivable from the certificate's own fields, whereas
`is_ancestor_transport_closed`'s anchor-min-slot premise is). The `hgate`
timing arithmetic is "same-slot capable" (`E.slot_at cfg second ≤ E.slot_at
cfg m`, equality not required) via `second_pos` and
`has_broadcast_certificate_span_nonempty`. -/
theorem bankedSupplier_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    h.supplier ∈ (E.store cfg ext w m).block_roots ∧
      fcr_store.current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  -- Unfold the gate to a plain certificate on the supplier.
  have hcert' : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs h.second)
      h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1) = true := by
    have hc := h.certificate
    -- The certificate names the supplier directly.
    exact hc
  -- Same-slot-capable timing: end_slot + 1 = current_slot = E.slot_at second ≤ E.slot_at m.
  have hend1 : get_current_slot cfg (E.store cfg ext obs h.second) - 1 + 1 =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    Nat.sub_add_cancel h.second_pos
  have hslotEq : E.slot_at cfg h.second =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    (E.store_current_slot cfg ext obs h.second).symm
  have htiming : (get_current_slot cfg (E.store cfg ext obs h.second) - 1) + 1 ≤
      E.slot_at cfg m := by
    rw [hend1, ← hslotEq]; exact hgate
  have hsupplier : h.supplier ∈ (E.store cfg ext w m).block_roots :=
    E.certificate_dissemination cfg ext hA.wellFormed hA.honest_behavior hsync
      hA.externals_coherence hA.byzantine_bound hji ⟨ast, ablk, hgeq, hslot, hparent⟩
      obs h.second h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1)
      h.second_within h.start_within h.end_within h.start_anchor
      h.balance_registry h.balance_total (hcomm h.second h.second_within)
      h.supplier_known hcert' w hw m hmH htiming
  -- The chain-intrinsic ancestry: the banked value *is* the supplier's own
  -- unrealized justification, which the accepted contracts place on the
  -- supplier's chain.
  obtain ⟨hbankedKnown, hbelow⟩ :=
    Weak.blockUnrealizedJustification_known_and_below cfg ext B hT hanchor hboundary
      obs h.second h.supplier h.supplier_known
  rw [← h.banked_eq] at hbankedKnown hbelow
  have hanchorBanked : ablk.message.slot ≤
      ((E.store cfg ext obs h.second).blocks
        fcr_store.current_epoch_observed_justified_checkpoint.root).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence hgeq hslot hparent
      obs h.second fcr_store.current_epoch_observed_justified_checkpoint.root hbankedKnown
  have hbanked : fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence hgeq hslot
      hparent hanchorBanked h.supplier_known hsupplier hbankedKnown hbelow
  exact ⟨hsupplier, hbanked⟩

/-- **The consumption lemma, both arms**: the banked root is known at every
honest endpoint past the gate whether it is the trusted anchor or a certified
installation — no scoping and no side condition on the anchor arm. The anchor
arm needs only `Execution.store_storeLE` from genesis; the certified arm
routes through `bankedSupplier_known_at_all_honest_endpoints_at_observer`
above (there is no supplier in the anchor arm, so only the banked-root
conjunct is stated here, universally over whichever certificate witnesses the
invariant's second disjunct). -/
theorem bankedRoot_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : ∀ h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store,
      E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  rcases hinv with hanchorArm | hne
  · exact (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorArm
  · obtain ⟨h⟩ := hne
    exact (Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync hji hgen hcomm h hw hmH (hgate h)).2

/-! ## Exact rotation of the two weak FCR checkpoint fields -/

/-- Weak twin of `update_fcv_observed_exact` (`ActualResetCheckpointRealization
.lean`): exact source selected for the observed checkpoint under the revised
rule delta 5 — the certified supplier's own unrealized justification when the
certificate gate fires at an epoch start and its checkpoint epoch is strictly
newer than the observed checkpoint epoch; the carried value otherwise. Note that the
ordered write through `previous_epoch_greatest_unrealized_checkpoint` has
disappeared: the revised rule does not read that field. -/
theorem update_fcv_observed_exact (fcr_store : FastConfirmationStore Root) :
    (Weak.update_fast_confirmation_variables cfg ext
        fcr_store).current_epoch_observed_justified_checkpoint =
      if (is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
          has_head_broadcast_certificate cfg ext fcr_store.store
            (get_current_balance_source fcr_store) = true) ∧
          (fcr_store.store.unrealized_justifications
            (Weak.get_certified_head cfg ext fcr_store.store
              (get_current_balance_source fcr_store))).epoch >
            fcr_store.current_epoch_observed_justified_checkpoint.epoch then
        fcr_store.store.unrealized_justifications (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store))
      else fcr_store.current_epoch_observed_justified_checkpoint := by
  simp only [Weak.update_fast_confirmation_variables]
  split_ifs <;> simp_all

/-- Weak twin of `Execution.fcr_previousGreatest_succ_exact`: the carried
greatest-unrealized field is refreshed at a real slot advance exactly when the
*next* slot starts an epoch. Retained for field-for-field parity with the
strong rule — the revised rule delta 5 no longer consumes this field. -/
theorem weakFcr_previousGreatest_succ_exact {E : Execution Root}
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.weakFcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.weakFcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  simp only [Execution.weakFcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (Weak.on_fast_confirmation cfg ext
      { E.weakFcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  simp only [Weak.on_fast_confirmation, Weak.update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- **Exact provenance of the weak carried greatest-unrealized field.** It is
always some earlier second's store-global unrealized-justified checkpoint — the
weak counterpart of `Execution.AcceptedUJCacheInstallationAt.field_eq`. Retained
for parity; the revised rule delta 5 does not read this field. -/
theorem weakFcr_previousGreatest_origin {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) :
    ∀ n : ℕ, ∃ k ≤ n,
      (E.weakFcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint =
        (E.store cfg ext v k).unrealized_justified_checkpoint := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      obtain ⟨ast, ablk, hgenEq⟩ := hgen
      change E.genesis_store.finalized_checkpoint =
        E.genesis_store.unrealized_justified_checkpoint
      rw [hgenEq]
      simp only [get_forkchoice_store]
  | succ n ih =>
      obtain ⟨k, hk, hfield⟩ := ih
      by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · rw [Weak.weakFcr_previousGreatest_succ_exact cfg ext v n hadv]
        by_cases hrot : is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = true
        · rw [if_pos hrot]
          exact ⟨n + 1, Nat.le_refl _, rfl⟩
        · rw [if_neg hrot]
          exact ⟨k, hk.trans (Nat.le_succ n), hfield⟩
      · refine ⟨k, hk.trans (Nat.le_succ n), ?_⟩
        have hstep : (E.weakFcr cfg ext v (n + 1)
            ).previous_epoch_greatest_unrealized_checkpoint =
            (E.weakFcr cfg ext v n
              ).previous_epoch_greatest_unrealized_checkpoint := by
          simp only [Execution.weakFcr, if_neg hadv]
        exact hstep.trans hfield

/-- The weak carried greatest-unrealized root is a known block in the
observer's own store at every later second. Retained for parity. -/
theorem weakFcr_previousGreatest_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) {n m : ℕ} (hnm : n ≤ m) :
    ((E.weakFcr cfg ext obs n
        ).previous_epoch_greatest_unrealized_checkpoint).root ∈
      (E.store cfg ext obs m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  obtain ⟨k, hk, hfield⟩ :=
    Weak.weakFcr_previousGreatest_origin cfg ext ⟨ast, ablk, hgenEq⟩ obs n
  rw [hfield]
  exact (E.store_storeLE cfg ext obs (hk.trans hnm)).1
    (Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary obs k)

/-! ### `banked_known`, discharged -/

/-- **`banked_known`, discharged for the whole weak trajectory.** Whatever the
revised rule delta 5 has banked in `current_epoch_observed_justified_checkpoint`
at any second is a known block in the observer's own store at that second — the
initialisation value is the trusted anchor, and every later value is either
carried (`store_storeLE`) or a gate-passing installation of the head's own
unrealized justification, which
`blockUnrealizedJustification_known_and_below` covers. Proved outright, with no
honesty hypothesis anywhere. -/
theorem weakFcr_observed_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ,
      ((E.weakFcr cfg ext obs n
          ).current_epoch_observed_justified_checkpoint).root ∈
        (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  intro n
  induction n with
  | zero =>
      change E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots
      rw [hgenEq]
      simp only [get_forkchoice_store, List.mem_singleton]
  | succ n ih =>
      by_cases hadv : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (Weak.update_fast_confirmation_variables cfg ext
              { E.weakFcr cfg ext obs n with
                store := E.store cfg ext obs (n + 1) }
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_pos hadv, Weak.on_fast_confirmation]
        rw [hstep, Weak.update_fcv_observed_exact]
        split_ifs
        · exact (Weak.blockUnrealizedJustification_known_and_below cfg ext B hT
            hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
        · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (E.weakFcr cfg ext obs n
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_neg hadv]
        rw [hstep]
        exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih

/-- `banked_known` at the speculative query store `E.weakFcrStep`, the shape
the maintenance lemma needs at `second := n + 1`. -/
theorem weakFcrStep_observed_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    ((E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint).root ∈
      (E.store cfg ext obs (n + 1)).block_roots := by
  rw [Execution.weakFcrStep, Weak.update_fcv_observed_exact]
  split_ifs
  · exact (Weak.blockUnrealizedJustification_known_and_below cfg ext B hT
      hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
  · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
      (Weak.weakFcr_observed_known cfg ext B hT hanchor hboundary obs n)

/-! ## Maintenance along the actual-call trajectory -/

/-- **Supplier evidence from a gate-passing epoch-start call.**

The certificate is indexed by a record containing the supplier's checkpoint.
This record supports supplier dissemination even when the strict-newer guard
retains the actual observed checkpoint. When the guard permits the write,
`certifiedBankedJustification_update` transports the certificate to the actual
output record.

Its `second` is the call's own boundary second `n + 1` and its `supplier` is
that second's selected certified carrier. Both projections remain `rfl`.
The checkpoint equation follows from the record's explicit field value;
`supplier_known` and `banked_known` follow from the accepted facts above.
The certificate supplies the checkpoint-state key, from which
`registryConstant` and `checkpoint_states_total_active_balance` give the two
economic facts. -/
noncomputable def bankedJustificationCertificate_of_gate
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_head_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    Weak.BankedJustificationCertificate cfg ext E obs (n + 1)
      { Weak.update_fast_confirmation_variables cfg ext fcr_store with
        current_epoch_observed_justified_checkpoint :=
          fcr_store.store.unrealized_justifications
            (Weak.get_certified_head cfg ext fcr_store.store
              (get_current_balance_source fcr_store)) } := by
  -- `hA.genesis` is an `Exists`, so it may only be destructed *inside* the
  -- `Prop`-valued fields: a `Classical.choice` at the head of this
  -- `Type`-valued definition would block the two `rfl` projections below.
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hA.genesis
    exact ⟨ast, ablk, hgeq⟩
  have hbanked :
      ({ Weak.update_fast_confirmation_variables cfg ext fcr_store with
        current_epoch_observed_justified_checkpoint :=
          fcr_store.store.unrealized_justifications
            (Weak.get_certified_head cfg ext fcr_store.store
              (get_current_balance_source fcr_store)) } :
        FastConfirmationStore Root).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext obs (n + 1)).unrealized_justifications
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := by
    change fcr_store.store.unrealized_justifications _ = _
    rw [hstore]
  have hheadKnown : (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    Weak.get_certified_head_known cfg ext _ _
      (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1))
  have hcertStore : Weak.has_head_broadcast_certificate cfg ext
      (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store) = true := by
    rw [← hstore]; exact hgate.2
  have hcertPlain : Weak.has_broadcast_certificate cfg ext
      (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      (get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)))
      (get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1) = true := by
    simpa only [Weak.has_head_broadcast_certificate] using hcertStore
  have hbseq : get_current_balance_source fcr_store =
      (E.store cfg ext obs (n + 1)).checkpoint_states
        fcr_store.current_epoch_observed_justified_checkpoint := by
    simp only [get_current_balance_source]
    rw [hstore]
  have hkey : fcr_store.current_epoch_observed_justified_checkpoint ∈
      (E.store cfg ext obs (n + 1)).checkpoint_state_keys := by
    refine Weak.checkpoint_state_key_of_broadcast_certificate cfg ext E hgen0 obs (n + 1)
      _ (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      (get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)))
      (get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1) ?_
    rw [← hbseq]
    exact hcertPlain
  -- Slot arithmetic for the span side conditions.
  have hpos : 1 ≤ get_current_slot cfg (E.store cfg ext obs (n + 1)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hcall
  have hslotNow : get_current_slot cfg (E.store cfg ext obs (n + 1)) =
      E.slot_at cfg (n + 1) := E.store_current_slot cfg ext obs (n + 1)
  have hspan : get_block_slot (E.store cfg ext obs (n + 1))
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ≤
      get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1 :=
    Weak.has_broadcast_certificate_span_nonempty cfg ext hcertPlain
  have hendLe : get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1 ≤
      E.slot_at cfg (n + 1) := by
    rw [← hslotNow]; exact Nat.sub_le _ _
  have hstartAnchor : E.slot_at cfg 0 ≤
      get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := by
    obtain ⟨ast, ablk, hgeq, hslotEq, hparentNe⟩ := hA.genesis
    have hanchorHead : ablk.message.slot ≤
        ((E.store cfg ext obs (n + 1)).blocks
          (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))).slot :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence hgeq hslotEq
        hparentNe obs (n + 1) _ hheadKnown
    have hslot0 : E.slot_at cfg 0 = ablk.message.slot := by
      have ht := E.store_current_slot cfg ext obs 0
      rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
        get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
      rw [← ht, hslotEq]
    rw [hslot0]
    exact hanchorHead
  exact
    { second := n + 1
      second_le := Nat.le_refl _
      second_within := hH
      second_pos := hpos
      second_epoch_start := by rw [← hstore]; exact hgate.1
      supplier := (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      supplier_known := hheadKnown
      banked_known := by
        rw [hbanked]
        exact (Weak.blockUnrealizedJustification_known_and_below cfg ext B hT
          hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
      banked_eq := hbanked
      balance_source := get_current_balance_source fcr_store
      balance_registry := by
        rw [hbseq]
        exact (E.registryConstant cfg ext hA.externals_coherence hgen0
          obs (n + 1)).2 _ hkey
      balance_total := by
        rw [hbseq]
        exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
          hA.externals_coherence (hdiv := hA.whole_seconds) (hgen := hgen0)
          obs (n + 1) _ hkey hH
      certificate := hcertPlain
      start_anchor := hstartAnchor
      start_within :=
        E.slotWithinHorizon_of_le cfg (hspan.trans hendLe) hH
      end_within := E.slotWithinHorizon_of_le cfg hendLe hH }

/-- The gate certificate's second is the call's own boundary second. -/
theorem bankedJustificationCertificate_of_gate_second
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_head_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    (Weak.bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
      hboundary hH hcall hstore hgate).second = n + 1 := rfl

/-- The gate certificate's supplier is that second's selected certified carrier. -/
theorem bankedJustificationCertificate_of_gate_supplier
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_head_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    (Weak.bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
        hboundary hH hcall hstore hgate).supplier =
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := rfl

/-- **The certified carrier of a gate-passing epoch-start call is disseminated.**

The banked twin of `Execution.confirmed_known_at_all_honest_endpoints_at_observer`
applied to the *supplier* half of
`bankedSupplier_known_at_all_honest_endpoints_at_observer`, using this call's
supplier certificate. The strict-newer guard need not permit a checkpoint
write for this certificate to establish dissemination. This is the epoch-start
replacement for stage S3's
`Weak.headSeed_known_at_all_honest_endpoints_at_observer`: at an epoch start
the tentative-entry gate takes the uncertified escape, so no *entry* head
certificate is available, but rule delta 5's own banking gate carries one
whenever it fires. -/
theorem gatedHead_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_head_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m) :
    (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ∈
      (E.store cfg ext w m).block_roots := by
  have hknown :=
    (Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync hji hA.genesis hcomm
      (Weak.bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
        hboundary hH hcall hstore hgate)
      hw hmH (by
        rw [Weak.bankedJustificationCertificate_of_gate_second]
        exact hslot)).1
  rwa [Weak.bankedJustificationCertificate_of_gate_supplier] at hknown

/-- **Rule delta 5 preserves its own input invariant.** At an epoch start,
a passing certificate gate and a strictly newer checkpoint install the
supplier's checkpoint. The exact write equation transports the supplier
certificate to the actual output. In every other case the banked field is
unchanged and the incoming witness re-indexes through
`BankedJustificationCertificate.transport`.

No ancestry obligation arises here: under the revised rule it is a theorem
about the banked value (`blockUnrealizedJustification_known_and_below`),
deferred to consumption. -/
theorem certifiedBankedJustification_update
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store) :
    Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (Weak.update_fast_confirmation_variables cfg ext fcr_store) := by
  by_cases hgate :
      (is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
        Weak.has_head_broadcast_certificate cfg ext fcr_store.store
          (get_current_balance_source fcr_store) = true) ∧
        (fcr_store.store.unrealized_justifications
          (Weak.get_certified_head cfg ext fcr_store.store
            (get_current_balance_source fcr_store))).epoch >
          fcr_store.current_epoch_observed_justified_checkpoint.epoch
  · -- The supplier checkpoint passes both the certificate and epoch guards.
    refine Or.inr ⟨(Weak.bankedJustificationCertificate_of_gate cfg ext hA B hT
      hanchor hboundary hH hcall hstore hgate.1).transport cfg ext
        (Nat.le_refl _) ?_⟩
    change (Weak.update_fast_confirmation_variables cfg ext
      fcr_store).current_epoch_observed_justified_checkpoint =
        fcr_store.store.unrealized_justifications
          (Weak.get_certified_head cfg ext fcr_store.store
            (get_current_balance_source fcr_store))
    rw [Weak.update_fcv_observed_exact, if_pos hgate]
  · -- No write: retain the previous checkpoint and its certificate.
    have heq : (Weak.update_fast_confirmation_variables cfg ext
        fcr_store).current_epoch_observed_justified_checkpoint =
        fcr_store.current_epoch_observed_justified_checkpoint := by
      rw [Weak.update_fcv_observed_exact, if_neg hgate]
    exact hinv.transport cfg ext (Nat.le_succ n) heq

/-- **The invariant holds along the whole actual weak trajectory.** Induction
on the second: the seed is the genesis initializer, which banks the anchor
store's `finalized_checkpoint` — in `E.genesis_store.block_roots`, hence the
anchor arm; the step is `certifiedBankedJustification_update` at a real slot
advance, and a pure re-index otherwise. No honesty hypothesis and no call
predicate beyond the slot advance `E.weakFcr` itself branches on. -/
theorem weakFcr_certifiedBankedJustification
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.CertifiedBankedJustification cfg ext E obs n (E.weakFcr cfg ext obs n) := by
  obtain ⟨ast, ablk, hgeq, _hslotEq, _hparentNe⟩ := hA.genesis
  intro n
  induction n with
  | zero =>
      intro _
      left
      change E.genesis_store.finalized_checkpoint.root ∈ E.genesis_store.block_roots
      rw [hgeq]
      simp only [get_forkchoice_store, List.mem_singleton]
  | succ n ih =>
      intro hH
      have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg (Nat.le_succ n) hH
      by_cases hadv : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hseat : Weak.CertifiedBankedJustification cfg ext E obs n
            { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) } :=
          (ih hHn).transport cfg ext (Nat.le_refl n) rfl
        have hupd := Weak.certifiedBankedJustification_update cfg ext hA B hT hanchor
          hboundary (obs := obs) (n := n) hH hadv (fcr_store :=
            { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) })
          rfl hseat
        refine hupd.transport cfg ext (Nat.le_refl (n + 1)) ?_
        simp only [Execution.weakFcr, if_pos hadv, Weak.on_fast_confirmation]
      · refine (ih hHn).transport cfg ext (Nat.le_succ n) ?_
        simp only [Execution.weakFcr, if_neg hadv]

end Weak

end FastConfirmation.Spec

end
