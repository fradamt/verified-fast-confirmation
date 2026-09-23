module
public import FastConfirmationProofs.FFG.SelectedSource.EndpointJustifiedOrientation
public import FastConfirmationProofs.Weak.Certificates.EndpointQuorumCausality
public import FastConfirmationProofs.Weak.Safety.WeakObserverDomain
public import FastConfirmationProofs.Weak.Common.WeakFCRCallContracts
public import FastConfirmationProofs.Weak.Safety.WeakObserverProvenance

@[expose] public section

/-!
# Spec / Proof / WeakHistoricalA32CallSupplier

Observer-side twins of the "completed scheduled event prefix" layer of
`AcceptedHistoricalA32CallSupplier.lean`, run at a possibly-Byzantine
observer `obs` over its own trajectory.

An `Execution.fcr` — and equally a `Execution.weakFcr` — write-back call reads
`E.store obs (n + 1)`, which is exactly the full scheduled prefix for second
`n + 1`.  The prefix itself, and everything the accepted current-target gate
reads off it, is a fact about *the observer's own replayed store*; none of it
is a fact about the observer's behaviour.  That is why this layer ports
mechanically while the write-back induction above it does not (see the
"What is not here" section).

## What is reused verbatim from the strong module

These four declarations are already honesty-free — they quantify over an
arbitrary `v : ValidatorIndex` with no `v ∈ E.honest` premise — so they are
imported and applied unchanged rather than cloned:

* `Execution.completedScheduledEventPrefix` and
  `Execution.completedScheduledEventPrefix_store`
  (`AcceptedHistoricalA32CallSupplier.lean:32`, `:41`);
* `Execution.completedPrefix_anchor_epoch_within` (`:169`);
* `Execution.currentTargetEpochEnd_within_of_epochEndsFitUint64` (`:221`) and
  `Execution.completedPrefix_currentTargetEpochEnd_within` (`:276`).

`Execution.CompletedFCRCallPremises` (`:332`) is
also reused verbatim as the premise bundle of the gate producer below; the
producer reads only its protocol fields, never its honest-quantified
`helper_provisos`.

## The substitutions

Per the wave's stage-S0 audit the query node's honesty binder
`hv : v ∈ E.honest` resolves, in this layer, to exactly two kinds of use, and
both are replaced by a field of `Execution.ObserverCoherence`
(`WeakOneShotSafety.lean:86`):

* (a) committee readback,
  `hT.externals_coherence.committees_agree v hv …`, becomes
  `hcoh.committees_agree …` — used once, in
  `completedScheduledEventPrefix_accountingEvidence_at_observer`;
* (b) head-root knownness,
  `E.headRootKnown_of_acceptedGlobalTrajectory … hv …`, becomes
  `Execution.head_root_known_at_observer` (`WeakObserverDomain.lean:81`) —
  used once each in the two pulled-up-head lemmas.

No third kind occurs anywhere in this module.  The one place where (a) could
not be applied *in situ* is the no-conflict arithmetic branch, which reaches
its `committees_agree` three call levels down inside a strong module; the
section below re-assembles that branch over the strong development's own
committee-explicit twin instead, and explains why that is still substitution
(a) and not a new assumption.

Because (b) removes the *only* consumer of the accepted global semantics in
the two pulled-up-head lemmas, their weak twins drop the `B`, `hanchor` and
`hboundary` premises entirely; `Execution.head_root_known_at_observer` needs
none of them.  This is a strict weakening of the premise surface, so the
twins remain drop-in for every strong call site.

## Indexing

Everything here except the gate producer is a statement about the ordinary
store `E.store cfg ext obs (n + 1)` and the scheduled event prefix, which the
weak model shares with the strong one verbatim — there is no weak twin of
`E.store`, so those four lemmas need no re-indexing at all beyond the node.

The gate producer is the one declaration that names an FCR store.  It is
stated over `E.weakFcrStep cfg ext obs n`.  This costs no proof content:
`Execution.AcceptedCurrentTargetA32GateRealizationProducerAt` mentions its
query only through `query.store`, and `Execution.weakFcrStep_store`
(`WeakFCRCallContracts.lean:68`) rewrites that to `E.store cfg ext obs (n+1)`
exactly as `Execution.fcrStep_store` does on the strong side, so the strong
proof transports under a rewrite of that one lemma.

## What is not here

The historical A3.2 payload producer of
`AcceptedActualSelectedJustifiedOrientation.lean` is deliberately absent; see
the report accompanying this module.  It bottoms out in an honesty use that is
*not* of kinds (a)/(b): it instantiates the honest-quantified write-back
induction `acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes`
at the query node over the *strong* `E.confirmed`.

The endpoint origin/pinning producer *is* here.  Its arithmetic half used to
be the same obstruction — the strong pinning proof reaches
`Execution.noConflict_arithmeticBranch_oneThird`, whose honesty premise feeds
the adversarial-weight bound on the query node's own observed latest messages
— and the section below re-assembles that branch over prefix accounting
evidence instead, which is substitution (a) in disguise.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## The completed scheduled prefix at an observer -/

theorem ScheduledEventPrefix.operationalEvidence_of_observer_validity
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix)
    (hvalid : E.ObserverValidity cfg ext p.node)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1)) :
    E.ScheduledPrefixOperationalEvidence cfg ext (p.store cfg ext)
      (p.previousSecond + 1) :=
  { causal := .scheduledPrefix p
    current_slot := p.current_slot cfg ext
    scheduled_provenance := p.schedLMProv cfg ext E hT
    latest_message_provenance :=
      p.latestMessageProvenance_of_observer_validity cfg ext hT hvalid hn
    parent_slot_lt := p.parentSlotLt cfg ext E hT
    blocks_slot_le_current := p.blocksSlotLeCurrent cfg ext E hT
    honest_not_equivocating :=
      p.honest_not_equivocating_of_observer_validity cfg ext hT hvalid }

/-- All prefix accounting evidence at an observer's own execution boundary is
mechanical: the operational half comes from exact replay of the observer's
schedule (`ScheduledEventPrefix.operationalEvidence` never inspects
`p.node`), while committee readback is the observer's own coherence field
instead of `BeaconExternalsPremises.committees_agree` at an honest node.

Substitution (a).  Mirrors
`Execution.completedScheduledEventPrefix_accountingEvidence`. -/
theorem completedScheduledEventPrefix_accountingEvidence_at_observer
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    (n : ℕ) (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext obs (n + 1)) (n + 1) := by
  let p := E.completedScheduledEventPrefix obs n
  have hpstore : p.store cfg ext = E.store cfg ext obs (n + 1) := by
    simpa only [p] using E.completedScheduledEventPrefix_store cfg ext obs n
  have hp : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1) :=
    { operational := p.operationalEvidence_of_observer_validity cfg ext hT
        hcoh.validity hHn1
      committees := by
        intro slot hslot
        rw [hpstore]
        exact hcoh.committees_agree (n + 1) hHn1 slot hslot }
  rw [hpstore] at hp
  simpa only [p, Execution.completedScheduledEventPrefix] using hp

/-! ## Mechanical gate fields at the observer's completed boundary -/

/-- The pulled-up head state reads the static execution registry.  Registry
constancy (`Execution.registryConstant`) is already proved for an arbitrary
node; the head root's membership in the block map is the only honesty use, and
it is the observer's own coherence field.

Substitution (b), and the reason `B`, `hanchor` and `hboundary` disappear from
the signature.  Mirrors
`Execution.completedPrefix_pulledUpHead_validators`. -/
theorem completedPrefix_pulledUpHead_validators_at_observer
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    (get_pulled_up_head_state cfg ext
      (E.store cfg ext obs n)).validators = E.registry := by
  have hhead := E.head_root_known_at_observer cfg ext hcoh n hHn
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hT.genesis_structure
    exact ⟨ast, ablk, hgeq⟩
  have hregistry :=
    (E.registryConstant cfg ext hT.externals_coherence hgen obs n).1
      (get_head cfg (E.store cfg ext obs n)).root hhead
  simp only [get_pulled_up_head_state]
  split_ifs
  · rw [hT.externals_coherence.process_slots_registry]
    exact hregistry
  · exact hregistry

/-- Pulling the head up makes its state epoch exactly the observer store's
current epoch.  In the no-pull branch this follows from the head-state slot
bound and the negated pull guard; the head-state slot bound
(`Execution.stateSlotsLE`) holds at an arbitrary node, so the only honesty use
is again head-root knownness.

Substitution (b).  Mirrors `Execution.completedPrefix_pulledUpHead_epoch`. -/
theorem completedPrefix_pulledUpHead_epoch_at_observer
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    get_current_epoch cfg (get_pulled_up_head_state cfg ext
        (E.store cfg ext obs n)) =
      get_current_store_epoch cfg (E.store cfg ext obs n) := by
  let store := E.store cfg ext obs n
  let head := (get_head cfg store).root
  have hhead : head ∈ store.block_roots := by
    simpa only [store, head] using
      E.head_root_known_at_observer cfg ext hcoh n hHn
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hstateSlots := E.stateSlotsLE cfg ext hT.whole_seconds
    hT.externals_coherence ⟨ast, ablk, hgen⟩ obs n
  have hheadSlot : (store.block_states head).slot ≤
      get_current_slot cfg store := by
    have h := hstateSlots.1 head (by simpa only [store] using hhead)
    simpa only [store, E.store_current_slot] using h
  simp only [get_pulled_up_head_state]
  change get_current_epoch cfg (if get_current_epoch cfg (store.block_states head) <
      get_current_store_epoch cfg store then
        ext.process_slots (store.block_states head)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg store))
      else store.block_states head) =
        get_current_store_epoch cfg store
  by_cases hpull : get_current_epoch cfg (store.block_states head) <
      get_current_store_epoch cfg store
  · rw [if_pos hpull]
    have hslotLt : (store.block_states head).slot <
        compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg store) := by
      have hnext : compute_epoch_at_slot cfg
            (store.block_states head).slot + 1 ≤
          get_current_store_epoch cfg store := by
        simpa only [get_current_epoch, compute_epoch_at_slot] using
          Nat.succ_le_of_lt hpull
      have hlt := Nat.lt_mul_div_succ
        (store.block_states head).slot cfg.slots_per_epoch_pos
      calc
        (store.block_states head).slot < cfg.slots_per_epoch *
            ((store.block_states head).slot / cfg.slots_per_epoch + 1) := hlt
        _ ≤ cfg.slots_per_epoch * get_current_store_epoch cfg store :=
          Nat.mul_le_mul_left cfg.slots_per_epoch hnext
        _ = compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg store) := by
          simp only [compute_start_slot_at_epoch, Nat.mul_comm]
    change (ext.process_slots (store.block_states head)
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg store))).slot /
          cfg.slots_per_epoch = get_current_store_epoch cfg store
    rw [hT.externals_coherence.process_slots_slot _ _ hslotLt]
    simp only [compute_start_slot_at_epoch]
    exact Nat.mul_div_cancel _ cfg.slots_per_epoch_pos
  · rw [if_neg hpull]
    apply Nat.le_antisymm
    · simpa only [get_current_epoch, get_current_store_epoch,
        compute_epoch_at_slot] using Nat.div_le_div_right hheadSlot
    · exact Nat.le_of_not_gt hpull

/-- The observer's pulled-up head balance source has the ground-truth total
active balance.  Registry equality and the two in-horizon state epochs are
enough; no selected-domain, justification interface, or honesty of `obs` is
involved.  `Execution.completedPrefix_anchor_epoch_within` is reused verbatim
from the strong module — it never mentions a node at all.

Composes the two substitution-(b) lemmas above.  Mirrors
`Execution.completedPrefix_pulledUpHead_totalActive`. -/
theorem completedPrefix_pulledUpHead_totalActive_at_observer
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    get_total_active_balance cfg (get_pulled_up_head_state cfg ext
      (E.store cfg ext obs n)) = E.total_active cfg := by
  let state := get_pulled_up_head_state cfg ext (E.store cfg ext obs n)
  have hval : state.validators = E.registry := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_validators_at_observer cfg ext hT hcoh hHn
  have hstateEpoch : get_current_epoch cfg state < E.verification_horizon := by
    rw [E.completedPrefix_pulledUpHead_epoch_at_observer cfg ext hT hcoh hHn]
    simpa only [get_current_store_epoch, E.store_current_slot,
      compute_epoch_at_slot] using hHn.2.2
  have hanchorEpoch := E.completedPrefix_anchor_epoch_within
    cfg ext hT hsv
  change get_total_active_balance cfg state =
    get_total_active_balance cfg E.anchor_state
  apply get_total_active_balance_congr cfg
  · simpa only [Execution.registry] using hval
  · intro i
    rw [hval]
    simpa only [Execution.registry] using
      hsv.activity_constant i (get_current_epoch cfg state)
        (get_current_epoch cfg E.anchor_state) hstateEpoch hanchorEpoch

/-! ## The observer-call accepted current-target gate producer -/

/-- At one weak boundary call, the observer's completed scheduled prefix
supplies the accepted current-target gate producer.  The producer remains
conditional on the executable Boolean and its matching whole-slot
target-support proviso; neither is assumed by this theorem.

This is the only declaration in the module that names an FCR store, and the
weak indexing is free: the producer reads its query solely through
`query.store`, and `Execution.weakFcrStep_store` normalizes that to
`E.store cfg ext obs (n + 1)` exactly as `Execution.fcrStep_store` does on the
strong side.  `Execution.scheduledEventPrefix_acceptedTargetA32GateRealization_withLookahead`,
which does the real work, is honesty-free in the prefix node.

Mirrors `Execution.completedPrefix_acceptedTargetGateProducerAt`, with
substitutions (a) and (b) entering through the three lemmas above. -/
noncomputable def observerCall_acceptedTargetGateProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (_hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n) := by
  intro hgate hsupport
  let p := E.completedScheduledEventPrefix obs n
  have hpstore : p.store cfg ext = E.store cfg ext obs (n + 1) := by
    simpa only [p] using E.completedScheduledEventPrefix_store cfg ext obs n
  have hevidenceBoundary :=
    E.completedScheduledEventPrefix_accountingEvidence_at_observer
      cfg ext hT hcoh n hHn1
  have hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1) := by
    rw [hpstore]
    change E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext obs (n + 1)) (n + 1)
    exact hevidenceBoundary
  let state := get_pulled_up_head_state cfg ext
    (E.store cfg ext obs (n + 1))
  have hstate : state = get_pulled_up_head_state cfg ext
      (p.store cfg ext) := by
    rw [hpstore]
  have hval : state.validators = E.registry := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_validators_at_observer cfg ext hT hcoh hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
        hC.static_validators hcoh hHn1
  have hgateBoundary : will_current_target_be_justified cfg ext
      (E.store cfg ext obs (n + 1)) = true := by
    simpa only [E.weakFcrStep_store] using hgate
  have hsupportBoundary : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext obs (n + 1))) (n + 1) := by
    simpa only [E.weakFcrStep_store] using hsupport
  have hendH := E.currentTargetEpochEnd_within_of_epochEndsFitUint64
    cfg ext hfit (v := obs) (q := n + 1) hHn1
  have hanchorH := E.completedPrefix_anchor_epoch_within cfg ext hT
    hC.static_validators
  have hendHP : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)) := by
    rw [hpstore]
    exact hendH
  have hgateP : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true := by
    rw [hpstore]
    exact hgateBoundary
  have hsupportP : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1) := by
    rw [hpstore]
    change HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext obs (n + 1))) (n + 1)
    exact hsupportBoundary
  have hrealized :=
    E.scheduledEventPrefix_acceptedTargetA32GateRealization_core_of_operationalEvidence
    cfg ext B hT hC.static_validators
      hC.byzantine_bound
      hC.phase0_source hC.phase0_boundary_source hanchor hboundary p hHn1
      hevidence hstate hval htab hendHP
      (fun Q => Q.scheduledDelivery_of_lookahead cfg ext E hC.synchrony)
      hanchorH hC.balance_floor
      hgateP hsupportP
  rw [hpstore] at hrealized
  simpa only [E.weakFcrStep_store] using hrealized

/-! ## The observer-call no-conflict certificate pinning producer

`Execution.noConflict_arithmeticBranch_oneThird`
(`NoConflictCertificatePinning.lean:91`) is the one place in this port where
substitution (a) cannot be applied in situ: its `hv` is consumed three levels
down, at `HonestWeight.lean:278`, as `hec.committees_agree v hv n slot …`, and
the strong lemma demands the membership proof as an explicit argument.

It is nonetheless *only* a committee readback.  The strong development already
factors that readback out: `CurrentTargetPrefixAccounting.lean` carries a
committee-explicit twin of the entire chain, ending at
`Execution.currentTarget_nonhonest_weight_le_adversarial_of_prefix` (`:189`),
which takes `CurrentTargetPrefixAccountingEvidence` and no honesty at all.
The arithmetic branch is therefore re-assembled below over that twin, which is
exactly what `completedScheduledEventPrefix_accountingEvidence_at_observer`
supplies at the observer's own boundary.  The "no honest equivocator" side
condition likewise comes from `evidence.operational.honest_not_equivocating`
— a fact about which *validators* are honest, not about the store's owner. -/

/-- Honesty-free twin of `Execution.noConflict_arithmeticBranch_oneThird`, over
the **raw** helper inequality rather than over either executable boolean: the
actual helper arithmetic puts strictly more than one third of total active
weight in the same concrete honest signer set used by the current-target
support bridge.

The honest-node binder is replaced by prefix accounting evidence for the very
store the arithmetic is read off, which is the only thing the strong proof's
`hv` ever reached.  Everything else in the body — score splitting, the future
honest remainder, observed/future disjointness, and
`Execution.latestMessageProvenance` — is already proved for an arbitrary
node.

This is **N4** of `docs/trunkB-two-case-discharge.md` §7.  Stating the premise
as `E.total_active cfg < 3 * compute_honest_ffg_support_for_current_target …`
lets the same arithmetic serve both live gate arms: the `previousNoConflict`
arm via `will_no_conflicting_checkpoint_be_justified` (the wrapper below, whose
statement is unchanged) and the `currentCrossing` arm via
`will_current_target_be_justified`, whose `3 · s ≥ 2 · T` implies `T < 3 · s`
once `0 < E.total_active cfg`. -/
theorem noConflict_arithmeticBranch_oneThird_of_rawGate
    (hA : NoConflictPinningAssumptions cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext v n) n)
    (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hraw : E.total_active cfg <
      3 * compute_honest_ffg_support_for_current_target cfg ext
        (E.store cfg ext v n)) :
    E.total_active cfg < 3 * E.weight
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state) := by
  obtain ⟨hgen, hwf, _hdiv, _hhb, hec, hsv, hbb, _hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let store := E.store cfg ext v n
  let observedHonest := E.currentTargetObservedHonestSupporters cfg store state
  let observedNonhonest :=
    E.currentTargetObservedNonhonestSupporters cfg store state
  let futureHonest := (E.currentTargetFutureSpan cfg store).filter
    (fun i => i ∈ E.honest)
  let score := get_current_target_score cfg ext store
  let start := currentTargetEpochStart cfg store
  let finish := get_current_slot cfg store - 1
  let estimate := estimate_committee_weight_between_slots cfg
    (E.total_active cfg) start finish
  let adversarial := compute_adversarial_weight cfg ext store state start finish
  let remaining := (E.total_active cfg - estimate) / 100 *
    (100 - cfg.confirmation_byzantine_threshold)
  have hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store) := by
    rw [show get_current_slot cfg store = E.slot_at cfg n by
      exact E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hscore : score =
      E.weight observedHonest + E.weight observedNonhonest := by
    simpa only [score, observedHonest, observedNonhonest, store,
      Execution.currentTargetObservedHonestSupporters,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.current_target_score_eq_honest_add_nonhonest_weight
        cfg ext hstate hval
  have hprov := hevidence.operational.latest_message_provenance
  have hbyz : E.weight observedNonhonest ≤ adversarial := by
    simpa only [observedNonhonest, adversarial, start, finish, store,
      currentTargetEpochStart,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.currentTarget_nonhonest_weight_le_adversarial_of_prefix cfg ext hbb
        hevidence hnH hval htab
  have hobserved : score - min adversarial score ≤
      E.weight observedHonest := by
    rw [hscore, Nat.min_def]
    split_ifs
    · apply (Nat.sub_le_iff_le_add).2
      exact Nat.add_le_add_left hbyz _
    · simp only [Nat.sub_self, Nat.zero_le]
  have hfuture : remaining ≤ E.weight futureHonest := by
    simpa only [remaining, estimate, start, finish, futureHonest, store] using
      E.currentTarget_remaining_honest_le_future_weight cfg ext
        hec hsv hbb hcurrentH hendH hanchorH hfloor
  have hdisjoint : Disjoint observedHonest futureHonest := by
    simpa only [observedHonest, futureHonest, store] using
      E.currentTarget_observed_future_disjoint cfg ext hec hprov
  have hgateArithmetic := hraw
  simp only [compute_honest_ffg_support_for_current_target] at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  have hgateArithmetic' : E.total_active cfg <
      3 * (score - min adversarial score + remaining) := by
    have hsub : score - adversarial = score - min adversarial score := by
      by_cases hle : adversarial ≤ score
      · rw [min_eq_left hle]
      · have hgt : score ≤ adversarial := Nat.le_of_lt (Nat.lt_of_not_ge hle)
        rw [min_eq_right hgt, Nat.sub_self, Nat.sub_eq_zero_of_le hgt]
    change E.total_active cfg < 3 * (score - adversarial + remaining) at hgateArithmetic
    rw [hsub] at hgateArithmetic
    simpa only [score, adversarial, remaining, estimate, start, finish,
      store, one_mul] using hgateArithmetic
  have hpredict : score - min adversarial score + remaining ≤
      E.weight observedHonest + E.weight futureHonest :=
    Nat.add_le_add hobserved hfuture
  have honeThird : E.total_active cfg <
      3 * (E.weight observedHonest + E.weight futureHonest) :=
    hgateArithmetic'.trans_le (Nat.mul_le_mul_left 3 hpredict)
  change E.total_active cfg <
    3 * E.weight (observedHonest ∪ futureHonest)
  rw [E.weight_union_disjoint hdisjoint]
  exact honeThird

/-- The no-conflict arm's executable gate, unchanged.  Away from the
`get_current_target = unrealized_justified` short circuit the boolean is
exactly the raw helper inequality, so this is now a wrapper over
`Execution.noConflict_arithmeticBranch_oneThird_of_rawGate` and carries no
proof content of its own. -/
theorem noConflict_arithmeticBranch_oneThird_of_prefixEvidence
    (hA : NoConflictPinningAssumptions cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext v n) n)
    (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hne : get_current_target cfg (E.store cfg ext v n) ≠
      (E.store cfg ext v n).unrealized_justified_checkpoint)
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v n) = true) :
    E.total_active cfg < 3 * E.weight
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state) := by
  apply E.noConflict_arithmeticBranch_oneThird_of_rawGate cfg ext hA
    hevidence hnH hstate hval htab hendH hanchorH hfloor
  have hgateArithmetic := hgate
  simp only [will_no_conflicting_checkpoint_be_justified, hne, if_false,
    decide_eq_true_eq] at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  simpa only [one_mul] using hgateArithmetic

/-- The crossing arm's executable gate implies the same one-third bound.

`will_current_target_be_justified` asserts `3 · support ≥ 2 · total_active`,
which is strictly stronger than the no-conflict gate as soon as the total
active weight is positive — and the minimum-balance floor gives exactly that
through `Execution.total_active_eq_anchorActive_weight` and
`Config.effective_balance_increment_pos`.  This is the second corollary of
**N4** (`docs/trunkB-two-case-discharge.md` §5.5, §7). -/
theorem noConflict_arithmeticBranch_oneThird_of_currentTargetGate
    (hA : NoConflictPinningAssumptions cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext v n) n)
    (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (E.store cfg ext v n) = true) :
    E.total_active cfg < 3 * E.weight
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state) := by
  apply E.noConflict_arithmeticBranch_oneThird_of_rawGate cfg ext hA
    hevidence hnH hstate hval htab hendH hanchorH hfloor
  have hgateArithmetic := hgate
  simp only [will_current_target_be_justified, decide_eq_true_eq]
    at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  have hpos : 0 < E.total_active cfg := by
    rw [E.total_active_eq_anchorActive_weight cfg hfloor]
    exact Nat.lt_of_lt_of_le cfg.effective_balance_increment_pos hfloor
  have hdouble : E.total_active cfg < 2 * E.total_active cfg := by
    rw [two_mul]
    exact Nat.lt_add_of_pos_left hpos
  exact Nat.lt_of_lt_of_le hdouble hgateArithmetic

omit [LinearOrder Root] [Inhabited Root] in
/-- A concrete assigned vote belongs to the committee union of its target
epoch.  Cloned rather than reused because the strong module's copy
(`AcceptedActualSelectedJustifiedOrientation.lean:97`) is `private`; the
statement mentions no node and no honesty. -/
private theorem mem_observerNoConflict_epoch_span_of_committee
    {i : ValidatorIndex} {s : Slot} {e : Epoch}
    (hcommittee : i ∈ E.committee s)
    (hepoch : compute_epoch_at_slot cfg s = e) :
    i ∈ E.span_committee (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := by
  have hdiv : s / cfg.slots_per_epoch = e := by
    simpa only [compute_epoch_at_slot] using hepoch
  have hlo : e * cfg.slots_per_epoch ≤ s := by
    have h := Nat.div_mul_le_self s cfg.slots_per_epoch
    rwa [hdiv] at h
  have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
    rw [hdiv, Nat.mul_add] at h
    simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
  have hhi : s ≤ e * cfg.slots_per_epoch +
      (cfg.slots_per_epoch - 1) := by
    have hpred := Nat.le_pred_of_lt hlt
    rw [Nat.pred_eq_sub_one,
      Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
    exact hpred
  simp only [Execution.span_committee, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hcommittee⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot between the canonical first and last slots of epoch `e` has epoch
exactly `e`.  Cloned rather than reused because the source copy
(`CurrentTargetFutureSupport.lean:65`) is `private`; the statement mentions no
node, no store, and no honesty. -/
private theorem observerNoConflict_epoch_eq_of_epoch_bounds
    {e : Epoch} {s : Slot}
    (hlo : e * cfg.slots_per_epoch ≤ s)
    (hhi : s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) :
    compute_epoch_at_slot cfg s = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le hlo
  calc
    s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := hhi
    _ < e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
      Nat.add_lt_add_left
        (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
    _ = (e + 1) * cfg.slots_per_epoch := by
      simp only [Nat.add_mul, one_mul]

/-- **N3** of `docs/trunkB-two-case-discharge.md` §7: case-β pinning of the
endpoint justification against the query's current target, with **no**
`HonestVotesSupportTarget` proviso.

Case β is the branch in which no honest member of the endpoint
justification's quorum voted at or after the query slot
(`hnoPostQuery`).  The proof is §5.3 of that note, i.e. the existing
arithmetic-branch argument with one seat argument swapped:

* the executable gate still puts more than one third of total active weight in
  the concrete honest signer set `currentTargetA32Signers` (N4, and note that
  the crossing arm supplies the same raw inequality, §5.5);
* `one_third_honest_intersects_two_thirds` still intersects that set with the
  two-thirds quorum, now taken from `Execution.EndpointJustifiedQuorumAt`
  rather than from a bare `SupermajorityLink`;
* an **observed** honest supporter is pinned exactly as before, by
  `no_forgery` plus `HonestBehavior.not_slashable`;
* a **future** seat is now excluded outright: by N1 the quorum attestation is
  assigned to the signer's committee slot and carries the target epoch, so
  `BeaconExternalsPremises.committee_assignment_unique` identifies its slot with the
  future seat's slot, which is at or after the query slot — contradicting
  `hnoPostQuery`.  This is where the proviso used to be consumed
  (`currentTargetFutureHonestSeat_vote`), and the replacement needs no
  statement about future votes at all.

The honesty and epoch-span side conditions on the signer set are re-derived
without the proviso, as §5.2 items 1-2 record. -/
theorem noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgateRaw :
      get_current_target cfg (E.store cfg ext obs (n + 1)) =
          (E.store cfg ext obs (n + 1)).unrealized_justified_checkpoint ∨
        E.total_active cfg <
          3 * compute_honest_ffg_support_for_current_target cfg ext
            (E.store cfg ext obs (n + 1)))
    {w : ValidatorIndex} {m : Nat}
    (Q : E.EndpointJustifiedQuorumAt cfg ext B.anchor w m)
    (hnoPostQuery : ¬ Q.PostQueryHonestSigner cfg ext (n + 1))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext obs (n + 1))).epoch) :
    (E.store cfg ext w m).justified_checkpoint.root =
      (get_current_target cfg (E.store cfg ext obs (n + 1))).root := by
  classical
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenZero : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgen⟩
  let hA := E.noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    cfg ext B hT hC.static_validators hC.byzantine_bound hanchor hboundary
  let hAccA : FFGAccountabilityAssumptions cfg ext E :=
    { genesis_store := hgenZero
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      externals_coherence := hT.externals_coherence
      static_validator_set := hC.static_validators
      byzantine_bound := hC.byzantine_bound }
  let hacc : CertificateAccountability cfg E B.anchor :=
    CertificateAccountability.of_assumptions cfg ext hAccA
  let store := E.store cfg ext obs (n + 1)
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  change (E.store cfg ext w m).justified_checkpoint.epoch = target.epoch
    at hepoch
  change (E.store cfg ext w m).justified_checkpoint.root = target.root
  obtain ⟨hc⟩ :=
    ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hstate : state = get_pulled_up_head_state cfg ext store := rfl
  have hval : state.validators = E.registry := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_validators_at_observer cfg ext hT
        hcoh hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
        hC.static_validators hcoh hHn1
  have hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg store) := by
    simpa only [store] using
      E.currentTargetEpochEnd_within_of_epochEndsFitUint64
        cfg ext hfit (v := obs) hHn1
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon :=
    E.completedPrefix_anchor_epoch_within cfg ext hT hC.static_validators
  have hstoreCausal : E.CausalStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext obs (n + 1)
  obtain ⟨hUJ⟩ :=
    ExactPrefixAcceptedFFGSemantics.unrealizedJustified_certificate
      cfg ext B hgenShort hanchor hstoreCausal
  by_cases heq : target = store.unrealized_justified_checkpoint
  · have hroot := hacc.justified_unique hc hUJ
      (hepoch.trans (congrArg Checkpoint.epoch heq))
    exact hroot.trans (congrArg Checkpoint.root heq).symm
  · have htargetNotAnchor : target ≠ B.anchor := by
      intro htargetAnchor
      have htargetEpoch : target.epoch =
          compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) := by
        simp only [target, store, get_current_target,
          get_checkpoint_for_block, get_current_store_epoch,
          E.store_current_slot cfg ext obs (n + 1)]
      have hUJLeTarget : store.unrealized_justified_checkpoint.epoch ≤
          target.epoch := by
        have hbound := (E.store_CkptEpochLe cfg ext
          hT.externals_coherence hT.whole_seconds hgenShort obs (n + 1)).2
        change store.unrealized_justified_checkpoint.epoch ≤
          compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) at hbound
        exact hbound.trans_eq htargetEpoch.symm
      have hanchorLeUJ : B.anchor.epoch ≤
          store.unrealized_justified_checkpoint.epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg) hUJ
      have hUJEpoch : store.unrealized_justified_checkpoint.epoch =
          B.anchor.epoch := by
        apply Nat.le_antisymm
        · exact hUJLeTarget.trans_eq
            (congrArg Checkpoint.epoch htargetAnchor)
        · exact hanchorLeUJ
      have hUJRoot : store.unrealized_justified_checkpoint.root =
          B.anchor.root :=
        hacc.justified_unique hUJ CertifiedJustified.anchor hUJEpoch
      have hUJAnchor : store.unrealized_justified_checkpoint = B.anchor := by
        generalize hu : store.unrealized_justified_checkpoint = u
          at hUJEpoch hUJRoot ⊢
        generalize ha : B.anchor = a at hUJEpoch hUJRoot ⊢
        cases u
        cases a
        simp only at hUJEpoch hUJRoot ⊢
        subst_vars
        rfl
      exact heq (htargetAnchor.trans hUJAnchor.symm)
    let p := E.completedScheduledEventPrefix obs n
    have hpstore : p.store cfg ext = store := by
      simpa only [p, store] using
        E.completedScheduledEventPrefix_store cfg ext obs n
    have hanchorBefore : B.anchor.epoch < target.epoch := by
      have hprefix := p.currentTarget_anchor_epoch_lt_of_ne
        cfg ext B hT hanchor hboundary
        (by
          rw [hpstore]
          simpa only [target, store] using htargetNotAnchor)
      simpa only [hpstore, target, store] using hprefix
    have hobservedVote : ∀ i ∈ E.currentTargetObservedHonestSupporters cfg
        store state,
        Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
          deadline target) := by
      intro i hiObserved
      let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
        cfg ext E B hT hanchor hboundary
      have hboundaryZero : TrustedAnchorBoundaryAligned
          (cfg := cfg) (E := E)
          (anchor := E.genesis_store.justified_checkpoint) := by
        simpa only [← hanchor] using hboundary
      have hvote :=
        E.currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
          cfg ext B hV hboundaryZero p
            (p.latestMessageProvenance_of_observer_validity cfg ext hT
              hcoh.validity hHn1) hHn1
            (by simpa only [hpstore, state, store] using hiObserved)
      rw [hpstore] at hvote
      simpa only [store, target, deadline] using hvote
    have hfutureSeat : ∀ i ∈ (E.currentTargetFutureSpan cfg store).filter
        (fun j => j ∈ E.honest),
        i ∈ E.honest ∧ ∃ s : Slot,
          E.slot_at cfg (n + 1) ≤ s ∧ i ∈ E.committee s ∧
            compute_epoch_at_slot cfg s = target.epoch := by
      intro i hiFuture
      simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
        Execution.span_committee, Finset.mem_biUnion,
        Finset.mem_Icc] at hiFuture
      obtain ⟨⟨s, hs, hiCommittee⟩, hi⟩ := hiFuture
      refine ⟨hi, s, ?_, hiCommittee, ?_⟩
      · rw [← E.store_current_slot cfg ext obs (n + 1)]
        exact hs.1
      · have hloCurrent : get_current_store_epoch cfg store *
            cfg.slots_per_epoch ≤ get_current_slot cfg store := by
          have h := Nat.div_mul_le_self (get_current_slot cfg store)
            cfg.slots_per_epoch
          simpa only [get_current_store_epoch, Nat.mul_comm] using h
        have hsEpoch : compute_epoch_at_slot cfg s =
            get_current_store_epoch cfg store := by
          apply observerNoConflict_epoch_eq_of_epoch_bounds cfg
          · exact hloCurrent.trans hs.1
          · simpa only [currentTargetEpochEnd, currentTargetEpochStart,
              compute_start_slot_at_epoch] using hs.2
        exact hsEpoch
    have hsignersHonest : signers ⊆ E.honest := by
      intro i hi
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hi
      rcases hi with hiObserved | hiFuture
      · obtain ⟨vote⟩ := hobservedVote i hiObserved
        exact vote.honest
      · exact (hfutureSeat i hiFuture).1
    have hsignersEpoch : signers ⊆
        E.span_committee (target.epoch * cfg.slots_per_epoch)
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
      intro i hi
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hi
      rcases hi with hiObserved | hiFuture
      · obtain ⟨vote⟩ := hobservedVote i hiObserved
        exact mem_observerNoConflict_epoch_span_of_committee cfg
          vote.assigned vote.slot_epoch
      · obtain ⟨_hi, s, _hsQuery, hiCommittee, hsEpoch⟩ :=
          hfutureSeat i hiFuture
        exact mem_observerNoConflict_epoch_span_of_committee cfg
          hiCommittee hsEpoch
    have hevidence := E.completedScheduledEventPrefix_accountingEvidence_at_observer
      cfg ext hT hcoh n hHn1
    have hraw : E.total_active cfg <
        3 * compute_honest_ffg_support_for_current_target cfg ext store :=
      hgateRaw.resolve_left heq
    have honeThird : E.total_active cfg < 3 * E.weight signers := by
      simpa only [signers, store, state] using
        E.noConflict_arithmeticBranch_oneThird_of_rawGate cfg ext hA
          hevidence hHn1 hstate hval htab hendH hanchorH hC.balance_floor
          hraw
    have hcurrentH : E.SlotWithinHorizon cfg
        (get_current_slot cfg store) := by
      rw [show get_current_slot cfg store = E.slot_at cfg (n + 1) by
        simpa only [store] using
          E.store_current_slot cfg ext obs (n + 1)]
      exact ⟨hHn1.2.1, hHn1.2.2⟩
    let U := E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1))
    have hspanEq : U = E.currentTargetAnchorActive cfg := by
      simpa only [U, target, store, get_current_target,
        get_checkpoint_for_block, currentTargetEpochStart,
        currentTargetEpochEnd, compute_start_slot_at_epoch] using
        E.current_epoch_span_eq_anchorActive cfg ext
          hT.externals_coherence hC.static_validators hcurrentH hendH
            hanchorH
    have hU : E.weight U ≤ E.total_active cfg := by
      rw [hspanEq, ← E.total_active_eq_anchorActive_weight
        cfg hC.balance_floor]
    have hTU : Q.signers ⊆ U := by
      intro i hi
      have hiEpoch := Q.signers_in_epoch hi
      simpa only [U, hepoch] using hiEpoch
    obtain ⟨i, hiSigner, hiQ, hiHonest⟩ :=
      one_third_honest_intersects_two_thirds E
        hsignersEpoch hTU hsignersHonest hU honeThird Q.supermajority
    obtain ⟨u, n', a, fb, hsched, hia, haTarget, haH, ha0, haEpoch,
      haCommittee, haBound⟩ := Q.signer_attestation i hiQ
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · obtain ⟨vote⟩ := hobservedVote i hiObserved
      obtain ⟨kCompeting, aCompeting, hvoteCompeting,
          hdataCompeting⟩ := hT.honest_behavior.no_forgery
            u n' a fb hsched i hiHonest hia
      let aTarget := honest_attestation cfg ext
        (E.store cfg ext i vote.time) vote.slot vote.index i
      have hvoteTarget : E.vote i vote.slot =
          some (vote.time, aTarget) := by
        simpa only [aTarget] using vote.vote
      have haTargetExact : aTarget.data.target = target := by
        simpa only [aTarget] using vote.target_eq
      have haCompetingExact : aCompeting.data.target =
          (E.store cfg ext w m).justified_checkpoint := by
        rw [← hdataCompeting]
        exact haTarget
      by_contra hroot
      have hdataNe : aTarget.data ≠ aCompeting.data := by
        intro hdataEq
        have htargets := congrArg
          (fun d : AttestationData Root => d.target) hdataEq
        change aTarget.data.target = aCompeting.data.target at htargets
        rw [haTargetExact, haCompetingExact] at htargets
        exact hroot (congrArg Checkpoint.root htargets).symm
      have htargetEpoch :
          aTarget.data.target.epoch =
            aCompeting.data.target.epoch := by
        rw [haTargetExact, haCompetingExact]
        exact hepoch.symm
      have hslash : is_slashable_attestation_data
          aTarget.data aCompeting.data = true := by
        simp [is_slashable_attestation_data, hdataNe, htargetEpoch]
      have hnot := hT.honest_behavior.not_slashable i hiHonest
        vote.slot a.data.slot vote.time kCompeting aTarget aCompeting
        hvoteTarget hvoteCompeting
      rw [hslash] at hnot
      contradiction
    · exfalso
      obtain ⟨_hi, s, hsQuery, hiCommittee, hsEpoch⟩ :=
        hfutureSeat i hiFuture
      have haSlotEpoch : compute_epoch_at_slot cfg a.data.slot =
          compute_epoch_at_slot cfg s := by
        rw [hsEpoch, haEpoch]
        exact hepoch
      have haSlotEq : a.data.slot = s :=
        hT.externals_coherence.committee_assignment_unique i a.data.slot s
          haCommittee hiCommittee haSlotEpoch
      apply hnoPostQuery
      exact ⟨i, hiQ, hiHonest, u, n', a, fb, hsched, hia, haTarget, haH,
        ha0, haBound, by rw [haSlotEq]; exact hsQuery⟩

set_option maxRecDepth 10000 in
/-- **N6** of `docs/trunkB-two-case-discharge.md` §7 at a possibly-Byzantine
observer: the executable gate alone decides, for every endpoint, between the
trusted anchor, a post-query honest quorum member, and same-epoch pinning
against the query's current target.

The case split is `by_cases` on
`Execution.EndpointJustifiedQuorumAt.PostQueryHonestSigner` applied to the
quorum N1 extracts from a non-anchor endpoint justification; case α is N2 and
case β is N3 above.  Neither the quorum extraction nor the case-β pinning
mentions the observer's honesty, so this is the observer twin of
`Execution.completedPrefix_endpointOriginOrPinnedProducerAt` with the honest
binder replaced by `Execution.ObserverCoherence`. -/
theorem observerCall_endpointOriginOrPinnedProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
  classical
  intro hgate w m
  simp only [E.weakFcrStep_store] at hgate ⊢
  have htab : get_total_active_balance cfg
      (get_pulled_up_head_state cfg ext (E.store cfg ext obs (n + 1))) =
      E.total_active cfg :=
    E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
      hC.static_validators hcoh hHn1
  have hpos : 0 < E.total_active cfg := by
    rw [E.total_active_eq_anchorActive_weight cfg hC.balance_floor]
    exact Nat.lt_of_lt_of_le cfg.effective_balance_increment_pos
      hC.balance_floor
  have hgateRaw := E.rawGate_of_executableGate cfg ext htab hpos hgate
  by_cases hne : (E.store cfg ext w m).justified_checkpoint = B.anchor
  · exact Or.inl hne
  · obtain ⟨Q⟩ :=
      ExactPrefixAcceptedFFGSemantics.endpointJustified_quorumAt
        cfg ext B hT hanchor hboundary hne
    by_cases hpost : Q.PostQueryHonestSigner cfg ext (n + 1)
    · exact Or.inr (Or.inl
        (EndpointJustifiedQuorumAt.causalHonestTargetAt_of_postQuerySigner
          cfg ext hT.honest_behavior hpost))
    · refine Or.inr (Or.inr fun hepoch => ?_)
      exact
        E.noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer
          cfg ext B hT hC hfit hanchor hboundary hcoh hHn1 hgateRaw Q hpost
          hepoch

end Execution

end FastConfirmation.Spec

end
