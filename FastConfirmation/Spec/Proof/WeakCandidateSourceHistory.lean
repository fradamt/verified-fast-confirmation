module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedCurrentSameSourceHistory
public import FastConfirmation.Spec.Proof.WeakCandidateHistoryRecurrence
public import FastConfirmation.Spec.Proof.WeakEarlyPhaseSourceWiring

@[expose] public section

/-!
# Spec / Proof / WeakCandidateSourceHistory

Stage S6 of the `hfilter`-discharge wave: the weak twin of
`AcceptedCurrentSameSourceHistory.lean`'s paper-Lemmas-22--26 candidate-source
history, run over the *observer's own* weak call trajectory
(`E.weakFcr` / `E.weakFcrStep` / `E.weakConfirmed`, `E.weakGetLatestConfirmed
TraceAt`) at a validator which need not be honest.

## The substitution table

Every use of the query node's honesty binder in the strong development
resolves to one of three things (the wave's stage-S0 audit), and each is
replaced here by its landed observer-side twin:

* `store_domainK_of_selectedMarginDomain … hv` becomes
  `Execution.observerStoreDomainK` (`WeakObserverDomain.lean`);
* `head_root_known_of_selectedMarginDomain … hv` becomes
  `Execution.head_root_known_at_observer` (same file);
* `hsync.block_relay` of a seed out of the observer's own store becomes one
  of the landed certificate-dissemination lemmas (below);
* `StrictSelectorAdvanceAt.mechanicalFacts … hv` becomes
  `Weak.strictSelectedResultMechanicalFacts … hcoh` (`WeakSelectedTrace.lean`);
* `not_epochStart_of_current_of_selectedMargin … hv` becomes
  `Weak.…not_epochStart_of_current` composed with
  `Weak.…confirmedPastDescendantSlotWitness_at_observer`.

The one structural consequence is in the two source-history records. The
strong `AcceptedLemma22EpochStartCandidateSourceAt` carries
`validator_honest` plus a `relay_gate`, and `lemma24` turns that pair into
the endpoint's copy of the seed with `hsync.block_relay`. At a Byzantine
observer there is no such relay, so both fields are replaced by the
*conclusion* the relay was used for:

```lean
  seed_disseminated : ∀ w ∈ E.honest, seed ∈ (E.store cfg ext w boundary).block_roots
```

and, one level up, `Weak.AcceptedCurrentCandidateSourceOriginAt` carries the
time-indexed form (`∀ w ∈ E.honest, ∀ m, … E.slot_at cfg originSecond ≤
E.slot_at cfg m → seed ∈ (E.store cfg ext w m).block_roots`). Both are
discharged, never assumed:

* strict-advance origins: the Lemma-13 seed *is* the query fork-choice head
  (`Weak.…currentHeadLemma13SourceSeedCertified_of_notStart`, stage S5),
  which carries `has_head_broadcast_certificate` in the same case split, so
  `Weak.headSeed_known_at_all_honest_endpoints_at_observer` (stage S3)
  disseminates it;
* the trusted-anchor origin: the anchor root is in `E.genesis_store
  .block_roots`, hence in every store by `Execution.store_storeLE`;
* the epoch-start banked candidate (site 8 of the design's inventory): its
  *seed* is the banking certificate's `supplier`, so the consumption lemma
  called is the finer
  `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`
  (`WeakBankedJustification.lean`) rather than the packaged
  `bankedRoot_known_at_all_honest_endpoints_at_observer` — the banked root is
  the Lemma-22 *candidate*, and the seed has to be the block whose voting
  source is that candidate. The anchor arm needs no certificate at all
  (global knownness from `E.genesis_store`), matching that lemma's own
  anchor arm.

## What is delivered

* the two records `Weak.AcceptedCurrentCandidateSourceOriginAt` (+
  `mono_upper`) and `Weak.AcceptedLemma22EpochStartCandidateSourceAt`, and
  `…lemma24` into the (reused, honesty-free) strong
  `Execution.AcceptedLemma24EpochStartSourceAt`;
* the three origin producers:
  `Weak.acceptedCurrentCandidateSourceOriginAt_anchor`,
  `Weak.AcceptedCurrentCandidateSourceOriginAt.toLemma22AtNextBoundary`, and
  `Weak.StrictSelectedResultMechanicalFacts.currentCandidateSourceOrigin`
  (with `Weak.StrictSelectorAdvanceAt.mechanicalFacts`);
* the boundary step, in query-generic form
  (`Weak.bankedEpochStartCandidateSource_of_certifiedBank`) and at an actual
  call (`Weak.ObservedResetCandidateInputAt.
  acceptedLemma22EpochStartCandidateSource`);
* the honesty-free clock clones `Weak.actualCall_epochStart_boundarySecond`
  and `Weak.previousConfirmed_current_of_boundary_recent`;
* the invariant `Weak.AcceptedConfirmedSourceHistoryAt`, its four step
  lemmas (`…_zero`, `…succ_of_noCall`, `…confirmedKnown_succ_of_call`,
  `…currentOrigin_succ_of_call`, `…recentSource_succ_of_call`), the combined
  `…succ_of_call`, the all-seconds `Weak.acceptedConfirmedSourceHistoryAt`,
  and the evaluator export
  `Weak.getLatestConfirmedTraceAt_current_epochStartSource`;
* the S6 → S7 bridge `Weak.StrictSelectedResultMechanicalFacts.
  currentSame_sourceHistoryOutcome_of_epochStartSource` and its actual-call
  form `…actualCurrentSame_sourceHistoryOutcome`, into the reused strong
  outcome type `Execution.AcceptedCurrentSameSourceHistoryOutcome`.

The weak evaluator trace and the four-way call-branch recurrence this
induction runs over live in `WeakCandidateHistoryRecurrence.lean` (split out
for the same reason the strong development splits
`AcceptedCandidateHistoryRecurrence.lean` from this file: that layer mentions
no assumption bundle at all).

## Divergences from the design (`/tmp/hfilter-wave-design.md` §(C) site 8,
`/tmp/delta5-proposal.md` §5), where the landed state won

1. **No `seed_certified` field is plumbed.** The design proposed extending
   `AcceptedCurrentCandidateSourceOriginAt` with a raw certificate field and
   re-deriving dissemination at each boundary. Since delta 5 landed with the
   consumption lemmas already proved, the records carry the *dissemination
   conclusion* instead; no certificate ever crosses a record boundary.
2. **The banked seed is the supplier, and it is provably old at the
   boundary.** Head-indexed banking (`banked = UJ[supplier]`,
   `supplier = head at the banking second`) makes the boundary step direct:
   `get_voting_source store supplier = GU supplier = banked` needs `supplier`
   to be a *previous-epoch* block at the boundary, and that is forced by the
   gate itself — `Weak.has_broadcast_certificate_span_nonempty` gives
   `get_block_slot store supplier ≤ get_current_slot store - 1`, i.e. the
   supplier's slot is strictly below the epoch's first slot. The strong
   development had to reach for the installer tip's *earlier installation
   second* to get the same "old" fact.
3. **`Weak.staleBanked_fails_observedRestartGuard` is not needed.** The
   delta-5 proposal (§3) expected the boundary step to have to rule out a
   value banked at an earlier epoch. Under the revised rule it does not: the
   supplier's slot is below the *banking* second's current slot, and the
   banking second is at or before the boundary second, so the supplier is old
   at the boundary whichever epoch banked it. The recency the argument needs
   comes from the executable guard conjunct
   `observed_previous_epoch` instead. The lemma is therefore not proved here;
   nothing in the induction asks for it.
4. **`AcceptedLemma22EpochStartCandidateSourceAt.strictly_before_boundary`
   is relaxed to `second_le_boundary`, and that is the only relaxation.** The
   delta-5 proposal suggested `second ≤ boundary` to accommodate a same-slot
   certificate; it is needed exactly for the banked arm's `second` (the
   certificate may be minted at the boundary second itself), and nowhere
   else — the *seed*'s own recency is not affected (see 2). No consumer of
   the record reads the field.
5. **`hspe : 1 < cfg.slots_per_epoch` disappears from the premise surface.**
   The strong induction carries it only to run the observed-reset arm's
   accepted *installation* witness (`AcceptedUJCacheInstallationAt`, via
   `ObservedResetCandidateInputAt.acceptedInstallation`). Rule delta 5's
   head-indexed banking replaces that witness with the banked certificate,
   which needs no such hypothesis.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Narrow lower bundle adapter -/

/-- Weak-side copy of `AcceptedCurrentSameSourceHistory.lean`'s private
`selectedMarginAssumptions_of_sourceHistoryInputs` (that one is `private`, so
it cannot be reused across modules). Public theorems below expose the
independent constituents rather than `SelectedMarginAssumptions` itself. -/
private def selectedMarginAssumptions_of_sourceHistoryInputs
    {E : Execution Root}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := hT.genesis_structure
    wellFormed := hT.wellFormed
    whole_seconds := hT.whole_seconds
    honest_behavior := hT.honest_behavior
    synchrony := hsync
    externals_coherence := hT.externals_coherence
    static_validators := hstatic
    byzantine_bound := hbyz
    domain := hdomain }

/-! ## The two weak source-history records -/

/-- Weak twin of `Execution.AcceptedCurrentCandidateSourceOriginAt`: the
candidate-specific payload retained while a confirmed candidate is
current-epoch at the observer.

The added field `seed_disseminated` replaces the strong development's
implicit reliance on the observer being honest (i.e. on
`PaperSafetySynchrony.block_relay` being applicable at the origin second). It
is stated in the "same-slot-capable" form the landed certificate
dissemination lemmas produce: knownness at every honest endpoint whose slot
is at or past the origin second's slot. -/
structure AcceptedCurrentCandidateSourceOriginAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (upper : Nat) (candidate : Root) where
  originSecond : Nat
  origin_le : originSecond ≤ upper
  origin_within : E.WithinHorizon cfg originSecond
  candidate_known : candidate ∈
    (E.store cfg ext v originSecond).block_roots
  candidate_current : get_block_epoch cfg
      (E.store cfg ext v originSecond) candidate =
    get_current_store_epoch cfg (E.store cfg ext v originSecond)
  seed : Root
  seed_known : seed ∈ (E.store cfg ext v originSecond).block_roots
  seed_descends_candidate : is_ancestor
    (E.store cfg ext v originSecond)
    (get_node_for_root seed) (get_node_for_root candidate) = true
  gu_recent : get_current_store_epoch cfg
      (E.store cfg ext v originSecond) ≤ (B.state.GU seed).epoch + 1
  /-- the observer-side replacement for `hsync.block_relay`: the retained
  seed is known at every honest endpoint at or past the origin's slot. -/
  seed_disseminated : ∀ w ∈ E.honest, ∀ m : Nat, E.WithinHorizon cfg m →
    E.slot_at cfg originSecond ≤ E.slot_at cfg m →
      seed ∈ (E.store cfg ext w m).block_roots

/-- Forget only the upper time bound. -/
def AcceptedCurrentCandidateSourceOriginAt.mono_upper
    {E : Execution Root} {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {v : ValidatorIndex} {n m : Nat} {candidate : Root}
    (h : Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B v n candidate)
    (hnm : n ≤ m) :
    Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B v m candidate :=
  { h with origin_le := h.origin_le.trans hnm }

/-- Weak twin of `Execution.AcceptedLemma22EpochStartCandidateSourceAt`: the
exact boundary specialization of paper Lemma 22 at a possibly-Byzantine
observer.

Two fields of the strong record are gone — `validator_honest` and
`relay_gate` — and one is new: `seed_disseminated`, the conclusion the strong
`lemma24` extracted from those two via `hsync.block_relay`.
`strictly_before_boundary` is weakened to `second_le_boundary`, which is all
any consumer uses and which the epoch-start banked arm needs (its certificate
may be minted at the boundary second itself). -/
structure AcceptedLemma22EpochStartCandidateSourceAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (e : Epoch) (candidate : Root) where
  validator : ValidatorIndex
  second : Nat
  second_within : E.WithinHorizon cfg second
  boundary_within : E.WithinHorizon cfg
    (E.slot_start cfg (compute_start_slot_at_epoch cfg e))
  second_le_boundary : second ≤
    E.slot_start cfg (compute_start_slot_at_epoch cfg e)
  candidate_known : candidate ∈
    (E.store cfg ext validator second).block_roots
  seed : Root
  seed_known_past : seed ∈
    (E.store cfg ext validator second).block_roots
  seed_descends_candidate : is_ancestor
    (E.store cfg ext validator second)
    (get_node_for_root seed) (get_node_for_root candidate) = true
  seed_known_boundary : seed ∈
    (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots
  boundary_epoch : get_current_store_epoch cfg
    (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) = e
  source_recent : e ≤
    (get_voting_source cfg
      (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) seed).epoch + 2
  /-- the observer-side replacement for `hsync.block_relay` at the boundary. -/
  seed_disseminated : ∀ w ∈ E.honest,
    seed ∈ (E.store cfg ext w
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots

/-- Paper Lemma 24 from one weak Lemma-22 boundary witness. The strong
proof's single relay is replaced by the record's `seed_disseminated` field;
the rest (accepted fixed-root selector monotonicity between two same-epoch
causal stores) is honesty-free and reused verbatim. The conclusion type is
the **strong** `Execution.AcceptedLemma24EpochStartSourceAt`, which mentions
only the receiving honest endpoint's own store and therefore needs no weak
twin. -/
theorem AcceptedLemma22EpochStartCandidateSourceAt.lemma24
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {e : Epoch} {candidate : Root}
    (h : Weak.AcceptedLemma22EpochStartCandidateSourceAt cfg ext E B e candidate)
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B e w) := by
  let boundary := E.slot_start cfg (compute_start_slot_at_epoch cfg e)
  have hseedW : h.seed ∈ (E.store cfg ext w boundary).block_roots :=
    h.seed_disseminated w hw
  have hwEpoch : get_current_store_epoch cfg
      (E.store cfg ext w boundary) = e := by
    simpa only [get_current_store_epoch, E.store_current_slot, boundary]
      using h.boundary_epoch
  have hclock : get_current_store_epoch cfg
      (E.store cfg ext h.validator boundary) ≤
      get_current_store_epoch cfg (E.store cfg ext w boundary) := by
    rw [h.boundary_epoch, hwEpoch]
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hT.wellFormed
      (E.store_causal cfg ext h.validator boundary)
      (E.store_causal cfg ext w boundary)
      (by simpa only [boundary] using h.seed_known_boundary)
      hseedW hclock
  exact ⟨{
    seed := h.seed
    seed_known := by simpa only [boundary] using hseedW
    source_recent := h.source_recent.trans
      (Nat.add_le_add_right hsourceMono 2)
  }⟩

/-! ## The trusted-anchor origin -/

/-- Weak twin of `Execution.acceptedCurrentCandidateSourceOriginAt_anchor`.
Every ingredient of the strong proof is honesty-free; the only addition is
`seed_disseminated`, which for the anchor root is `Execution.store_storeLE`
from `E.genesis_store`. -/
theorem acceptedCurrentCandidateSourceOriginAt_anchor
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {n : Nat}
    (hHn : E.WithinHorizon cfg n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v n) B.anchor.root =
      get_current_store_epoch cfg (E.store cfg ext v n)) :
    Nonempty (Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B v n
      B.anchor.root) := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary v n
  have haccepted : E.AcceptedRoot cfg ext B.anchor.root :=
    E.acceptedRoot_of_causal_known cfg ext
      (E.store_causal cfg ext v n) hreal.root_known
  have hblockEpochLeAnchor : get_block_epoch cfg
      (E.store cfg ext v n) B.anchor.root ≤ B.anchor.epoch := by
    have hscaled : get_block_epoch cfg
          (E.store cfg ext v n) B.anchor.root * cfg.slots_per_epoch ≤
        B.anchor.epoch * cfg.slots_per_epoch :=
      (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v n) B.anchor.root).trans
          hreal.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hanchorLeGU :=
    Execution.ExactPrefixAcceptedFFGSemantics.anchor_epoch_le_gu
      (E := E) cfg ext B haccepted
  have hanchorRoot : B.anchor.root = ablk.root := by
    rw [hanchor, hgen]; rfl
  have hgenesisKnown : ∀ (u : ValidatorIndex) (m : Nat),
      B.anchor.root ∈ (E.store cfg ext u m).block_roots := by
    intro u m
    have hknown0 : B.anchor.root ∈ (E.store cfg ext u 0).block_roots := by
      change B.anchor.root ∈ E.genesis_store.block_roots
      rw [hgen, hanchorRoot]
      simp only [get_forkchoice_store, List.mem_singleton]
    exact (E.store_storeLE cfg ext u (Nat.zero_le m)).1 hknown0
  exact ⟨{
    originSecond := n
    origin_le := Nat.le_refl n
    origin_within := hHn
    candidate_known := hreal.root_known
    candidate_current := hcurrent
    seed := B.anchor.root
    seed_known := hreal.root_known
    seed_descends_candidate := is_ancestor_refl _ _
    gu_recent := by
      rw [← hcurrent]
      exact hblockEpochLeAnchor.trans
        (hanchorLeGU.trans (Nat.le_add_right _ _))
    seed_disseminated := fun u _hu m _hmH _hgate => hgenesisKnown u m
  }⟩

/-! ## Carrying a current-epoch origin across the next boundary -/

/-- Weak twin of `Execution.AcceptedCurrentCandidateSourceOriginAt.
toLemma22AtNextBoundary`. The strong proof's `hv` is used for exactly one
field (`validator_honest`); here the new `seed_disseminated` field is
produced from the origin's own time-indexed dissemination at the boundary
second, whose gate `E.slot_at cfg originSecond ≤ E.slot_at cfg (n + 1)` is
monotonicity of the clock along `originSecond ≤ n`. -/
theorem AcceptedCurrentCandidateSourceOriginAt.toLemma22AtNextBoundary
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {e : Epoch} {candidate : Root}
    (hboundarySecond : E.slot_start cfg
      (compute_start_slot_at_epoch cfg e) = n + 1)
    (hboundaryEpoch : get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)) = e)
    (hcandidateBoundary : candidate ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (hprevious : get_block_epoch cfg
      (E.store cfg ext v (n + 1)) candidate + 1 = e)
    (h : Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B v n candidate) :
    Nonempty (Weak.AcceptedLemma22EpochStartCandidateSourceAt cfg ext E B e
      candidate) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have horiginLeBoundary : h.originSecond ≤ n + 1 :=
    h.origin_le.trans (Nat.le_succ n)
  have hseedBoundary : h.seed ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v horiginLeBoundary).1 h.seed_known
  have hcandidateAgree :
      (E.store cfg ext v h.originSecond).blocks candidate =
        (E.store cfg ext v (n + 1)).blocks candidate :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v h.originSecond)
      (E.blockProvenance cfg ext v (n + 1))
      h.candidate_known hcandidateBoundary
  have hseedAgree :
      (E.store cfg ext v h.originSecond).blocks h.seed =
        (E.store cfg ext v (n + 1)).blocks h.seed :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v h.originSecond)
      (E.blockProvenance cfg ext v (n + 1))
      h.seed_known hseedBoundary
  have horiginEpochSucc : get_current_store_epoch cfg
        (E.store cfg ext v h.originSecond) + 1 = e := by
    calc
      get_current_store_epoch cfg (E.store cfg ext v h.originSecond) + 1 =
          get_block_epoch cfg
              (E.store cfg ext v h.originSecond) candidate + 1 := by
        rw [h.candidate_current]
      _ = get_block_epoch cfg
              (E.store cfg ext v (n + 1)) candidate + 1 := by
        simp only [get_block_epoch, hcandidateAgree]
      _ = e := hprevious
  have hseedEpochLeOrigin : get_block_epoch cfg
        (E.store cfg ext v h.originSecond) h.seed ≤
      get_current_store_epoch cfg (E.store cfg ext v h.originSecond) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
            v h.originSecond h.seed h.seed_known)
  have hseedOld : get_current_store_epoch cfg
        (E.store cfg ext v (n + 1)) >
      get_block_epoch cfg (E.store cfg ext v (n + 1)) h.seed := by
    rw [hboundaryEpoch]
    have hseedEpochLeOrigin' : get_block_epoch cfg
          (E.store cfg ext v (n + 1)) h.seed ≤
        get_current_store_epoch cfg
          (E.store cfg ext v h.originSecond) := by
      simpa only [get_block_epoch, hseedAgree] using hseedEpochLeOrigin
    exact hseedEpochLeOrigin'.trans_lt
      (by exact Nat.lt_of_succ_le (horiginEpochSucc.le))
  have hsourceEq : get_voting_source cfg
      (E.store cfg ext v (n + 1)) h.seed = B.state.GU h.seed := by
    rw [(E.store_causal cfg ext v (n + 1)
      ).getVotingSource_eq_acceptedSelector cfg ext B hseedBoundary]
    exact if_pos hseedOld
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    unfold Execution.IsFCRCallAt at hcall
    simpa only [E.store_current_slot] using hcall
  have hgateBoundary : E.slot_at cfg h.originSecond ≤ E.slot_at cfg (n + 1) :=
    E.slot_at_mono cfg horiginLeBoundary
  exact ⟨{
    validator := v
    second := h.originSecond
    second_within := h.origin_within
    boundary_within := by simpa only [hboundarySecond] using hHn1
    second_le_boundary := by
      simpa only [hboundarySecond] using horiginLeBoundary
    candidate_known := h.candidate_known
    seed := h.seed
    seed_known_past := h.seed_known
    seed_descends_candidate := h.seed_descends_candidate
    seed_known_boundary := by
      simpa only [hboundarySecond] using hseedBoundary
    boundary_epoch := by
      simpa only [hboundarySecond] using hboundaryEpoch
    source_recent := by
      rw [hboundarySecond, hsourceEq]
      calc
        e = get_current_store_epoch cfg
              (E.store cfg ext v h.originSecond) + 1 :=
          horiginEpochSucc.symm
        _ ≤ ((B.state.GU h.seed).epoch + 1) + 1 :=
          Nat.add_le_add_right h.gu_recent 1
        _ = (B.state.GU h.seed).epoch + 2 := by
          simp only [Nat.add_assoc, Nat.reduceAdd]
    seed_disseminated := by
      intro u hu
      rw [hboundarySecond]
      exact h.seed_disseminated u hu (n + 1) hHn1 hgateBoundary
  }⟩

/-! ### One-second clock geometry, honesty-free -/

/-- Honesty-free clone of `Execution.actualCall_epochStart_boundarySecond`.
That theorem's `_hv : v ∈ E.honest` binder is already unused in its body (it
only ever consults the clock through `query_slot_start_facts_minimal`), but a
required explicit argument cannot be supplied at a possibly-Byzantine
observer, so the body is copied with the binder dropped — the same
"copy, don't route through" move `ObserverCoherence.justified_root_known_of_
acceptedGlobalTrajectory` documents. -/
theorem actualCall_epochStart_boundarySecond
    {E : Execution Root} (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true) :
    E.slot_start cfg (compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1)))) = n + 1 := by
  let hA := Weak.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  let e := get_current_store_epoch cfg (E.store cfg ext v (n + 1))
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
      E.store_current_slot] using hstart
  have hslotBoundaryRaw : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg e := by
    simpa only [e, get_current_store_epoch, E.store_current_slot]
      using hslotBoundaryRaw
  rw [← hslotBoundary]
  obtain ⟨hstartLe, _hstartH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA (n + 1) hHn1
  apply Nat.le_antisymm hstartLe
  by_contra hnot
  have hlt : E.slot_start cfg (E.slot_at cfg (n + 1)) < n + 1 :=
    Nat.lt_of_not_ge hnot
  have hleN : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ n :=
    Nat.lt_succ_iff.mp hlt
  have hslotLe := E.slot_at_mono cfg hleN
  rw [hslotStart] at hslotLe
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    unfold Execution.IsFCRCallAt at hcall
    simpa only [E.store_current_slot] using hcall
  exact (Nat.not_lt_of_ge hslotLe) hslotAdvance


/-! ## The boundary step (design site 8): the banked epoch-start candidate -/

set_option maxRecDepth 4000 in
/-- **Site 8, closed at a Byzantine observer.** An epoch-start weak query
store whose banked observed-justified checkpoint satisfies rule delta 5's
input invariant supplies the exact paper-Lemma-22 boundary witness for that
banked value, with no relay.

The statement is query-generic (the actual-call wrapper below feeds it
`E.weakFcrStep` and discharges `hbank` along the trajectory), which is also
what keeps the bookkeeping function folded throughout the proof.

Both arms of `Weak.CertifiedBankedJustification` produce a seed whose
dissemination at the boundary is already a landed theorem:

* **anchor arm** — the banked root is in `E.genesis_store.block_roots`, hence
  in every store (`Execution.store_storeLE`); it is its own seed, its voting
  source is `GU` of the anchor root, and `anchor_epoch_le_gu` plus the
  executable guard `hprev` give the `+2` bound;
* **certified arm** — the seed is the certificate's `supplier`, the head at
  the banking second, disseminated by
  `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`. Rule delta
  5's head-indexed banking makes the source identity *definitional*:
  `banked = UJ[supplier] = GU supplier`, so the boundary store's voting
  source for the seed is the banked checkpoint itself, provided the supplier
  is a previous-epoch block there — which the certificate gate forces, since
  `Weak.has_broadcast_certificate_span_nonempty` puts the supplier's slot at
  or below `get_current_slot - 1` of the banking second, and the banking
  second is at or before this epoch-start second. The `+2` bound is then
  `hprev` plus `AcceptedSelectorAUCarrier.resetCheckpointRealizedAt`'s
  boundary geometry for the AU checkpoint `GU supplier`.

This is where the design's proposed `seed_certified` plumbing and the
delta-5 proposal's `staleBanked_fails_observedRestartGuard` would have gone;
neither is needed (module docstring, divergences 1--3). -/
theorem bankedEpochStartCandidateSource_of_certifiedBank
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {query : FastConfirmationStore Root}
    (hqstore : query.store = E.store cfg ext obs (n + 1))
    (hbank : Weak.CertifiedBankedJustification cfg ext E obs (n + 1) query)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true)
    (hprev : get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store) :
    Nonempty (Weak.AcceptedLemma22EpochStartCandidateSourceAt cfg ext E B
      (get_current_store_epoch cfg (E.store cfg ext obs (n + 1)))
      query.current_epoch_observed_justified_checkpoint.root) := by
  have hA := Weak.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  -- Clock geometry at the boundary.
  have hstart' : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs (n + 1))) = true := by
    rw [← hqstore]; exact hstart
  have hboundarySecond :
      E.slot_start cfg (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext obs (n + 1)))) = n + 1 :=
    Weak.actualCall_epochStart_boundarySecond cfg ext hT hsync hstatic hbyz
      hdomain hHn1 hcall hstart'
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
      E.store_current_slot] using hstart'
  have hslotBoundaryRaw : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) := by
    simpa only [get_current_store_epoch, E.store_current_slot]
      using hslotBoundaryRaw
  have hboundaryH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))))) := by
    rw [hboundarySecond]; exact hHn1
  have hboundaryEpoch : get_current_store_epoch cfg
      (E.store cfg ext obs
        (E.slot_start cfg (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1)))))) =
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    rw [hboundarySecond]
  have hprev' : get_block_epoch cfg (E.store cfg ext obs (n + 1))
        query.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    rw [← hqstore]; exact hprev
  have hcRootOld : get_current_store_epoch cfg
      (E.store cfg ext obs (n + 1)) >
        get_block_epoch cfg (E.store cfg ext obs (n + 1))
          query.current_epoch_observed_justified_checkpoint.root := by
    rw [← hprev']
    exact Nat.lt_succ_self _
  rcases hbank with hanchorArm | hne
  · -- Anchor arm: the banked root is the globally known trusted anchor root.
    have hanchorRoot : B.anchor.root = ablk.root := by
      rw [hanchor, hgen]; rfl
    have hcRootEq : query.current_epoch_observed_justified_checkpoint.root =
        B.anchor.root := by
      have hmem := hanchorArm
      rw [hgen] at hmem
      simp only [get_forkchoice_store, List.mem_singleton] at hmem
      rw [hmem, hanchorRoot]
    have hknownAll : ∀ (u : ValidatorIndex) (m : ℕ),
        query.current_epoch_observed_justified_checkpoint.root ∈
          (E.store cfg ext u m).block_roots := by
      intro u m
      have hknown0 : query.current_epoch_observed_justified_checkpoint.root ∈
          (E.store cfg ext u 0).block_roots := hanchorArm
      exact (E.store_storeLE cfg ext u (Nat.zero_le m)).1 hknown0
    have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
      cfg ext hT hanchor hboundary obs (n + 1)
    have haccepted : E.AcceptedRoot cfg ext
        query.current_epoch_observed_justified_checkpoint.root :=
      E.acceptedRoot_of_causal_known cfg ext
        (E.store_causal cfg ext obs (n + 1)) (hknownAll obs (n + 1))
    have hblockEpochLeAnchor : get_block_epoch cfg
        (E.store cfg ext obs (n + 1))
          query.current_epoch_observed_justified_checkpoint.root ≤
        B.anchor.epoch := by
      have hscaled : get_block_epoch cfg (E.store cfg ext obs (n + 1))
            query.current_epoch_observed_justified_checkpoint.root *
              cfg.slots_per_epoch ≤
          B.anchor.epoch * cfg.slots_per_epoch := by
        rw [hcRootEq]
        exact (start_slot_at_block_epoch_le cfg
          (E.store cfg ext obs (n + 1)) B.anchor.root).trans
            hreal.root_slot_le_boundary
      exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
    have hanchorLeGU :=
      Execution.ExactPrefixAcceptedFFGSemantics.anchor_epoch_le_gu
        (E := E) cfg ext B haccepted
    have hsourceEq : get_voting_source cfg (E.store cfg ext obs (n + 1))
        query.current_epoch_observed_justified_checkpoint.root =
        B.state.GU query.current_epoch_observed_justified_checkpoint.root := by
      rw [(E.store_causal cfg ext obs (n + 1)
        ).getVotingSource_eq_acceptedSelector cfg ext B (hknownAll obs (n + 1))]
      exact if_pos hcRootOld
    exact ⟨{
      validator := obs
      second := n + 1
      second_within := hHn1
      boundary_within := hboundaryH
      second_le_boundary := by rw [hboundarySecond]
      candidate_known := hknownAll obs (n + 1)
      seed := query.current_epoch_observed_justified_checkpoint.root
      seed_known_past := hknownAll obs (n + 1)
      seed_descends_candidate := is_ancestor_refl _ _
      seed_known_boundary := hknownAll obs _
      boundary_epoch := hboundaryEpoch
      source_recent := by
        rw [hboundarySecond, hsourceEq]
        calc
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) =
              get_block_epoch cfg (E.store cfg ext obs (n + 1))
                query.current_epoch_observed_justified_checkpoint.root + 1 :=
            hprev'.symm
          _ ≤ B.anchor.epoch + 1 := Nat.add_le_add_right hblockEpochLeAnchor 1
          _ ≤ (B.state.GU
              query.current_epoch_observed_justified_checkpoint.root).epoch + 1 :=
            Nat.add_le_add_right hanchorLeGU 1
          _ ≤ (B.state.GU
              query.current_epoch_observed_justified_checkpoint.root).epoch + 2 :=
            Nat.add_le_add_left (Nat.le_succ 1) _
      seed_disseminated := fun u _hu => hknownAll u _
    }⟩
  · -- Certified arm: the seed is the certificate's supplier.
    obtain ⟨hcert⟩ := hne
    have hsLe : hcert.second ≤ n + 1 := hcert.second_le
    have hsupplierKnownN1 : hcert.supplier ∈
        (E.store cfg ext obs (n + 1)).block_roots :=
      (E.store_storeLE cfg ext obs hsLe).1 hcert.supplier_known
    -- The gate's non-empty span puts the supplier strictly below the banking
    -- second's own slot, hence strictly below the boundary slot.
    have hcertPlain : Weak.has_broadcast_certificate cfg ext
        (E.store cfg ext obs hcert.second) hcert.balance_source hcert.supplier
        (get_block_slot (E.store cfg ext obs hcert.second) hcert.supplier)
        (get_current_slot cfg (E.store cfg ext obs hcert.second) - 1) = true := by
      have hc' := hcert.certificate
      exact hc'
    have hspan : get_block_slot (E.store cfg ext obs hcert.second)
        hcert.supplier ≤
        get_current_slot cfg (E.store cfg ext obs hcert.second) - 1 :=
      Weak.has_broadcast_certificate_span_nonempty cfg ext hcertPlain
    have hslotS : get_current_slot cfg (E.store cfg ext obs hcert.second) =
        E.slot_at cfg hcert.second :=
      E.store_current_slot cfg ext obs hcert.second
    have hsupplierSlotLtS :
        ((E.store cfg ext obs hcert.second).blocks hcert.supplier).slot <
          E.slot_at cfg hcert.second := by
      have hpos : 1 ≤ E.slot_at cfg hcert.second := by
        rw [← hslotS]; exact hcert.second_pos
      have hspan' : ((E.store cfg ext obs hcert.second).blocks
          hcert.supplier).slot ≤ E.slot_at cfg hcert.second - 1 := by
        simpa only [get_block_slot, hslotS] using hspan
      exact Nat.lt_of_le_of_lt hspan'
        (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos) Nat.zero_lt_one)
    have hsupplierAgree :
        (E.store cfg ext obs hcert.second).blocks hcert.supplier =
          (E.store cfg ext obs (n + 1)).blocks hcert.supplier :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext obs hcert.second)
        (E.blockProvenance cfg ext obs (n + 1))
        hcert.supplier_known hsupplierKnownN1
    have hsupplierSlotLtBoundary :
        ((E.store cfg ext obs (n + 1)).blocks hcert.supplier).slot <
          E.slot_at cfg (n + 1) := by
      rw [← hsupplierAgree]
      exact Nat.lt_of_lt_of_le hsupplierSlotLtS (E.slot_at_mono cfg hsLe)
    have hsupplierOld : get_current_store_epoch cfg
        (E.store cfg ext obs (n + 1)) >
          get_block_epoch cfg (E.store cfg ext obs (n + 1)) hcert.supplier := by
      have hlt := hsupplierSlotLtBoundary
      rw [hslotBoundary] at hlt
      simp only [get_block_epoch, compute_epoch_at_slot]
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch] using hlt
    -- The banked identity: what was banked is `GU supplier`.
    have hguEq : (E.store cfg ext obs hcert.second).unrealized_justifications
        hcert.supplier = B.state.GU hcert.supplier :=
      E.accepted_unrealized_justification_eq
        B.coherence.toAcceptedFFGSelectorCoherence obs hcert.second
        hcert.supplier_known
    have hcGU : query.current_epoch_observed_justified_checkpoint =
        B.state.GU hcert.supplier := hcert.banked_eq.trans hguEq
    have hsourceEq : get_voting_source cfg
        (E.store cfg ext obs (n + 1)) hcert.supplier =
        query.current_epoch_observed_justified_checkpoint := by
      rw [(E.store_causal cfg ext obs (n + 1)
        ).getVotingSource_eq_acceptedSelector cfg ext B hsupplierKnownN1]
      rw [if_pos hsupplierOld]
      exact hcGU.symm
    -- Boundary geometry of the AU checkpoint `GU supplier`.
    have hsupplierAccepted : E.AcceptedRoot cfg ext hcert.supplier :=
      E.acceptedRoot_of_causal_known cfg ext
        (E.store_causal cfg ext obs hcert.second) hcert.supplier_known
    have hAU : B.state.AU cfg ext hcert.supplier
        query.current_epoch_observed_justified_checkpoint := by
      rw [hcGU]
      exact B.state.gu_AU cfg ext hsupplierAccepted
    have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
        (E.store cfg ext obs hcert.second) hcert.supplier :=
      ⟨hcert.supplier_known,
        ⟨(E.store cfg ext obs hcert.second).blocks hcert.supplier,
          E.acceptedBlockAt_of_causal_known cfg ext
            (E.store_causal cfg ext obs hcert.second) hcert.supplier_known⟩⟩
    obtain ⟨hcarrierAU⟩ : AcceptedSelectorAUEvidence (cfg := cfg) (ext := ext)
        B.state (E.store cfg ext obs hcert.second)
        query.current_epoch_observed_justified_checkpoint :=
      AcceptedSelectorAUEvidence.of_AU hcarrier hAU
    have hrealS := Execution.AcceptedSelectorAUCarrier.resetCheckpointRealizedAt
      (E := E) cfg ext B hT hanchor hboundary hcarrierAU
    have hrealN1 := hrealS.mono_of_trajectory cfg ext E hT hsLe
    have hcBlockEpochLe : get_block_epoch cfg (E.store cfg ext obs (n + 1))
        query.current_epoch_observed_justified_checkpoint.root ≤
        query.current_epoch_observed_justified_checkpoint.epoch := by
      have hscaled : get_block_epoch cfg (E.store cfg ext obs (n + 1))
            query.current_epoch_observed_justified_checkpoint.root *
              cfg.slots_per_epoch ≤
          query.current_epoch_observed_justified_checkpoint.epoch *
            cfg.slots_per_epoch :=
        (start_slot_at_block_epoch_le cfg (E.store cfg ext obs (n + 1))
          query.current_epoch_observed_justified_checkpoint.root).trans
            hrealN1.root_slot_le_boundary
      exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
    have hcRecent : get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) ≤
        query.current_epoch_observed_justified_checkpoint.epoch + 2 := by
      calc
        get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) =
            get_block_epoch cfg (E.store cfg ext obs (n + 1))
              query.current_epoch_observed_justified_checkpoint.root + 1 :=
          hprev'.symm
        _ ≤ query.current_epoch_observed_justified_checkpoint.epoch + 1 :=
          Nat.add_le_add_right hcBlockEpochLe 1
        _ ≤ query.current_epoch_observed_justified_checkpoint.epoch + 2 :=
          Nat.add_le_add_left (Nat.le_succ 1) _
    -- Chain-intrinsic ancestry of the banked root below the supplier.
    obtain ⟨_hbankedKnown, hbelow⟩ :=
      Weak.blockUnrealizedJustification_known_and_below cfg ext B hT hanchor
        hboundary obs hcert.second hcert.supplier hcert.supplier_known
    rw [← hcert.banked_eq] at hbelow
    -- Dissemination of the supplier at the boundary.
    have hdiss : ∀ w ∈ E.honest,
        hcert.supplier ∈ (E.store cfg ext w (n + 1)).block_roots := by
      intro w hw
      exact (Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer
        cfg ext hA B hT hanchor hboundary hsync hji hA.genesis
        hcoh.committees_agree hcert hw hHn1
        (E.slot_at_mono cfg hsLe)).1
    exact ⟨{
      validator := obs
      second := hcert.second
      second_within := hcert.second_within
      boundary_within := hboundaryH
      second_le_boundary := by rw [hboundarySecond]; exact hsLe
      candidate_known := hcert.banked_known
      seed := hcert.supplier
      seed_known_past := hcert.supplier_known
      seed_descends_candidate := hbelow
      seed_known_boundary := by
        rw [hboundarySecond]; exact hsupplierKnownN1
      boundary_epoch := hboundaryEpoch
      source_recent := by
        rw [hboundarySecond, hsourceEq]
        exact hcRecent
      seed_disseminated := by
        intro w hw
        rw [hboundarySecond]
        exact hdiss w hw
    }⟩

/-- The actual-call wrapper: at one weak epoch-start call whose evaluator
trace took the observed-restart arm, the banked candidate has its Lemma-22
boundary witness. `hbank` is discharged here, not assumed — along the weak
trajectory by `Weak.weakFcr_certifiedBankedJustification`, and across this
call by one `Weak.certifiedBankedJustification_update`. Weak twin of
`Execution.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource`. -/
theorem ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (h : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace) :
    Nonempty (Weak.AcceptedLemma22EpochStartCandidateSourceAt cfg ext E B
      (get_current_store_epoch cfg (E.store cfg ext obs (n + 1)))
      (E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint.root) := by
  have hA := Weak.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hseat : Weak.CertifiedBankedJustification cfg ext E obs n
      { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) } :=
    (Weak.weakFcr_certifiedBankedJustification cfg ext hA B hT hanchor hboundary
      obs n hHn).transport cfg ext (Nat.le_refl n) rfl
  have hbank : Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
    rw [Execution.weakFcrStep]
    exact Weak.certifiedBankedJustification_update cfg ext hA B hT hanchor
      hboundary hHn1 hcall (fcr_store :=
        { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) })
      rfl hseat
  exact Weak.bankedEpochStartCandidateSource_of_certifiedBank cfg ext B hT hsync
    hstatic hbyz hdomain hji hanchor hboundary hcoh hHn1 hcall
    (E.weakFcrStep_store cfg ext obs n) hbank h.epoch_start
    h.observed_previous_epoch


/-! ## The strict-advance origin (Lemma 13 at the observer) -/

/-- Weak twin of `Execution.StrictSelectorAdvanceAt.mechanicalFacts`: enrich
the strict arm of the weak recurrence with the query-local mechanical facts.
`hv` is replaced by `hcoh` throughout, via
`Weak.strictSelectedResultMechanicalFacts` (`WeakSelectedTrace.lean`). -/
theorem StrictSelectorAdvanceAt.mechanicalFacts
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    {trace : Weak.GetLatestConfirmedTrace cfg ext query}
    (hquery : query.store = E.store cfg ext obs q)
    (hinput : trace.afterObserved ∈ query.store.block_roots)
    (h : Weak.StrictSelectorAdvanceAt cfg ext query trace) :
    Weak.StrictSelectedResultMechanicalFacts cfg ext query
      trace.afterObserved trace.result := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hA.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        rw [hquery]
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenShort
            obs q trace.afterObserved (by simpa only [hquery] using hinput))
  have hinputEpoch : get_block_epoch cfg query.store
          trace.afterObserved = get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store trace.afterObserved + 1 =
        get_current_store_epoch cfg query.store := by
    have hrecent := h.input_recent
    rcases Nat.eq_or_lt_of_le hinputEpochUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm (Nat.succ_le_iff.mpr hlt) hrecent)
  have hstrictFind : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact h.result_ne_input (h.result_eq.trans hfixed)
  have hfacts := Weak.strictSelectedResultMechanicalFacts cfg ext hA hcoh hqH
    query hquery trace.afterObserved hinput hinputEpoch hstrictFind
  simpa only [← h.result_eq] using hfacts

/-- Weak twin of `Execution.StrictSelectedResultMechanicalFacts.
currentCandidateSourceOrigin`: a strict current-epoch weak selector advance
installs a fresh candidate-specific history origin at the observer.

The Lemma-13 seed is the query fork-choice head, and stage S5's combined
lemma hands back the `has_head_broadcast_certificate` flag alongside the `GU`
bound, so the record's `seed_disseminated` field is
`Weak.headSeed_known_at_all_honest_endpoints_at_observer` applied to that
flag. `hslotPos` is the only genuinely new premise (the certificate's span
ends at `get_current_slot - 1`, so translating its gate into the record's
`E.slot_at cfg q ≤ E.slot_at cfg m` form needs the query slot to be past
slot 0); at every actual call it is immediate from `E.IsFCRCallAt`. -/
theorem StrictSelectedResultMechanicalFacts.currentCandidateSourceOrigin
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (hslotPos : 1 ≤ E.slot_at cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext obs q)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : input ∈ query.store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true) :
    Nonempty (Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B obs q
      result) := by
  obtain ⟨hdesc, hgu, hcert⟩ :=
    h.currentHeadLemma13SourceSeedCertified_of_notStart cfg ext B
      (by rw [hquery]; exact E.store_causal cfg ext obs q)
      hparent hwalk hhead hinput hout hstrict hcurrent hnotStart
  have hclock : get_current_slot cfg query.store = E.slot_at cfg q := by
    rw [hquery]; exact E.store_current_slot cfg ext obs q
  exact ⟨{
    originSecond := q
    origin_le := Nat.le_refl q
    origin_within := hqH
    candidate_known := by simpa only [hquery] using h.result_known
    candidate_current := by simpa only [hquery] using hcurrent
    seed := Weak.get_certified_head cfg ext (E.store cfg ext obs q)
      (get_current_balance_source query)
    seed_known := by
      simpa only [hquery] using Weak.get_certified_head_known cfg ext _ _ hhead
    seed_descends_candidate := by simpa only [hquery] using hdesc
    gu_recent := by simpa only [hquery] using hgu
    seed_disseminated := by
      intro w hw m hmH hgate
      have hgate' : (get_current_slot cfg query.store - 1) + 1 ≤
          E.slot_at cfg m := by
        rw [hclock, Nat.sub_add_cancel hslotPos]
        exact hgate
      have hknown := Weak.headSeed_known_at_all_honest_endpoints_at_observer
        cfg ext hA hsync hji hqH hcoh hquery hcert hw hmH hgate'
      simpa only [hquery] using hknown
  }⟩

/-- Weak twin of `Execution.previousConfirmed_current_of_boundary_recent`,
over `E.weakFcrStep` / `E.weakConfirmed`. Honesty-free in both developments;
only the bookkeeping function changes. -/
theorem previousConfirmed_current_of_boundary_recent
    {E : Execution Root} (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    (hknownN : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hrecentQ : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
          (E.weakConfirmed cfg ext v n) + 1 ≥
        get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :
    get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hknownN1 : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.weakConfirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.weakConfirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  have hblockEpochEq : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) =
      get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakConfirmed cfg ext v n) := by
    rw [E.weakFcrStep_store]
    simp only [get_block_epoch, hblockAgree]
  have hblockUpper : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
            v n (E.weakConfirmed cfg ext v n) hknownN)
  have hepochSucc := E.actualCall_currentEpoch_succ_of_start
    cfg ext hT hcall hstart
  have hlowerPlus : get_current_store_epoch cfg (E.store cfg ext v n) + 1 ≤
      get_block_epoch cfg (E.store cfg ext v n)
          (E.weakConfirmed cfg ext v n) + 1 := by
    calc
      get_current_store_epoch cfg (E.store cfg ext v n) + 1 =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
        hepochSucc
      _ ≤ get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
            (E.weakConfirmed cfg ext v n) + 1 := by
        simpa only [E.weakFcrStep_store] using hrecentQ
      _ = get_block_epoch cfg (E.store cfg ext v n)
            (E.weakConfirmed cfg ext v n) + 1 := by rw [← hblockEpochEq]
  exact Nat.le_antisymm hblockUpper
    (Nat.le_of_add_le_add_right hlowerPlus)


/-! ## The candidate-indexed confirmed-history invariant at the observer -/

/-- Weak twin of `Execution.AcceptedConfirmedSourceHistoryAt`, over
`E.weakConfirmed`. The `recent_epochStartSource` field's conclusion is the
**strong** `Execution.AcceptedLemma24EpochStartSourceAt` (it mentions only the
receiving honest endpoint's store, so it is honesty-free as stated); only the
retained `current_origin` payload is the weak record. -/
structure AcceptedConfirmedSourceHistoryAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (n : Nat) : Prop where
  confirmed_known : E.weakConfirmed cfg ext v n ∈
    (E.store cfg ext v n).block_roots
  recent_epochStartSource :
    get_block_epoch cfg (E.store cfg ext v n)
          (E.weakConfirmed cfg ext v n) + 1 ≥
        get_current_store_epoch cfg (E.store cfg ext v n) →
      ∀ w ∈ E.honest,
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v n)) w)
  current_origin :
    get_block_epoch cfg (E.store cfg ext v n)
          (E.weakConfirmed cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v n) →
      Nonempty (Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B v n
        (E.weakConfirmed cfg ext v n))

/-- Initialization, checkpoint-sync safe exactly as in the strong
development: the weak trajectory's seed is the same genesis initializer. -/
theorem acceptedConfirmedSourceHistoryAt_zero
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (hH0 : E.WithinHorizon cfg 0) :
    Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B v 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hconfirmedAnchor : E.weakConfirmed cfg ext v 0 = B.anchor.root := by
    rw [E.weakConfirmed_zero, hanchor]
    change E.genesis_store.finalized_checkpoint.root =
      E.genesis_store.justified_checkpoint.root
    rw [hgen]
    rfl
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary v 0
  have hblockEpochLeAnchor : get_block_epoch cfg
      (E.store cfg ext v 0) B.anchor.root ≤ B.anchor.epoch := by
    have hscaled : get_block_epoch cfg
          (E.store cfg ext v 0) B.anchor.root * cfg.slots_per_epoch ≤
        B.anchor.epoch * cfg.slots_per_epoch :=
      (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v 0) B.anchor.root).trans
          hreal.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  exact {
    confirmed_known := by simpa only [hconfirmedAnchor] using hreal.root_known
    recent_epochStartSource := by
      intro hrecent w _hw
      have hnear : get_current_store_epoch cfg (E.store cfg ext v 0) ≤
          B.anchor.epoch + 2 := by
        rw [← hconfirmedAnchor] at hblockEpochLeAnchor
        exact hrecent.trans
          ((Nat.add_le_add_right hblockEpochLeAnchor 1).trans
            (Nat.add_le_add_left (Nat.le_succ 1) B.anchor.epoch))
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary hnear w
    current_origin := by
      intro hcurrent
      rw [hconfirmedAnchor] at hcurrent ⊢
      exact Weak.acceptedCurrentCandidateSourceOriginAt_anchor
        cfg ext B hT hanchor hboundary hH0 hcurrent
  }

/-- Weak twin of `AcceptedConfirmedSourceHistoryAt.succ_of_noCall`: between
weak FCR calls everything is carried definitionally. -/
theorem AcceptedConfirmedSourceHistoryAt.succ_of_noCall
    {E : Execution Root} {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hnoCall : ¬ E.IsFCRCallAt cfg ext v n)
    (h : Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B v n) :
    Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B v (n + 1) := by
  have hknownN1 : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 h.confirmed_known
  have hconfirmedEq : E.weakConfirmed cfg ext v (n + 1) =
      E.weakConfirmed cfg ext v n :=
    E.weakConfirmed_succ_of_no_advance cfg ext v n hnoCall
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.weakConfirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.weakConfirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1))
      h.confirmed_known hknownN1
  have hslotMono : get_current_slot cfg (E.store cfg ext v n) ≤
      get_current_slot cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.store_current_slot] using
      E.slot_at_mono cfg (Nat.le_succ n)
  have hslotEq : get_current_slot cfg (E.store cfg ext v n) =
      get_current_slot cfg (E.store cfg ext v (n + 1)) :=
    Nat.le_antisymm hslotMono (Nat.le_of_not_gt hnoCall)
  have hcurrentEpochEq : get_current_store_epoch cfg
      (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simp only [get_current_store_epoch, hslotEq]
  have hblockEpochEq : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) =
      get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.weakConfirmed cfg ext v n) := by
    simp only [get_block_epoch, hblockAgree]
  exact {
    confirmed_known := by simpa only [hconfirmedEq] using hknownN1
    recent_epochStartSource := by
      intro hrecent w hw
      have hrecentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.weakConfirmed cfg ext v n) + 1 ≥
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochEq, hcurrentEpochEq, ← hconfirmedEq]
        exact hrecent
      have hsource := h.recent_epochStartSource hrecentN w hw
      simpa only [hcurrentEpochEq] using hsource
    current_origin := by
      intro hcurrent
      have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.weakConfirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochEq, hcurrentEpochEq, ← hconfirmedEq]
        exact hcurrent
      obtain ⟨horigin⟩ := h.current_origin hcurrentN
      exact ⟨by
        simpa only [hconfirmedEq] using
          (horigin.mono_upper cfg ext (Nat.le_succ n))⟩
  }


set_option maxRecDepth 4000 in
/-- Knownness half of one actual weak call. Weak twin of
`AcceptedConfirmedSourceHistoryAt.confirmedKnown_succ_of_call`: the strong
`store_domainK_of_selectedMarginDomain … hv` / `head_root_known_of_
selectedMarginDomain … hv` pair becomes `Execution.observerStoreDomainK` /
`Execution.head_root_known_at_observer`, and the observed-reset input's
knownness is the landed `Weak.weakFcrStep_observed_known` (rule delta 5's
`banked_known`, discharged for the whole weak trajectory) in place of
`Execution.actualObservedRestartInputAt`. -/
theorem AcceptedConfirmedSourceHistoryAt.confirmedKnown_succ_of_call
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (h : Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs n) :
    E.weakConfirmed cfg ext obs (n + 1) ∈
      (E.store cfg ext obs (n + 1)).block_roots := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hrec := E.weakActualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have hknownN1 : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 h.confirmed_known
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.weakFcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.weakFcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have observedKnown :
      query.current_epoch_observed_justified_checkpoint.root ∈
        query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
  cases hrec.branch with
  | carriedUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext, hinput.input_eq]
      simpa only [query, E.weakFcrStep_confirmed_root] using hknownN1
  | finalizedResetUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext, hinput.input_eq]
      simpa only [query, E.weakFcrStep_store] using hfinalized.root_known
  | observedResetUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext, hinput.input_eq]
      simpa only [query, E.weakFcrStep_store] using observedKnown
  | strictSelected horigin hselector =>
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        cases horigin with
        | carried hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.weakFcrStep_confirmed_root,
              E.weakFcrStep_store] using hknownN1
        | finalizedReset hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.weakFcrStep_store] using hfinalized.root_known
        | observedReset hinput =>
            rw [hinput.input_eq]
            exact observedKnown
      have hgeometry := hselector.geometry cfg ext hparent hwalk hhead hinputKnown
      rw [hconfirmedOut]
      simpa only [query, E.weakFcrStep_store] using hgeometry.result_known

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exhaustive operational branch fold needs a larger elaboration budget.
/-- Current-origin half of one actual weak call. Weak twin of
`AcceptedConfirmedSourceHistoryAt.currentOrigin_succ_of_call`. Branch for
branch: carried roots reuse the induction origin, finalized-current roots
reduce to the trusted anchor through the causal lag law, observed resets are
previous-epoch (impossible while current), and a strict current result
installs a fresh Lemma-13 origin via the weak mechanical-facts bracket. -/
theorem AcceptedConfirmedSourceHistoryAt.currentOrigin_succ_of_call
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (h : Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext obs (n + 1))
          (E.weakConfirmed cfg ext obs (n + 1)) =
        get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) :
    Nonempty (Weak.AcceptedCurrentCandidateSourceOriginAt cfg ext E B obs
      (n + 1) (E.weakConfirmed cfg ext obs (n + 1))) := by
  have hA := Weak.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hrec := E.weakActualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have htraceCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store := by
    rw [hconfirmedOut] at hcurrent
    simpa only [query, trace, E.weakFcrStep_store] using hcurrent
  have hknownN1 : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 h.confirmed_known
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.weakFcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.weakFcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    unfold Execution.IsFCRCallAt at hcall
    simpa only [E.store_current_slot] using hcall
  have hslotPos : 1 ≤ E.slot_at cfg (n + 1) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hslotAdvance
  cases hrec.branch with
  | carriedUnchanged hinput hselector =>
      have hresultPrev : trace.result = E.weakConfirmed cfg ext obs n := by
        calc
          trace.result = trace.afterObserved :=
            hselector.result_eq_input cfg ext
          _ = query.confirmed_root := hinput.input_eq
          _ = E.weakConfirmed cfg ext obs n := by
            simpa only [query] using E.weakFcrStep_confirmed_root cfg ext obs n
      have hblockAgree :
          (E.store cfg ext obs n).blocks (E.weakConfirmed cfg ext obs n) =
            (E.store cfg ext obs (n + 1)).blocks
              (E.weakConfirmed cfg ext obs n) :=
        hT.wellFormed.blocks_agree
          (E.blockProvenance cfg ext obs n)
          (E.blockProvenance cfg ext obs (n + 1))
          h.confirmed_known hknownN1
      obtain ⟨ast, ablk, hgen, hslot, _hgenParent⟩ := hT.genesis_structure
      have hgenShort : ∃ (ast : BeaconState Root)
          (ablk : SignedBeaconBlock Root),
          E.genesis_store = get_forkchoice_store cfg ast ablk ∧
            ast.slot = ablk.message.slot :=
        ⟨ast, ablk, hgen, hslot⟩
      have hblockUpperN : get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) ≤
          get_current_store_epoch cfg (E.store cfg ext obs n) := by
        simp only [get_block_epoch, get_current_store_epoch,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right
          (by
            simpa only [E.store_current_slot] using
              E.store_blocks_slot_le_current cfg ext hT.whole_seconds
                hgenShort obs n (E.weakConfirmed cfg ext obs n)
                h.confirmed_known)
      have hclockMono : get_current_store_epoch cfg (E.store cfg ext obs n) ≤
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
        simp only [get_current_store_epoch, E.store_current_slot,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
      have hblockEpochEq : get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_block_epoch cfg (E.store cfg ext obs (n + 1))
            (E.weakConfirmed cfg ext obs n) := by
        simp only [get_block_epoch, hblockAgree]
      have hclockEq : get_current_store_epoch cfg (E.store cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
        apply Nat.le_antisymm hclockMono
        have hqueryReverse : get_current_store_epoch cfg query.store ≤
            get_block_epoch cfg query.store
              (E.weakConfirmed cfg ext obs n) := by
          rw [← hresultPrev]
          exact htraceCurrent.symm.le
        calc
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) ≤
              get_block_epoch cfg (E.store cfg ext obs (n + 1))
                (E.weakConfirmed cfg ext obs n) := by
            simpa only [query, E.weakFcrStep_store] using hqueryReverse
          _ = get_block_epoch cfg (E.store cfg ext obs n)
                (E.weakConfirmed cfg ext obs n) := hblockEpochEq.symm
          _ ≤ get_current_store_epoch cfg (E.store cfg ext obs n) :=
            hblockUpperN
      have hcurrentN : get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) := by
        rw [hblockEpochEq, hclockEq, ← hresultPrev]
        simpa only [query, E.weakFcrStep_store] using htraceCurrent
      obtain ⟨horigin⟩ := h.current_origin hcurrentN
      exact ⟨by
        simpa only [hconfirmedOut, hresultPrev] using
          (horigin.mono_upper cfg ext (Nat.le_succ n))⟩
  | finalizedResetUnchanged hinput hselector =>
      have hresultFinalized : trace.result =
          query.store.finalized_checkpoint.root :=
        (hselector.result_eq_input cfg ext).trans hinput.input_eq
      have hfinalizedCurrent : get_block_epoch cfg query.store
            query.store.finalized_checkpoint.root =
          get_current_store_epoch cfg query.store := by
        simpa only [hresultFinalized] using htraceCurrent
      have hfieldAnchor := E.finalizedCheckpoint_eq_anchor_of_root_current
        cfg ext hLag
          (by simpa only [query, E.weakFcrStep_store] using
            E.store_causal cfg ext obs (n + 1))
          (by simpa only [query, E.weakFcrStep_store] using hfinalized)
          hfinalizedCurrent
      have hresultAnchor : trace.result = B.anchor.root := by
        rw [hresultFinalized, hfieldAnchor]
      have hanchorCurrent : get_block_epoch cfg
            (E.store cfg ext obs (n + 1)) B.anchor.root =
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
        simpa only [query, E.weakFcrStep_store, hresultAnchor]
          using htraceCurrent
      obtain ⟨horigin⟩ := Weak.acceptedCurrentCandidateSourceOriginAt_anchor
        cfg ext B hT hanchor hboundary hHn1 hanchorCurrent
      exact ⟨by simpa only [hconfirmedOut, hresultAnchor] using horigin⟩
  | observedResetUnchanged hinput hselector =>
      have hresultObserved : trace.result =
          query.current_epoch_observed_justified_checkpoint.root :=
        (hselector.result_eq_input cfg ext).trans hinput.input_eq
      have hbad : get_block_epoch cfg query.store
              query.current_epoch_observed_justified_checkpoint.root + 1 =
            get_block_epoch cfg query.store
              query.current_epoch_observed_justified_checkpoint.root := by
        calc
          _ = get_current_store_epoch cfg query.store :=
            hinput.observed_previous_epoch
          _ = get_block_epoch cfg query.store
                query.current_epoch_observed_justified_checkpoint.root := by
            rw [← hresultObserved]
            exact htraceCurrent.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
  | strictSelected horigin hselector =>
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        cases horigin with
        | carried hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.weakFcrStep_confirmed_root,
              E.weakFcrStep_store] using hknownN1
        | finalizedReset hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.weakFcrStep_store] using hfinalized.root_known
        | observedReset hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.weakFcrStep_store] using
              Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary
                obs n
      have hqstore : query.store = E.store cfg ext obs (n + 1) := by
        simpa only [query] using E.weakFcrStep_store cfg ext obs n
      have hfacts := Weak.StrictSelectorAdvanceAt.mechanicalFacts cfg ext hA
        hcoh hHn1 hqstore hinputKnown hselector
      have hpast :=
        Weak.StrictSelectedResultMechanicalFacts.confirmedPastDescendantSlotWitness_at_observer
          cfg ext hA hcoh.validity (hcoh.committees_agree (n + 1) hHn1) hHn1 hqstore hfacts
      have hclock : get_current_slot cfg query.store = E.slot_at cfg (n + 1) := by
        rw [hqstore]; exact E.store_current_slot cfg ext obs (n + 1)
      have hnotStart :=
        Weak.StrictSelectedResultMechanicalFacts.not_epochStart_of_current
          cfg ext hclock hparent hwalk hfacts hpast htraceCurrent
      have hnew :=
        Weak.StrictSelectedResultMechanicalFacts.currentCandidateSourceOrigin
          cfg ext hA B hsync hji hcoh hHn1 hslotPos hqstore hparent hwalk hhead
          hinputKnown hselector.result_eq.symm hselector.result_ne_input hfacts
          htraceCurrent hnotStart
      simpa only [hconfirmedOut] using hnew


set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exhaustive operational branch fold needs a larger elaboration budget.
/-- Recent-source half of one actual weak call. Weak twin of
`AcceptedConfirmedSourceHistoryAt.recentSource_succ_of_call`.

Away from an epoch boundary the exact weak evaluator recurrence reduces a
recent result to the previous confirmed root or the realized finalized
checkpoint, exactly as in the strong development (both arms are honesty-free
there). At a boundary, carried roots consume the retained current-origin
field through the weak Lemma 22, **observed resets use the banked
certificate** (`Weak.ObservedResetCandidateInputAt.
acceptedLemma22EpochStartCandidateSource`, this file's site-8 step) in place
of the strong accepted installation witness, and finalized resets stay
confined to the trusted-anchor base region by the causal lag law. -/
theorem AcceptedConfirmedSourceHistoryAt.recentSource_succ_of_call
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (h : Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs n)
    (hrecent : get_block_epoch cfg (E.store cfg ext obs (n + 1))
          (E.weakConfirmed cfg ext obs (n + 1)) + 1 ≥
        get_current_store_epoch cfg (E.store cfg ext obs (n + 1)))
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
      (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) w) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hrec := E.weakActualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have htraceRecent : get_block_epoch cfg query.store trace.result + 1 ≥
      get_current_store_epoch cfg query.store := by
    rw [hconfirmedOut] at hrecent
    simpa only [query, trace, E.weakFcrStep_store] using hrecent
  have hknownN1 : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 h.confirmed_known
  have hblockAgree :
      (E.store cfg ext obs n).blocks (E.weakConfirmed cfg ext obs n) =
        (E.store cfg ext obs (n + 1)).blocks
          (E.weakConfirmed cfg ext obs n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs n)
      (E.blockProvenance cfg ext obs (n + 1))
      h.confirmed_known hknownN1
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)
  by_cases hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs (n + 1))) = true
  · have hboundarySecond := Weak.actualCall_epochStart_boundarySecond
      cfg ext hT hsync hstatic hbyz hdomain hHn1 hcall hstart
    have hepochSucc := E.actualCall_currentEpoch_succ_of_start
      cfg ext hT hcall hstart
    have carriedBoundarySource
        (hrecentPrevQ : get_block_epoch cfg query.store
              (E.weakConfirmed cfg ext obs n) + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) w) := by
      have hpreviousCurrent := Weak.previousConfirmed_current_of_boundary_recent
        cfg ext hT hcall hstart h.confirmed_known
          (by simpa only [query] using hrecentPrevQ)
      obtain ⟨horigin⟩ := h.current_origin hpreviousCurrent
      have hprevious : get_block_epoch cfg
            (E.store cfg ext obs (n + 1)) (E.weakConfirmed cfg ext obs n) + 1 =
          get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
        calc
          get_block_epoch cfg (E.store cfg ext obs (n + 1))
                (E.weakConfirmed cfg ext obs n) + 1 =
              get_block_epoch cfg (E.store cfg ext obs n)
                (E.weakConfirmed cfg ext obs n) + 1 := by
            simp only [get_block_epoch, hblockAgree]
          _ = get_current_store_epoch cfg (E.store cfg ext obs n) + 1 := by
            rw [hpreviousCurrent]
          _ = get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) :=
            hepochSucc
      obtain ⟨hlemma22⟩ := horigin.toLemma22AtNextBoundary cfg ext B hT
        hHn1 hcall hboundarySecond rfl hknownN1 hprevious
      exact hlemma22.lemma24 cfg ext B hT w hw
    have finalizedBoundarySource
        (hrecentFinalized : get_block_epoch cfg query.store
              query.store.finalized_checkpoint.root + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) w) := by
      have hnear := E.finalizedRecent_epoch_le_anchor_add_two cfg ext hLag
        (by simpa only [query, E.weakFcrStep_store] using
          E.store_causal cfg ext obs (n + 1))
        (by simpa only [query, E.weakFcrStep_store] using hfinalized)
        hrecentFinalized
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary
          (by simpa only [query, E.weakFcrStep_store] using hnear) w
    cases hrec.branch with
    | carriedUnchanged hinput _hselector =>
        exact carriedBoundarySource
          (by simpa only [query, E.weakFcrStep_confirmed_root] using
            hinput.confirmed_recent cfg ext)
    | finalizedResetUnchanged hinput hselector =>
        apply finalizedBoundarySource
        have hresult : trace.result = query.store.finalized_checkpoint.root :=
          (hselector.result_eq_input cfg ext).trans hinput.input_eq
        simpa only [hresult] using htraceRecent
    | observedResetUnchanged hinput _hselector =>
        obtain ⟨hlemma22⟩ :=
          Weak.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
            cfg ext B hT hsync hstatic hbyz hdomain hji hanchor hboundary hcoh
              hHn1 hcall hinput
        exact hlemma22.lemma24 cfg ext B hT w hw
    | strictSelected horigin hselector =>
        cases horigin with
        | carried hinput =>
            apply carriedBoundarySource
            simpa only [query, E.weakFcrStep_confirmed_root, hinput.input_eq]
              using hselector.input_recent
        | finalizedReset hinput =>
            apply finalizedBoundarySource
            simpa only [hinput.input_eq] using hselector.input_recent
        | observedReset hinput =>
            obtain ⟨hlemma22⟩ :=
              Weak.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
                cfg ext B hT hsync hstatic hbyz hdomain hji hanchor hboundary
                  hcoh hHn1 hcall hinput
            exact hlemma22.lemma24 cfg ext B hT w hw
  · have hepochEq := E.actualCall_currentEpoch_eq_of_notStart
      cfg ext hT hcall hstart
    have previousMidSource
        (hprevious : get_block_epoch cfg query.store
              (E.weakConfirmed cfg ext obs n) + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) w) := by
      have hprevious' : get_current_store_epoch cfg
            (E.store cfg ext obs (n + 1)) ≤
          get_block_epoch cfg query.store
            (E.weakConfirmed cfg ext obs n) + 1 := by
        simpa only [query, E.weakFcrStep_store] using hprevious
      have hrecentN : get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) + 1 ≥
          get_current_store_epoch cfg (E.store cfg ext obs n) := by
        calc
          get_current_store_epoch cfg (E.store cfg ext obs n) =
              get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) :=
            hepochEq
          _ ≤ get_block_epoch cfg query.store
                (E.weakConfirmed cfg ext obs n) + 1 := hprevious'
          _ = get_block_epoch cfg (E.store cfg ext obs n)
                (E.weakConfirmed cfg ext obs n) + 1 := by
            simp only [query, E.weakFcrStep_store, get_block_epoch, hblockAgree]
      have hsource := h.recent_epochStartSource hrecentN w hw
      simpa only [hepochEq] using hsource
    have finalizedMidSource
        (hfinalizedRecent : get_block_epoch cfg query.store
              query.store.finalized_checkpoint.root + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext obs (n + 1))) w) := by
      have hnear := E.finalizedRecent_epoch_le_anchor_add_two cfg ext hLag
        (by simpa only [query, E.weakFcrStep_store] using
          E.store_causal cfg ext obs (n + 1))
        (by simpa only [query, E.weakFcrStep_store] using hfinalized)
        hfinalizedRecent
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary
          (by simpa only [query, E.weakFcrStep_store] using hnear) w
    cases hrec.branch with
    | carriedUnchanged hinput _hselector =>
        apply previousMidSource
        simpa only [query, E.weakFcrStep_confirmed_root] using
          hinput.confirmed_recent cfg ext
    | finalizedResetUnchanged hinput hselector =>
        apply finalizedMidSource
        have hresult : trace.result = query.store.finalized_checkpoint.root :=
          (hselector.result_eq_input cfg ext).trans hinput.input_eq
        simpa only [hresult] using htraceRecent
    | observedResetUnchanged hinput _hselector =>
        exfalso
        apply hstart
        simpa only [query, E.weakFcrStep_store] using hinput.epoch_start
    | strictSelected horigin hselector =>
        cases horigin with
        | carried hinput =>
            apply previousMidSource
            simpa only [query, E.weakFcrStep_confirmed_root, hinput.input_eq]
              using hselector.input_recent
        | finalizedReset hinput =>
            apply finalizedMidSource
            simpa only [hinput.input_eq] using hselector.input_recent
        | observedReset hinput =>
            exfalso
            apply hstart
            simpa only [query, E.weakFcrStep_store] using hinput.epoch_start


/-- The complete one-call transformer for the weak candidate-indexed source
history invariant. -/
theorem AcceptedConfirmedSourceHistoryAt.succ_of_call
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (h : Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs n) :
    Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs (n + 1) := {
  confirmed_known := h.confirmedKnown_succ_of_call cfg ext B hT hanchor
    hboundary hcoh hHn1 hcall
  recent_epochStartSource := fun hrecent w hw =>
    h.recentSource_succ_of_call cfg ext B hT hsync hstatic hbyz hdomain hji
      hanchor hboundary hLag hcoh hHn1 hcall hrecent w hw
  current_origin := fun hcurrent =>
    h.currentOrigin_succ_of_call cfg ext B hT hsync hstatic hbyz hdomain hji
      hanchor hboundary hLag hcoh hHn1 hcall hcurrent
}

/-- **Weak candidate-source history for every in-horizon second at a
possibly-Byzantine observer.** Weak twin of
`Execution.acceptedConfirmedSourceHistoryAt`: same induction, same single
paper-facing timing contract (`AcceptedRealizedFinalizationDelay`), the
observer's honesty binder `hv` replaced throughout by `hcoh :
E.ObserverCoherence cfg ext obs`.

The strong premise `hspe : 1 < cfg.slots_per_epoch` is **not** carried: it was
needed only by the strong observed-reset arm's accepted *installation*
witness (`AcceptedUJCacheInstallationAt`), which rule delta 5's head-indexed
banking replaces with the banked certificate. -/
theorem acceptedConfirmedSourceHistoryAt
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) :
    ∀ n : Nat, E.WithinHorizon cfg n →
      Weak.AcceptedConfirmedSourceHistoryAt cfg ext E B obs n := by
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay
      cfg ext B hT hanchor hDelay
  intro n
  induction n with
  | zero =>
      intro hH0
      exact Weak.acceptedConfirmedSourceHistoryAt_zero cfg ext B hT hanchor
        hboundary obs hH0
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hn := ih hHn
      by_cases hcall : E.IsFCRCallAt cfg ext obs n
      · exact hn.succ_of_call cfg ext B hT hsync hstatic hbyz hdomain hji
          hanchor hboundary hLag hcoh hHn1 hcall
      · exact hn.succ_of_noCall cfg ext hT hcall

/-- **Callback-free paper-Lemma-24 export for one actual weak evaluator
call.** Weak twin of
`Execution.getLatestConfirmedTraceAt_current_epochStartSource`: the S7
dispatcher's entry point into this stage. -/
theorem getLatestConfirmedTraceAt_current_epochStartSource
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) w) := by
  have hhistory := Weak.acceptedConfirmedSourceHistoryAt cfg ext B hT hsync
    hstatic hbyz hdomain hji hanchor hboundary hDelay hcoh (n + 1) hHn1
  have hrec := E.weakActualCandidateHistoryRecurrence cfg ext hcall
  have hstoredCurrent : get_block_epoch cfg (E.store cfg ext obs (n + 1))
          (E.weakConfirmed cfg ext obs (n + 1)) =
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    rw [hrec.result_writeback]
    simpa only [E.weakFcrStep_store] using hcurrent
  have hstoredRecent : get_block_epoch cfg (E.store cfg ext obs (n + 1))
          (E.weakConfirmed cfg ext obs (n + 1)) + 1 ≥
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    rw [hstoredCurrent]
    exact Nat.le_succ _
  have hsource := hhistory.recent_epochStartSource hstoredRecent w hw
  simpa only [E.weakFcrStep_store] using hsource


/-! ## Source-history split: the S6 → S7 export -/

set_option maxRecDepth 4000 in
/-- Weak twin of `StrictSelectedResultMechanicalFacts.currentSame_source
HistoryOutcome_of_epochStartSource`. The outcome type
`Execution.AcceptedCurrentSameSourceHistoryOutcome` is reused verbatim: both
of its arms are indexed at the *honest past supporter*'s store, so neither
mentions the query node's honesty. The single honesty use in the strong proof
is `confirmed_honestPastHeadBelow`, replaced by stage S4's landed
`Execution.confirmed_honestPastHeadBelow_at_observer`; the past-head split
`directJustified_or_pathLocal` and the carrier constructor `of_pathLocal` are
already stated at the honest supporter and need no twin. -/
theorem StrictSelectedResultMechanicalFacts.currentSame_sourceHistoryOutcome_of_epochStartSource
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} {q : Nat}
    (hvalid : E.ObserverValidity cfg ext obs)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext obs q)
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hsource : ∀ w ∈ E.honest,
      Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
        (get_current_store_epoch cfg query.store) w)) :
    E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B obs q result := by
  obtain ⟨hpast⟩ := E.confirmed_honestPastHeadBelow_at_observer cfg ext hT
    hsync hstatic hbyz hdomain hvalid hcomm hqH hquery h.result_known h.parent_known
    h.confirmed
  have hpastEpoch : get_current_store_epoch cfg
      (E.store cfg ext hpast.validator hpast.second) =
      get_current_store_epoch cfg (E.store cfg ext obs q) := by
    have hblockAgree : query.store.blocks result =
        (E.store cfg ext hpast.validator hpast.second).blocks result := by
      rw [hquery]
      exact hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext obs q)
        (E.blockProvenance cfg ext hpast.validator hpast.second)
        (by simpa only [hquery] using h.result_known) hpast.candidate_known
    have hlower : get_current_store_epoch cfg (E.store cfg ext obs q) ≤
        get_current_store_epoch cfg
          (E.store cfg ext hpast.validator hpast.second) := by
      rw [← hquery, ← hcurrent]
      simp only [get_block_epoch, hblockAgree]
      exact ce_mono cfg
        (E.store_blocks_slot_le_current cfg ext hT.whole_seconds
          (by
            obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
            exact ⟨ast, ablk, hgen, hslot⟩)
          hpast.validator hpast.second result hpast.candidate_known)
    have hupper : get_current_store_epoch cfg
        (E.store cfg ext hpast.validator hpast.second) ≤
        get_current_store_epoch cfg (E.store cfg ext obs q) := by
      simp only [get_current_store_epoch, E.store_current_slot]
      exact ce_mono cfg hpast.strictly_past.le
    exact Nat.le_antisymm hupper hlower
  rcases hpast.directJustified_or_pathLocal cfg ext hT hdomain with
      hdirect | hpath
  · exact .justifiedFallback ⟨{
      past := hpast
      justified_descends_candidate := hdirect
    }⟩
  · obtain ⟨hlemma24⟩ := hsource hpast.validator hpast.validator_honest
    have hJRecentQuery : get_current_store_epoch cfg query.store ≤
        (E.store cfg ext hpast.validator hpast.second
          ).justified_checkpoint.epoch + 2 :=
      hlemma24.justified_recent cfg ext B hT hanchor hpast.second_within
        (by simpa only [hquery] using hpastEpoch)
    have hJRecent : get_current_store_epoch cfg (E.store cfg ext obs q) ≤
        (E.store cfg ext hpast.validator hpast.second
          ).justified_checkpoint.epoch + 2 := by
      simpa only [← hquery] using hJRecentQuery
    exact .recentCarrier
      (Execution.AcceptedRecentCandidateSourceCarrierAt.of_pathLocal cfg ext B
        hT hpast hpastEpoch hJRecent hpath)

set_option maxRecDepth 4000 in
/-- **Callback-free Lemma-26 export for a strict current result of the actual
weak evaluator at a possibly-Byzantine observer.** Weak twin of
`StrictSelectedResultMechanicalFacts.actualCurrentSame_sourceHistoryOutcome`
— the S7 dispatcher's `currentSame` entry point. Its only paper-facing timing
premise is the accepted realized-finalization delay, exactly as in the strong
development; `hspe : 1 < cfg.slots_per_epoch` is not needed (see
`Weak.acceptedConfirmedSourceHistoryAt`). -/
theorem StrictSelectedResultMechanicalFacts.actualCurrentSame_sourceHistoryOutcome
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {input : Root}
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) :
    E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B obs (n + 1)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
  apply h.currentSame_sourceHistoryOutcome_of_epochStartSource cfg ext B hT
    hsync hstatic hbyz hdomain hanchor hcoh.validity
    (hcoh.committees_agree (n + 1) hHn1)
    hHn1 (E.weakFcrStep_store cfg ext obs n) hcurrent
  intro w hw
  exact Weak.getLatestConfirmedTraceAt_current_epochStartSource cfg ext B hT
    hsync hstatic hbyz hdomain hji hanchor hboundary hDelay hcoh hHn1 hcall
    hcurrent w hw

end Weak

end FastConfirmation.Spec

end
