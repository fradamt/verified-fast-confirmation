import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedCurrentSameSourceHistory
import FastConfirmation.Spec.Proof.WeakCandidateHistoryRecurrence
import FastConfirmation.Spec.Proof.WeakEarlyPhaseSourceWiring

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

| strong use | weak replacement |
|---|---|
| `store_domainK_of_selectedMarginDomain … hv` | `Execution.observerStoreDomainK` (`WeakObserverDomain.lean`) |
| `head_root_known_of_selectedMarginDomain … hv` | `Execution.head_root_known_at_observer` (same) |
| `hsync.block_relay` of a seed out of the observer's store | the landed certificate-dissemination lemmas (below) |
| `StrictSelectorAdvanceAt.mechanicalFacts … hv` | `Weak.strictSelectedResultMechanicalFacts … hcoh` (`WeakSelectedTrace.lean`) |
| `not_epochStart_of_current_of_selectedMargin … hv` | `Weak.…not_epochStart_of_current` + `…confirmedPastDescendantSlotWitness_at_observer` |

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
* the epoch-start banked origin (site 8 of the design's inventory):
  `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`
  (`WeakBankedJustification.lean`), whose two arms are exactly global
  knownness of the anchor and the certificate minted at the banking second.

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
   stays strict.** The proposal suggested relaxing it to `second ≤ boundary`
   to accommodate a same-slot certificate. The relaxation is unnecessary for
   the *seed* (see 2), and is needed only for the banked arm's `second`,
   which is why the weak record's field is `second_le_boundary : second ≤
   boundary` — the one place the two differ.
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
  { genesis := hT.genesis
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
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
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
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
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
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
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
      simp only [Weak.has_head_broadcast_certificate,
        ← hcert.supplier_eq_head] at hc'
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
      Weak.headUnrealizedJustification_known_and_below cfg ext B hT hanchor
        hboundary obs hcert.second
    rw [← hcert.supplier_eq_head, ← hcert.banked_eq] at hbelow
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
    seed := (get_head cfg (E.store cfg ext obs q)).root
    seed_known := by simpa only [hquery] using hhead
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
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis
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
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
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

end Weak

end FastConfirmation.Spec
