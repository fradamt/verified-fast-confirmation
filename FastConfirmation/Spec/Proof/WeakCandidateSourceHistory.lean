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

end Weak

end FastConfirmation.Spec
