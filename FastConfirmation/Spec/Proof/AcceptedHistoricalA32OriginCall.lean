import FastConfirmation.Spec.Proof.HonestTargetAgreement
import FastConfirmation.Spec.Proof.TrustedAnchorGeometry
import FastConfirmation.Spec.Proof.SelectedCoveredMarginConstruction

/-!
# Origin-call data for a historical A3.2 crossing, and its lazy proviso

`docs/trunkA-final-discharge.md` §2.4 is the reason this module exists.

The historical A3.2 payload used to carry the *positive* certification content
(`certified`, and the quorum behind `support_branch`) as data, proved at the
crossing call.  That is **same-step circular**: the only proviso-free route to
`HonestVotesSupportTarget` at a call is
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
(`HonestTargetAgreement.lean`), whose `hsafe` input at the crossing call's own
second is literally the conclusion the safety fold is proving at that step.

The repair is **laziness**.  The payload carries only the *origin-call data*
recorded here — which validator called, at which second, on which root, with
which gate boolean, and that the call's current target is the retained
checkpoint.  The positive content is then manufactured at the **consuming**
call, which is strictly later, from the fold's safety output *at the origin
call*.  That input is a strictly earlier fold output, so the recursion is
well-founded.

`AcceptedHistoricalA32OriginCallAt.honestVotesSupportTarget` is the single new
proof: origin-call data plus `E.SafeFrom origin (second + 1)` reconstructs the
whole proviso at the crossing call.  Everything downstream — the existing
`certifiedCurrentTarget_of_gate_and_stateSemantics` pipeline — is then run
unchanged, just later.

Nothing here mentions `ExactPrefixAcceptedFFGSemantics`: the record is indexed
by a bare `Checkpoint Root`, so that the payload can index it by the
*checkpoint* `B.state.C · e` and transport it by the same one-line `rw` that
`transport_sameEpoch` already uses (`docs/trunkA-final-discharge.md` §2.1).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The originating-call record of a historical A3.2 crossing.

Every field is a fact *about the crossing call itself*; none of them is a
certificate, a quorum, or any other positive certification content, and none
of them mentions safety.  That is the point: the record is constructible at the
crossing call without circularity, and the positive content is rebuilt later
from it.

* `node_honest`, `second_horizon`, `is_call` — the call happened, at an honest
  node, in horizon.  `is_call` is what makes
  `E.slot_start_eq_succ_of_advance_minimal` give
  `slot_start (slot_at (second + 1)) = second + 1`, the exact deadline shape
  the reconstruction consumes.
* `origin_known`, `origin_parent_known`, `origin_confirmed` — the crossing
  origin is the call's concretely one-confirmed selected result.  These three
  are what carry it to *every* honest voter's store later, via
  `confirmed_known_at_all_honest_endpoints_minimal`.
* `origin_current`, `head_descends` — the origin is a current-epoch block of
  the query store which the query head descends from.  Per
  `docs/proviso-discharge-map.md` §5.1 this is the configuration the weak
  one-shot sites cannot supply; at a crossing it holds by construction
  (`strictSelectedResult_below_head`).
* `gate` — the executable boolean the call actually evaluated.
* `target_eq` — the call's current target is the retained checkpoint. -/
structure AcceptedHistoricalA32OriginCallAt
    (node : ValidatorIndex) (second : ℕ) (origin : Root)
    (target : Checkpoint Root) : Prop where
  node_honest : node ∈ E.honest
  second_horizon : E.WithinHorizon cfg (second + 1)
  is_call : E.IsFCRCallAt cfg ext node second
  origin_known : origin ∈ (E.fcrStep cfg ext node second).store.block_roots
  origin_parent_known :
    ((E.fcrStep cfg ext node second).store.blocks origin).parent_root ∈
      (E.fcrStep cfg ext node second).store.block_roots
  origin_confirmed : is_one_confirmed cfg ext
    (E.fcrStep cfg ext node second).store
    (get_current_balance_source (E.fcrStep cfg ext node second)) origin = true
  origin_current : get_block_epoch cfg (E.fcrStep cfg ext node second).store
      origin =
    get_current_store_epoch cfg (E.fcrStep cfg ext node second).store
  head_descends : is_ancestor (E.fcrStep cfg ext node second).store
    (get_head cfg (E.fcrStep cfg ext node second).store)
    (get_node_for_root origin) = true
  /-- The origin *is* the root this call writes back. -/
  origin_writeback : E.confirmed cfg ext node (second + 1) = origin
  /-- …and the write-back strictly advanced.  Both facts hold at a crossing by
  `AcceptedCandidateHistoryRecurrence`'s `result_writeback` and
  `CurrentTargetAcceptedEdge.result_ne_input`; together they are exactly the
  shape `Execution.AcceptedFoldSafetyAt.callSecond` consumes, which is how the
  origin's safety is recovered from a strictly earlier fold output. -/
  origin_strict : origin ≠
    (E.getLatestConfirmedTraceAt cfg ext node second).afterObserved
  gate : will_current_target_be_justified cfg ext
    (E.fcrStep cfg ext node second).store = true
  target_eq : get_current_target cfg (E.fcrStep cfg ext node second).store =
    target

/-- Existential wrapper: *some* crossing call produced this checkpoint.

This is the shape the payload field takes.  The call data is existentially
quantified because the payload is transported along a same-epoch segment and
must not re-index it; the checkpoint `target` is constant along that segment
(`AcceptedHistoricalA32GatePayloadAt.transport_sameEpoch`'s `hcheckpoint`), so
the whole object transports by a single `rw`. -/
def AcceptedHistoricalA32OriginCallFor (target : Checkpoint Root) : Prop :=
  ∃ (node : ValidatorIndex) (second : ℕ) (origin : Root),
    E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target

/-- **The threaded fold output the lazy transport consumes.**

Every strictly advanced call write-back at a second *strictly below* `n`, at
any honest node, is safe from its own write-back second — the **unweakened**
`slot_start`-indexed deadline, not the `followingSlotStart`-mono'd one
(`docs/trunkA-final-discharge.md` §5.3).

This is exactly the `callSecond` component of `Execution.AcceptedFoldSafetyAt`
at seconds `k + 1 ≤ n`, i.e. precisely what the accepted fold's strengthened
induction hypothesis hands out at its `succ n` step.  Well-foundedness is the
strict `k < n`: the crossing that produced a payload consumed at the call for
second `n` necessarily happened at an earlier call, because the
`currentHistorical` arm fires only when *this* call found no crossing edge
(§2.4).  An eager variant would need `k = n` and would be circular. -/
def PriorStrictCallWriteBackSafe (n : ℕ) : Prop :=
  ∀ i ∈ E.honest, ∀ k : ℕ, k < n → E.WithinHorizon cfg (k + 1) →
    E.IsFCRCallAt cfg ext i k →
    E.confirmed cfg ext i (k + 1) ≠
      (E.getLatestConfirmedTraceAt cfg ext i k).afterObserved →
      E.SafeFrom cfg ext (E.confirmed cfg ext i (k + 1)) (k + 1)

/-- Monotonicity in the horizon: a wider prior window restricts. -/
theorem PriorStrictCallWriteBackSafe.mono {n m : ℕ} (hnm : n ≤ m)
    (h : E.PriorStrictCallWriteBackSafe cfg ext m) :
    E.PriorStrictCallWriteBackSafe cfg ext n :=
  fun i hi k hk => h i hi k (Nat.lt_of_lt_of_le hk hnm)

namespace AcceptedHistoricalA32OriginCallAt

/-- **The lazy reconstruction.**  Origin-call data plus the fold's safety
output at the origin call rebuilds the *whole* target-support proviso at that
call.

This is the first consumer of
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
(`HonestTargetAgreement.lean`), and it supplies every one of that lemma's
seventeen hypotheses without a proviso:

* the clock/behaviour side conditions come from `hA`;
* `hqStart` is `E.slot_start_eq_succ_of_advance_minimal` at `is_call`;
* the query-store geometry is `origin_current` / `head_descends` from the
  record plus two trusted-anchor boundary walks;
* the five voter-side families are ambient store facts at any honest store —
  `stateSlotsLE`, `store_domainK_of_selectedMarginDomain`,
  `trustedAnchor_boundaryWalkAtEpoch`, `blocks_agree` — except for knownness of
  the origin in the voter's own store, which is
  `confirmed_known_at_all_honest_endpoints_minimal` applied to
  `origin_confirmed`.

`hsafe` is the only genuinely non-local input, and on the strong path it is the
`callSecond` component of `Execution.AcceptedFoldSafetyAt` at the *origin*
call, i.e. a strictly earlier fold output. -/
theorem honestVotesSupportTarget
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    (hsafe : E.SafeFrom cfg ext origin (second + 1)) :
    HonestVotesSupportTarget cfg E target (second + 1) := by
  classical
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  set q : ℕ := second + 1 with hq
  have hqH : E.WithinHorizon cfg q := h.second_horizon
  have hqStore : (E.fcrStep cfg ext node second).store =
      E.store cfg ext node q := E.fcrStep_store cfg ext node second
  -- the query second is the first second of its slot
  have hqStart : E.slot_start cfg (E.slot_at cfg q) = q := by
    exact E.slot_start_eq_succ_of_advance_minimal cfg ext (v := node) hA second
      h.second_horizon h.is_call
  -- genesis clock facts
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  -- the trusted anchor is never above any store's current epoch
  have hanchorLe : ∀ (w : ValidatorIndex) (m : ℕ), anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext w m) :=
    fun w m => E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor
      hboundary w m
  set epochQ : Epoch :=
    get_current_store_epoch cfg (E.fcrStep cfg ext node second).store
    with hepochQ
  have hanchorLeQ : anchor.epoch ≤ epochQ := by
    rw [hepochQ, hqStore]
    exact hanchorLe node q
  -- query-store geometry
  obtain ⟨hparentQ, _hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain node h.node_honest q hqH
  have hqueryParent : ParentSlotLt (E.fcrStep cfg ext node second).store := by
    rw [hqStore]; exact hparentQ
  have hheadQ : (get_head cfg (E.store cfg ext node q)).root ∈
      (E.store cfg ext node q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      h.node_honest q hqH
  have hqueryHeadWalk : WalkKnown (E.fcrStep cfg ext node second).store
      (compute_start_slot_at_epoch cfg epochQ)
      (get_head cfg (E.fcrStep cfg ext node second).store).root := by
    rw [hqStore]
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      node q (by rw [hepochQ, hqStore] at hanchorLeQ ⊢; exact hanchorLeQ)
      hheadQ
  have horiginKnownQ : origin ∈ (E.store cfg ext node q).block_roots := by
    rw [← hqStore]; exact h.origin_known
  have hqueryWalk : WalkKnown (E.fcrStep cfg ext node second).store
      (compute_start_slot_at_epoch cfg epochQ) origin := by
    rw [hqStore]
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      node q (by rw [hepochQ, hqStore] at hanchorLeQ ⊢; exact hanchorLeQ)
      horiginKnownQ
  -- voter-side families, uniformly at every honest store at or after `q`
  have hvoterHeadSlot : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      ((E.store cfg ext i k).block_states
        (get_head cfg (E.store cfg ext i k)).root).slot ≤ E.slot_at cfg k := by
    intro i hi k _hqk hHk
    have hheadK := E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hi k hHk
    have hstate := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen0 i k).1 _ hheadK
    simpa only [E.store_current_slot] using hstate
  have hvoterParent : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k → ParentSlotLt (E.store cfg ext i k) := by
    intro i hi k _hqk hHk
    exact (E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain i hi k hHk).1
  have hvoterHeadWalk : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg epochQ)
        (get_head cfg (E.store cfg ext i k)).root := by
    intro i hi k _hqk hHk
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      i k hanchorLeQ
      (E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi k hHk)
  -- the crossing origin is one-confirmed, hence known at every later honest
  -- endpoint
  have horiginKnownAt : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k → origin ∈ (E.store cfg ext i k).block_roots := by
    intro i hi k hqk hHk
    refine E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      node h.node_honest q (E.fcrStep cfg ext node second) hqStore origin
      hqH horiginKnownQ ?_ ?_ i hi k (E.slot_at_mono cfg hqk) hHk
    · rw [← hqStore]; exact h.origin_parent_known
    · exact h.origin_confirmed
  have hvoterWalk : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg epochQ) origin := by
    intro i hi k hqk hHk
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      i k hanchorLeQ (horiginKnownAt i hi k hqk hHk)
  have hagree : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ∀ r : Root, r ∈ (E.store cfg ext i k).block_roots →
        r ∈ (E.fcrStep cfg ext node second).store.block_roots →
        (E.store cfg ext i k).blocks r =
          (E.fcrStep cfg ext node second).store.blocks r := by
    intro i _hi k _hqk _hHk r hrK hrQ
    rw [hqStore] at hrQ ⊢
    exact hA.wellFormed.blocks_agree (E.blockProvenance cfg ext i k)
      (E.blockProvenance cfg ext node q) hrK hrQ
  -- assemble
  have hsupport := E.honestVotesSupportTarget_of_safeFrom_currentEpochCandidate
    cfg ext hA.honest_behavior hA.externals_coherence.process_slots_slot
    hA.whole_seconds hgenTime
    (query := E.fcrStep cfg ext node second) (b := origin) (q := q)
    hqH hqStart hsafe hqueryParent h.head_descends h.origin_current
    hqueryHeadWalk hqueryWalk hvoterHeadSlot hvoterParent hvoterHeadWalk
    hvoterWalk hagree
  rw [h.target_eq] at hsupport
  exact hsupport

/-- Recover the origin call's safety from the threaded fold output.

This is the one place where the recursion's well-foundedness is discharged:
the origin call sits at a second `second < n` strictly below the consuming
call, so the required witness is a strictly earlier output of the same fold. -/
theorem safeFrom_of_prior
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    {n : ℕ} (hlt : second < n)
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n) :
    E.SafeFrom cfg ext origin (second + 1) := by
  have hsafe := hprior node h.node_honest second hlt h.second_horizon h.is_call
    (by rw [h.origin_writeback]; exact h.origin_strict)
  rwa [h.origin_writeback] at hsafe

/-- **A3, first half** — run the *unchanged* gate-realization producer at the
crossing call.

This is the whole of the lazy design downstream of the reconstruction: the
producer (`AcceptedCurrentTargetA32GateRealizationProducerAt`, i.e.
`certifiedCurrentTarget_of_gate_and_stateSemantics` at the actual call) is not
modified in any way — it is simply *called later*, at the consuming call,
with the proviso rebuilt on the spot instead of taken from the call-site
record. -/
theorem gateRealization
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : AcceptedChainFFGState cfg ext E anchor}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    (hsafe : E.SafeFrom cfg ext origin (second + 1))
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S (second + 1) (E.fcrStep cfg ext node second)) :
    AcceptedCurrentTargetA32GateRealization cfg ext E anchor S
      (E.fcrStep cfg ext node second).store := by
  refine hproducer h.gate ?_
  rw [h.target_eq]
  exact h.honestVotesSupportTarget cfg ext E hA hanchor hboundary hsafe

/-- **A3, second half** — the certificate the two `currentHistorical` arms
actually read, rebuilt at the consuming call.

`docs/trunkA-final-discharge.md` §1: the only thing either arm extracts from
the payload's old `certified` field is
`Nonempty (CertifiedJustified anchor T)`, consumed once by
`CertificateAccountability.justified_unique`.  This produces exactly that, from
origin-call data plus the origin's safety. -/
theorem certified
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : AcceptedChainFFGState cfg ext E anchor}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    (hsafe : E.SafeFrom cfg ext origin (second + 1))
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S (second + 1) (E.fcrStep cfg ext node second)) :
    Nonempty (CertifiedJustified cfg E anchor target) := by
  have hreal := h.gateRealization cfg ext E hA hanchor hboundary hsafe hproducer
  have hcert := hreal.certified
  rwa [h.target_eq] at hcert

end AcceptedHistoricalA32OriginCallAt

end Execution

end FastConfirmation.Spec
