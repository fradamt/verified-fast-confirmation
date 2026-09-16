import FastConfirmation.Spec.Proof.AcceptedActualFCRNextSlotSafetyFold
import FastConfirmation.Spec.Proof.WeakCandidateSourceHistory
import FastConfirmation.Spec.Proof.WeakHistoricalA32OriginCall
import FastConfirmation.Spec.Proof.WeakOneShotSafetyClosed

/-!
# Spec / Proof / WeakTrajectorySafety

Stage 1 of the **weak full-rule** effort: the trajectory invariant, its
initialization, its four-branch step, and the headline fold that lifts the
closed one-shot weak safety theorem from *one* FCR call to *every* second of
the observer's own weak confirmation trajectory.

`WeakOneShotSafetyClosed.lean` closes one call: given that the call's own
candidate input is known and `SafeFrom` from the start of the query slot, the
weak selector's result is `SafeFrom` at the call's own second, with no
`hmargin` and no `hfilter` residue. What it does *not* do is produce those two
inputs: its own docstring flags that closing the "carried" and "observed-reset"
candidate-history branches unconditionally needs an induction over
`E.weakConfirmed`'s own `SafeFrom` history. This file builds that induction.

## The invariant

`Execution.WeakConfirmedSafeFromFollowingSlot cfg ext obs n` — the weak twin of
`Execution.ConfirmedSafeFromFollowingSlot`
(`AcceptedActualFCRNextSlotSafetyFold.lean`), over `E.weakConfirmed` at a
possibly-Byzantine, possibly-eclipsed observer instead of over `E.confirmed` at
an honest node:

> the root the observer's weak FCR trajectory holds at second `n` is an
> ancestor of every in-horizon honest node's fork-choice head from the first
> second of the *following* slot onward.

It is deliberately a **single** conjunct. The two auxiliary trajectory facts a
naive design would bundle alongside it are already built, each by its own
all-seconds weak induction, and neither depends on safety:

* candidate knownness —
  `Weak.AcceptedConfirmedSourceHistoryAt.confirmed_known`, supplied for every
  in-horizon second by `Weak.acceptedConfirmedSourceHistoryAt`
  (`WeakCandidateSourceHistory.lean`), honesty-free at `obs`;
* the certified justification witness carried across epoch boundaries — the
  "restart" bookkeeping of rule delta 5 — supplied for every second by
  `Weak.weakFcr_certifiedBankedJustification` (`WeakBankedJustification.lean`),
  also honesty-free at `obs`.

Folding either into the invariant would duplicate a landed induction, so the
fold consumes them as inputs instead.

## The step

At a call second the invariant's own deadline collapses onto the call
(`Execution.followingSlotStart_eq_succ_of_call`), so the induction hypothesis
is exactly `SafeFrom (E.weakConfirmed obs n) (n + 1)` — and `n + 1` is exactly
the second at which `weak_safeFrom_observerCall_closed_lazy` wants its `hbase`
(`Execution.slot_start_eq_succ_of_advance_minimal` identifies
`E.slot_start (E.slot_at (n + 1))` with `n + 1`). The step therefore reduces to
supplying `hinput`/`hbase` for the call's own candidate input, which
`Weak.GetLatestConfirmedTrace.selectorInput_cases` splits three ways:

* **carried** (`query.confirmed_root`) — `hinput` by `store_storeLE` on the
  previous second's `confirmed_known`; `hbase` is the induction hypothesis;
* **finalized reset** — `hinput` by
  `finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory`; `hbase` by
  `Execution.weak_finalizedReset_safeFrom_of_synchrony`;
* **observed reset** (the epoch-start restart) — `hinput` by
  `Weak.weakFcrStep_observed_known` (rule delta 5's `banked_known`); `hbase`
  by `Weak.ObservedResetSeedSafety`, consumed here and proved in
  `WeakObservedResetSeedSafety.lean`.

Five of those six cells are discharged here. The sixth is proved in
`WeakObservedResetSeedSafety.lean` (stage 6), on top of the arms of
`WeakObservedRestartAdoption.lean` and
`WeakObservedRestartDynamicSafety.lean`, which sit above this file in the
import order; here it is therefore consumed as a named `Prop`,
`Weak.ObservedResetSeedSafety`, in the style `Spec/Model/WeakSynchrony.lean`
already uses for `Weak.CertificateHonestSupporter` /
`Weak.CertificateDissemination`: the migration target is stated, so the fold
below is a complete theorem rather than a placeholder, and the obligation is
visible in the premise list of everything downstream of it.

`Weak.ObservedResetSeedSafety` is the weak twin of the strong
`Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`
(`AcceptedObservedRestartDynamicSafety.lean`), whose proof uses the querying
node's honesty at exactly two sites, both `PaperSafetySynchrony.block_relay`
with that node as *sender*: relaying the banked checkpoint root, and relaying
the GU carrier tip. Rule delta 5's head-indexed banking replaces both with
broadcast certificates at the level of *knownness*
(`Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`,
`Weak.gatedHead_known_at_all_honest_endpoints_at_observer`), and the
head-*domination* step on top of them is stages 2–5. See
`docs/weak-full-rule.md` for the staged plan.

## The all-seconds form of the fold

`Execution.weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le` runs
the same induction with the motive strengthened to
`∀ k ≤ n, WithinHorizon k → invariant k`, and the headline fold is its
`k := n` instance.  The reason is `docs/proviso-discharge-map.md` §4: the
historical A3.2 replay at a call second `n`
(`Weak.observerHistoricalA32CurrentLineageAt_all`, whose call interface is
eta-closed over *all* call seconds in
`Weak.observerHistoricalA32CurrentLineage_invariant`) demands the call-site
data at **every earlier call second `k < n`**, never at a second beyond `n`.
Any discharge of the historical A3.2 crossing payload from the trajectory
invariant therefore needs the invariant retained at those earlier seconds; the
plain single-second motive drops it.  Nothing downstream changes: no signature
moves, and the strengthening is well-founded exactly as the plain induction is.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## The residual obligation -/

/-- **Obligation 3 — observed-reset seed safety at a non-honest observer.**

At a genuine weak FCR call whose candidate input came from the epoch-start
restart branch (`Weak.ObservedResetCandidateInputAt`: the guard fired, so the
observer's `current_epoch_observed_justified_checkpoint` is a previous-epoch
checkpoint equal to the head's own unrealized justification, and it improves
on the post-finalized candidate), the restarted-from root is an ancestor of
every in-horizon honest node's fork-choice head from the call's own second
onward.

This is the weak twin of
`Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`, with
the querying node's honesty binder dropped: under rule delta 5 the field can
only ever hold a broadcast-certified, head-chain-observed justification
(`Weak.CertifiedBankedJustification`, maintained for the whole trajectory by
`Weak.weakFcr_certifiedBankedJustification`), which is the evidence that has to
stand in for the strong proof's two sender-side `block_relay` applications.

Stated as a named `Prop` rather than proved here, because its proof needs the
arm-by-arm discharge of `WeakObservedRestartAdoption.lean` /
`WeakObservedRestartDynamicSafety.lean`, which sit above this file's
`WeakOneShotSafetyClosed` import.  It is **no longer open**:
`Weak.observedResetSeedSafety_of_acceptedDynamics`
(`WeakObservedResetSeedSafety.lean`, stage 6) proves it from the floor alone,
and the fold's unconditional corollary
`Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
lives there too.  The `Prop` is kept as the conditional fold's premise so the
one-call-at-a-time reading remains available. -/
def ObservedResetSeedSafety (E : Execution Root) (obs : ValidatorIndex) : Prop :=
  ∀ n : ℕ, E.WithinHorizon cfg (n + 1) → E.IsFCRCallAt cfg ext obs n →
    ∀ trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n),
      Weak.ObservedResetCandidateInputAt cfg ext
          (E.weakFcrStep cfg ext obs n) trace →
        E.SafeFrom cfg ext trace.afterObserved (n + 1)

/-! ## Branch-dispatch plumbing -/

namespace CandidateHistoryCallBranch

/-- Every operational branch of one weak call exposes an ordered candidate
input origin: the three "unchanged" branches carry their own origin record,
and the strict branch carries the disjunction directly. Pure plumbing — it
lets the input-side lemmas below case on the origin alone, without repeating
the selector-outcome split. -/
theorem origin {query : FastConfirmationStore Root}
    {trace : Weak.GetLatestConfirmedTrace cfg ext query}
    (h : Weak.CandidateHistoryCallBranch cfg ext query trace) :
    Weak.OrderedCandidateInputOrigin cfg ext query trace := by
  cases h with
  | carriedUnchanged hinput _ => exact .carried hinput
  | finalizedResetUnchanged hinput _ => exact .finalizedReset hinput
  | observedResetUnchanged hinput _ => exact .observedReset hinput
  | strictSelected horigin _ => exact horigin

end CandidateHistoryCallBranch

end Weak

namespace Execution

variable (E : Execution Root)

/-! ## The non-duplicated part of the completed-prefix call contract -/

/-- The part of `E.AcceptedHistoricalA32CompletedPrefixCallAssumptions` that is
**not** already contained in `SelectedMarginAssumptions`: the two phase-0
source-coherence contracts and the anchor-active balance floor.

The full 6-field call contract additionally carries `synchrony`,
`static_validators` and `byzantine_bound`, which are literally three fields of
`SelectedMarginAssumptions` — a record every weak trajectory headline already
carries inside `hW.base`.  Taking those three a second time would only
double-count the premise *surface*, so the headlines take this 3-field
supplement and rebuild the full contract internally with
`toCompletedPrefixCallAssumptions` below.

The supplement used to have a fourth field, `delivery_lookahead`.  It is gone:
the boundary delivery case is now part of the single `synchrony` assumption,
which the headlines already carry inside `hW.base`, so dropping it weakened
the premise surface without moving any assumption content. -/
structure AcceptedHistoricalA32CompletedPrefixCallSupplement : Prop where
  phase0_source : Phase0SourceCoherence cfg ext
  phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext
  balance_floor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg)

/-- The 3-field supplement together with the selected-margin floor rebuilds the
full 6-field completed-prefix call contract: the three shared fields are read
off `hA`, so no caller has to supply them twice. -/
def AcceptedHistoricalA32CompletedPrefixCallSupplement.toCompletedPrefixCallAssumptions
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallSupplement cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E) :
    E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext where
  synchrony := hA.synchrony
  static_validators := hA.static_validators
  byzantine_bound := hA.byzantine_bound
  phase0_source := hC.phase0_source
  phase0_boundary_source := hC.phase0_boundary_source
  balance_floor := hC.balance_floor

/-- Local restatement of the Fold file's (private) genesis clock bound. -/
private theorem weakFold_genesisTime_le
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext) :
    E.genesis_store.genesis_time ≤ E.genesis_store.time := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
  rw [hgen]
  simp only [get_forkchoice_store]
  omega

/-! ## The weak full-rule trajectory invariant -/

/-- **The weak full-rule trajectory invariant.** Following-slot safety of the
root the observer's weak FCR trajectory holds at second `n`. Weak twin of
`Execution.ConfirmedSafeFromFollowingSlot`, at an observer that is not assumed
honest and to which no delivery is assumed. -/
def WeakConfirmedSafeFromFollowingSlot (obs : ValidatorIndex) (n : ℕ) : Prop :=
  E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs n)
    (E.followingSlotStart cfg n)

end Execution

namespace Weak

/-- **The invariant the weak fold actually maintains at every second.**

Weak twin of `Execution.AcceptedFoldSafetyAt`
(`AcceptedActualFCRNextSlotSafetyFold.lean`), with one difference, and it is in
the weak side's favour: `callSecond` carries **no** side condition.

`followingSlot` is the historical single-second conclusion, unchanged.

`callSecond` is the *unweakened* form: when second `n` is the write-back second
of a call at `k = n - 1`, the newly cached root is safe from second `n` itself,
not merely from `followingSlotStart n`.  At a call
`Execution.slot_start_eq_succ_of_advance_minimal` gives
`slot_start (slot_at (k + 1)) = k + 1`, so this is exactly the
`slot_start`-indexed safety the lazy A3.2 origin-call transport consumes at an
*earlier* crossing call.

*Why no strictness side condition.*  The strong record has to condition
`callSecond` on `E.confirmed v n ≠ afterObserved`, because its
`finalizedResetUnchanged` arm recovers safety only via
`finalizedReset_safeFrom_of_nextSlotSynchrony`, which needs a strictly later
slot.  The weak fold has no such arm: its step already computes
`hresult : SafeFrom trace.result (n + 1)` on **all four** branches of
`Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`
(`Execution.weak_safeFrom_observerCall_closed_lazy`, driven by `hbase` at
`slot_start (slot_at (n + 1)) = n + 1`) and then throws it away with `.mono`.
This record keeps it.  See `docs/weak-final-wave.md` §3.2. -/
structure ObserverFoldSafetyAt (E : Execution Root) (obs : ValidatorIndex)
    (n : ℕ) : Prop where
  followingSlot : E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n
  callSecond : ∀ k : ℕ, n = k + 1 → E.IsFCRCallAt cfg ext obs k →
    E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs n) n

end Weak

namespace Execution

variable (E : Execution Root)

/-! ## Stage A — initialization ("restarts") -/

/-- **Base case.** The weak trajectory is seeded by the same genesis
initializer as the strong one (`Execution.weakConfirmed_zero`), so its seed is
the trusted anchor and is safe from second `0` — checkpoint-sync safe in
exactly the sense `Weak.acceptedConfirmedSourceHistoryAt_zero` is: the anchor
is the store's own initial finalized checkpoint, not a genesis literal. -/
theorem weakConfirmedSafeFromFollowingSlot_zero
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (obs : ValidatorIndex) :
    E.WeakConfirmedSafeFromFollowingSlot cfg ext obs 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
  have hseed : E.weakConfirmed cfg ext obs 0 = B.anchor.root := by
    rw [E.weakConfirmed_zero, hanchor]
    change E.genesis_store.finalized_checkpoint.root =
      E.genesis_store.justified_checkpoint.root
    rw [hgen]
    rfl
  unfold WeakConfirmedSafeFromFollowingSlot
  rw [hseed]
  exact (E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary).mono cfg ext E (Nat.zero_le _)

/-! ## Stage B — the idle step -/

/-- **No-call step.** Between calls neither the cached root nor the deadline
moves. Weak twin of the `hcall`-negative arm of
`confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold`. -/
theorem weakConfirmedSafeFromFollowingSlot_succ_of_noCall
    {obs : ValidatorIndex} {n : ℕ}
    (hnoCall : ¬ E.IsFCRCallAt cfg ext obs n)
    (h : E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n) :
    Weak.ObserverFoldSafetyAt cfg ext E obs (n + 1) := by
  refine { followingSlot := ?_, callSecond := ?_ }
  · unfold WeakConfirmedSafeFromFollowingSlot at h ⊢
    rw [E.weakConfirmed_succ_of_no_advance cfg ext obs n hnoCall,
      E.followingSlotStart_succ_eq_of_noCall cfg ext hnoCall]
    exact h
  · intro k hk hcallk
    exact absurd (by simpa only [Nat.succ_inj.mp hk] using hcallk) hnoCall

/-! ## Stage C — the call step's candidate-input supply -/

/-- **Candidate-input knownness at a weak call.** The three-way origin split of
`Weak.GetLatestConfirmedTrace.selectorInput_cases`, each arm closed by the
landed weak knownness fact for its own source. This is the named extraction of
a derivation the weak stack currently repeats inline; it is the weak twin of
`Execution.getLatestConfirmedTraceAt_input_known`. -/
theorem weakGetLatestConfirmedTraceAt_input_known
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots) :
    (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
  have hstore : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  rcases (E.weakGetLatestConfirmedTraceAt cfg ext obs n).selectorInput_cases
    cfg ext with hcarried | hfinalized | hobserved
  · rw [hcarried, E.weakFcrStep_confirmed_root, hstore]
    exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
  · rw [hfinalized, hstore]
    exact (E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)).root_known
  · rw [hobserved, hstore]
    exact Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n

/-- **Candidate-input safety at a weak call.** The same three-way origin split,
on the safety side. The carried arm is the induction hypothesis (the invariant
at `n`, whose deadline collapses onto the call second), the finalized arm is
`weak_finalizedReset_safeFrom_of_synchrony`, and the observed-reset arm is the
open obligation `Weak.ObservedResetSeedSafety`.

The conclusion is stated at `E.slot_start cfg (E.slot_at cfg (n + 1))` — the
exact shape `weak_safeFrom_observerCall_closed_lazy` consumes as `hbase`. -/
theorem weakGetLatestConfirmedTraceAt_input_safeFrom
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex}
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs)
    {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hprev : E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n) :
    E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))) := by
  have hacc : FFGAccountabilityAssumptions cfg ext E :=
    SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hcall
  have hstore : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  rw [hstartEq]
  have horigin := ((E.weakGetLatestConfirmedTraceAt cfg ext obs n
    ).candidateHistoryCallBranch cfg ext).origin cfg ext
  cases horigin with
  | carried hinput =>
      have hdeadline : E.followingSlotStart cfg n = n + 1 :=
        E.followingSlotStart_eq_succ_of_call cfg ext hT hA hHn1 hcall
      rw [hinput.input_eq, E.weakFcrStep_confirmed_root]
      unfold WeakConfirmedSafeFromFollowingSlot at hprev
      rwa [hdeadline] at hprev
  | finalizedReset hinput =>
      rw [hinput.input_eq, hstore]
      have hfin := E.weak_finalizedReset_safeFrom_of_synchrony cfg ext B hT hacc
        hphase0 hboundaryPhase hanchor hboundary hA.synchrony
        (v := obs) (q := n + 1) hHn1
      rwa [hstartEq] at hfin
  | observedReset hinput =>
      exact hOR n hHn1 hcall _ hinput

/-! ## Stage D — the call step -/

/-- **Call step.** The invariant at `n` plus the call's own candidate
knownness gives the invariant at `n + 1`, by feeding Stage C's two supplies
into the closed one-shot theorem.

Both components of `Weak.ObserverFoldSafetyAt` come from the *same* witness:
`weak_safeFrom_observerCall_closed_lazy` produces the unweakened
`SafeFrom trace.result (n + 1)` on every branch, which is `callSecond`
verbatim; `followingSlot` is that witness relaxed to the following-slot
deadline.  Before `docs/weak-final-wave.md` §3.2 the unweakened form was
computed here and immediately discarded. -/
theorem weakConfirmedSafeFromFollowingSlot_succ_of_call
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs)
    {n : ℕ}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots)
    (hprev : E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n) :
    Weak.ObserverFoldSafetyAt cfg ext E obs (n + 1) := by
  have hinput := E.weakGetLatestConfirmedTraceAt_input_known cfg ext B hT
    hanchor hboundary (obs := obs) (n := n) hknownN
  have hbase := E.weakGetLatestConfirmedTraceAt_input_safeFrom cfg ext B hT
    hW.base hphase0 hboundaryPhase hanchor hboundary hOR hHn1 hcall hprev
  have hresult := E.weak_safeFrom_observerCall_closed_lazy cfg ext B hT hji
    hanchor hboundary hDelay hphase0 hpaper P V hanchorExact hW hwalkDomain
    hCbase hfit hprior hHn1 hcall hinput hbase
  have hwrite : E.weakConfirmed cfg ext obs (n + 1) =
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    (E.weakActualCandidateHistoryRecurrence cfg ext hcall).result_writeback
  have hunweakened : E.SafeFrom cfg ext
      (E.weakConfirmed cfg ext obs (n + 1)) (n + 1) := by
    rw [hwrite]
    exact hresult
  refine { followingSlot := ?_, callSecond := ?_ }
  · unfold WeakConfirmedSafeFromFollowingSlot
    exact hunweakened.mono cfg ext E
      (Nat.le_of_lt (E.lt_followingSlotStart cfg ext hT (n + 1)))
  · exact fun _ _ _ => hunweakened

/-! ## Stage E — the headline fold -/

/-- **All-seconds form of the weak full-rule fold.**

Same content as `weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold`
below, but with the induction motive strengthened from "the invariant at `n`"
to "the invariant at **every** second `k ≤ n`".

*Why the strengthening is wanted* (see `docs/proviso-discharge-map.md` §4).
The fold's call step feeds `hprev` — input safety at the call's own second —
into `weak_safeFrom_observerCall_closed_lazy`.  That is enough for the
orientation (Trunk-B) proviso sites, which are instantiated at the call second
only.  It is **not** enough for the historical A3.2 lineage: the interface
`Weak.observerHistoricalA32CallInterfaceAt_of_callAssumptions` is eta-closed
over all call seconds in `Weak.observerHistoricalA32CurrentLineage_invariant`,
and the write-back recursion `observerHistoricalA32CurrentLineageAt_all`
replays **every earlier call second `k < n`**.  A discharge of the crossing
payload from the trajectory invariant therefore needs an input-safety witness
at each of those earlier seconds, which the plain
single-second motive does not retain.  The demand is never at a second beyond
`n`, so the strengthened induction is well-founded exactly as the plain one is;
this lemma simply keeps the witness around.

*Why the motive also carries `callSecond`* (see `docs/weak-final-wave.md` §3).
The lazy historical A3.2 crossing manufactures its certificate and quorum at the
*consuming* call from the fold's safety output at the strictly earlier *origin*
call, and it needs that output at the origin call's own second — the unweakened
`slot_start`-indexed form, which `followingSlot` has already thrown away.  So
the retained record is `Weak.ObserverFoldSafetyAt`, whose `callSecond` is
exactly the witness the step already computes.

Purely enabling: no public witness signature changes, and the single-second
theorem is recovered by `.followingSlot` at `k := n`. -/
theorem weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs) :
    ∀ n : ℕ, ∀ k ≤ n, E.WithinHorizon cfg k →
      Weak.ObserverFoldSafetyAt cfg ext E obs k := by
  -- the observer's `justified_root_known` is *derived* here from `B`/`hT`/
  -- `hanchor`/`hboundary`, never assumed
  have hWM := hW.toMarginAssumptions cfg ext E B hT hanchor hboundary
  have hknown := Weak.acceptedConfirmedSourceHistoryAt cfg ext B hT
    hW.base.synchrony hW.base.static_validators hW.base.byzantine_bound
    hW.base.domain hji hanchor hboundary hDelay hWM.coherence
  intro n
  induction n with
  | zero =>
      intro k hk _hH0
      rw [Nat.le_zero.mp hk]
      exact
        { followingSlot := E.weakConfirmedSafeFromFollowingSlot_zero cfg ext B
            hT hanchor hboundary obs
          callSecond := fun _ hk0 => absurd hk0 (by omega) }
  | succ n ih =>
      intro k hk hHk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · have hHn : E.WithinHorizon cfg n :=
          E.withinHorizon_mono cfg (Nat.le_succ n) hHk
        have hprev := (ih n (Nat.le_refl n) hHn).followingSlot
        -- the threaded fold output at the strictly earlier call seconds, read
        -- straight off the strengthened induction hypothesis
        have hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n :=
          fun k hk hHk1 hcallK =>
            (ih (k + 1) hk hHk1).callSecond k rfl hcallK
        by_cases hcall : E.IsFCRCallAt cfg ext obs n
        · exact E.weakConfirmedSafeFromFollowingSlot_succ_of_call cfg ext B hT
            hji hanchor hboundary hDelay hphase0 hboundaryPhase hpaper P V
            hanchorExact hW hwalkDomain hCbase hfit hOR hprior hHk hcall
            (hknown n hHn).confirmed_known hprev
        · exact E.weakConfirmedSafeFromFollowingSlot_succ_of_noCall cfg ext hcall
            hprev
      · exact ih k (Nat.lt_succ_iff.mp hlt) hHk

/-- **The weak full-rule safety theorem.**

Every root the observer's weak FCR trajectory holds, at every in-horizon
second, is an ancestor of every in-horizon honest node's fork-choice head from
the following slot onward — at an observer that is not honest, receives no
guaranteed delivery, and whose every use of synchrony is licensed by a
broadcast certificate.

Weak twin of
`Execution.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold`. Its
premise surface is that of `weak_safeFrom_observerCall_closed_lazy` (the
ratified floor plus the accepted FFG semantic contracts) — with
`hCbase.phase0_boundary_source` supplying the finalized arm of
`weakGetLatestConfirmedTraceAt_input_safeFrom` — together with the single open
obligation `hOR : Weak.ObservedResetSeedSafety`. The strong fold's
observer-honesty binder `hv : v ∈ E.honest` does not appear.

Nothing on the surface is taken twice: `hT` is derived from `hW.base` by
`ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions`,
`hwalkDomain : PostAnchorHonestVoteTargetWalkDomain` is derived from
`hW.base`/`hanchor`/`hboundary` by
`Execution.postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions`
(store-closure walk from the voter's head to the retained trusted anchor, lifted
to the vote's target-epoch boundary by the predicate's own post-anchor
hypothesis), the
phase-0 coherence contracts come from `hCbase` alone, and the call contract is
the 3-field `AcceptedHistoricalA32CompletedPrefixCallSupplement`, whose
`synchrony`/`static_validators`/`byzantine_bound` counterparts in the full
6-field record are read off `hW.base`
(`…CallSupplement.toCompletedPrefixCallAssumptions`).

This theorem and its endpoint form `…_head_of_weakFullRuleFold_nextSlot` are
**not** audit witnesses: they are strictly weaker restatements of the two
unconditional corollaries in `WeakObservedResetSeedSafety.lean`, which discharge
`hOR` from premises this pair already carries and are the registered weak
headlines (`scripts/Audit.lean`).  This pair is kept as an internal theorem —
the unconditional pair's proof chain runs through it — and so that the
one-call-at-a-time reading of `hOR` remains available.

Observer-wise the premise surface is `hW : WeakObserverAssumptions`: committee
readback at the observer's own store, nothing else — `obs` is arbitrary and
may be honest.
`ObserverCoherence.justified_root_known` is *derived* inside the induction
from `B`/`hT`/`hanchor`/`hboundary`
(`WeakObserverAssumptions.toMarginAssumptions`), never assumed.

Corollary of `…_of_weakFullRuleFold_all_le` at `k := n`; the statement is
unchanged. -/
theorem weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n :=
  fun n hHn =>
    (E.weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le cfg ext B
      (ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions cfg ext E
        hW.base)
      hji hanchor hboundary hDelay hCbase.phase0_source
      hCbase.phase0_boundary_source hpaper P V hanchorExact hW
      (E.postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions cfg ext
        hW.base hanchor hboundary)
      (AcceptedHistoricalA32CompletedPrefixCallSupplement.toCompletedPrefixCallAssumptions
        cfg ext E hCbase hW.base)
      hfit hOR n n (Nat.le_refl n) hHn).followingSlot

/-- The lazy weak A3.2 transport's threaded input, straight off the
strengthened fold.

`Weak.ObserverPriorCallWriteBackSafe obs n` is exactly the `callSecond`
component of `Weak.ObserverFoldSafetyAt` at the seconds `k + 1 ≤ n`, so this is
a projection, not a new proof.  Weak twin of
`Execution.priorStrictCallWriteBackSafe_of_acceptedActualFCRFold`. -/
theorem observerPriorCallWriteBackSafe_of_weakFullRuleFold
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs)
    (n : ℕ) :
    Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n :=
  fun k hk hHk1 hcallK =>
    (E.weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le cfg ext B
      hT hji hanchor hboundary hDelay hphase0 hboundaryPhase hpaper P V
      hanchorExact hW hwalkDomain hCbase hfit hOR n (k + 1) hk
        hHk1).callSecond k rfl hcallK

/-- Endpoint form of the weak full-rule theorem, matching the paper's timing:
the observer's weak confirmed root at second `n` is canonical at every
in-horizon honest endpoint in a strictly later slot. Weak twin of
`Execution.confirmed_head_of_acceptedActualFCRFold_nextSlot`. -/
theorem weakConfirmed_head_of_weakFullRuleFold_nextSlot
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hOR : Weak.ObservedResetSeedSafety cfg ext E obs)
    {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakConfirmed cfg ext obs n)) = true := by
  have hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext :=
    ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions cfg ext E
      hW.base
  have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg hnm hHm
  have hsafe := E.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold cfg ext
    B hji hanchor hboundary hDelay hpaper P V
    hanchorExact hW hCbase hfit hOR n hHn
  have hdeadlineLe : E.followingSlotStart cfg n ≤ m := by
    by_contra hnot
    have hmLt : m < E.followingSlotStart cfg n := Nat.lt_of_not_ge hnot
    have hslotLt := (E.slot_at_lt_iff cfg hT.whole_seconds
      (E.weakFold_genesisTime_le cfg ext hT)).2 hmLt
    exact (Nat.not_lt_of_ge hnext) hslotLt
  exact hsafe w hw m hdeadlineLe hHm

end Execution

end FastConfirmation.Spec
