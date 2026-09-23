module
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationProofs.FCRRule.SelectedEdgeSafety
public import FastConfirmationProofs.Safety.FinalizedCheckpointNextSlotSafety
public import FastConfirmationProofs.Safety.ObservedRestartSafety
public import FastConfirmationProofs.Weak.History.AcceptedHistoricalA32OriginCall
public import FastConfirmationProofs.ModelFacts

@[expose] public section


/-!
# Accepted actual-FCR next-slot safety fold

This fold proves following-slot safety for the exact executable `confirmed`
cache.  A root stored during slot `s` is required to be safe from the first second
of slot `s + 1`:

`slot_start (slot_at n + 1)`.

Consequently the finalized-reset arm uses ordinary synchrony and the accepted
next-slot finalized theorem.  No same-moment finalized-revert adoption law is
assumed.

The active observed-reset arm is likewise derived from the accepted execution:
same-epoch checkpoints close by accountable uniqueness, while later justified
checkpoints expose an earlier honest target vote and close by strong induction.
Thus this fold has no separate reset-safety or source-lock premise.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- First execution second of the slot following the slot containing `n`. -/
def followingSlotStart (n : ℕ) : ℕ :=
  E.slot_start cfg (E.slot_at cfg n + 1)

/-- Following-slot safety of the cached output present at second `n`. -/
def ConfirmedSafeFromFollowingSlot (v : ValidatorIndex) (n : ℕ) : Prop :=
  E.SafeFrom cfg ext (E.confirmed cfg ext v n) (E.followingSlotStart cfg n)

/-- **The invariant the accepted fold actually maintains at every second.**

`followingSlot` is the historical single-second conclusion, unchanged.

`callSecond` is the *unweakened* form: when second `n` is the write-back
second of a call at `k = n - 1` whose selector **strictly advanced**, the newly
cached root is safe from second `n` itself, not merely from
`followingSlotStart n`.  At a call `E.slot_start_eq_succ_of_advance_minimal`
gives `slot_start (slot_at (k + 1)) = k + 1`, so this is exactly the
`slot_start`-indexed safety that the lazy A3.2 origin-call transport consumes
at an *earlier* crossing call (`docs/trunkA-final-discharge.md` §2.4, §5.3);
the `followingSlotStart` form is strictly weaker and does not suffice there.

The strictness side condition is not a restriction for that consumer: an A3.2
crossing origin is produced only on the `strictSelected` arm, whose
`StrictSelectorAdvanceAt.result_ne_input` supplies it.  It is *necessary*
here: on the `finalizedResetUnchanged` arm the cached root is the query's
freshly finalized checkpoint, whose safety genuinely needs a strictly later
slot (`finalizedReset_safeFrom_of_nextSlotSynchrony` takes
`slot_at (n + 1) + 1 ≤ slot_at q`), so no unconditional unweakened form is
derivable. -/
structure AcceptedFoldSafetyAt (v : ValidatorIndex) (n : ℕ) : Prop where
  followingSlot : E.ConfirmedSafeFromFollowingSlot cfg ext v n
  callSecond : ∀ k : ℕ, n = k + 1 → E.IsScheduledFCRCallAt cfg ext v k →
    E.confirmed cfg ext v n ≠
      (E.getLatestConfirmedTraceAt cfg ext v k).afterObserved →
    E.SafeFrom cfg ext (E.confirmed cfg ext v n) n

private theorem nextSlotFold_genesisTime_le
    (hT : E.ScheduledPrefixPremises cfg ext) :
    E.genesis_store.genesis_time ≤ E.genesis_store.time := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  rw [hgen]
  simp only [get_forkchoice_store]
  omega

/-- A whole-second execution can advance by at most one slot per execution
second. -/
private theorem nextSlotFold_slot_at_succ_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (n : ℕ) :
    E.slot_at cfg (n + 1) ≤ E.slot_at cfg n + 1 := by
  obtain ⟨secondsPerSlot, hduration⟩ := hdiv
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  have hdenPos : 0 < cfg.slot_duration_ms / 1000 := by
    rw [hduration, Nat.mul_div_cancel_left secondsPerSlot
      (by omega : (0 : ℕ) < 1000)]
    exact hsecondsPos
  have hdiv' : 1000 ∣ cfg.slot_duration_ms :=
    ⟨secondsPerSlot, hduration⟩
  rw [E.slot_at_eq cfg hdiv', E.slot_at_eq cfg hdiv']
  have hnum : E.genesis_store.time + (n + 1) -
        E.genesis_store.genesis_time =
      (E.genesis_store.time + n - E.genesis_store.genesis_time) + 1 := by
    omega
  rw [hnum]
  let a := E.genesis_store.time + n - E.genesis_store.genesis_time
  calc
    (a + 1) / (cfg.slot_duration_ms / 1000) ≤
        (a + cfg.slot_duration_ms / 1000) /
          (cfg.slot_duration_ms / 1000) :=
      Nat.div_le_div_right (by omega)
    _ = a / (cfg.slot_duration_ms / 1000) + 1 :=
      Nat.add_div_right a hdenPos

/-- The following-slot boundary really lies in the following slot. -/
theorem slot_at_followingSlotStart
    (hT : E.ScheduledPrefixPremises cfg ext)
    (n : ℕ) :
    E.slot_at cfg (E.followingSlotStart cfg n) = E.slot_at cfg n + 1 := by
  have hgenTime : E.genesis_store.genesis_time ≤
      E.genesis_store.time :=
    E.nextSlotFold_genesisTime_le cfg ext hT
  apply E.slot_at_slot_start cfg hT.whole_seconds
  · exact (E.slot_at_mono cfg (Nat.zero_le n)).trans
      (Nat.le_succ (E.slot_at cfg n))
  · exact hgenTime

/-- Every second precedes the boundary of its following slot. -/
theorem lt_followingSlotStart
    (hT : E.ScheduledPrefixPremises cfg ext)
    (n : ℕ) :
    n < E.followingSlotStart cfg n := by
  have hgenTime : E.genesis_store.genesis_time ≤
      E.genesis_store.time :=
    E.nextSlotFold_genesisTime_le cfg ext hT
  exact (E.slot_at_lt_iff cfg hT.whole_seconds hgenTime).1
    (Nat.lt_succ_self (E.slot_at cfg n))

/-- At an actual FCR call, the preceding cached output's following-slot
deadline is exactly the call second.  The second equality is the accepted
minimal call-boundary theorem; the one-second clock bound identifies the new
slot with the successor of the old slot. -/
theorem followingSlotStart_eq_succ_of_call
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n) :
    E.followingSlotStart cfg n = n + 1 := by
  have hgenTime : E.genesis_store.genesis_time ≤
      E.genesis_store.time :=
    E.nextSlotFold_genesisTime_le cfg ext hT
  have hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    unfold IsScheduledFCRCallAt at hcall
    simpa only [E.store_current_slot] using hcall
  have hstep : E.slot_at cfg (n + 1) = E.slot_at cfg n + 1 :=
    Nat.le_antisymm
      (E.nextSlotFold_slot_at_succ_le cfg hT.whole_seconds hgenTime n)
      (Nat.succ_le_iff.mpr hadvance)
  have hcallStart :
      E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal
      cfg ext hA n hHn1 hcall
  unfold followingSlotStart
  rw [← hstep]
  exact hcallStart

/-- Between calls the local slot is unchanged, hence the paper deadline is
unchanged as well. -/
theorem followingSlotStart_succ_eq_of_noCall
    {v : ValidatorIndex} {n : ℕ}
    (hnoCall : ¬ E.IsScheduledFCRCallAt cfg ext v n) :
    E.followingSlotStart cfg (n + 1) = E.followingSlotStart cfg n := by
  have hslotMono : E.slot_at cfg n ≤ E.slot_at cfg (n + 1) :=
    E.slot_at_mono cfg (Nat.le_succ n)
  have hslotEq : E.slot_at cfg (n + 1) = E.slot_at cfg n := by
    apply Nat.le_antisymm
    · unfold IsScheduledFCRCallAt at hnoCall
      rw [E.store_current_slot, E.store_current_slot] at hnoCall
      exact Nat.le_of_not_gt hnoCall
    · exact hslotMono
  simp only [followingSlotStart, hslotEq]

/-- A selector-eligible finalized-reset input can only be the trusted anchor.
A non-anchor finalized checkpoint is two epochs old by causal finalization lag,
contradicting the selector's literal recency premise.  The conclusion does not
require the selector to advance strictly, so it also covers a selected helper
call whose return is unchanged. -/
theorem finalizedResetCandidateInput_safeFrom_anchor_of_recent
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    {v : ValidatorIndex} {n : ℕ}
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (hinput : FinalizedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace)
    (hrecent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        trace.afterObserved + 1 ≥
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
  let query := E.fcrStoreAtCall cfg ext v n
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay
      cfg ext B hT hanchor hDelay
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.fcrStep_store] using
      E.store_causal cfg ext v (n + 1)
  have hrealizedQuery : E.ResetCheckpointRealizedAt cfg B.anchor
      query.store query.store.finalized_checkpoint := by
    simpa only [query, E.fcrStep_store] using hrealized
  have hrecentFinalized : get_block_epoch cfg query.store
        query.store.finalized_checkpoint.root + 1 ≥
      get_current_store_epoch cfg query.store := by
    simpa only [query, hinput.input_eq] using hrecent
  have hfinalizedAnchor : query.store.finalized_checkpoint = B.anchor := by
    by_contra hne
    have hstale := E.finalizedResetRoot_stale_of_causalLag
      cfg ext hLag hstore hrealizedQuery hne
    exact (Nat.not_lt_of_ge hrecentFinalized) hstale
  have hroot : trace.afterObserved = B.anchor.root := by
    calc
      trace.afterObserved = query.store.finalized_checkpoint.root := by
        simpa only [query] using hinput.input_eq
      _ = B.anchor.root := congrArg Checkpoint.root hfinalizedAnchor
  rw [hroot]
  exact (E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary).mono cfg ext E (Nat.zero_le _)

/-- Strict-selector convenience wrapper around the plain recency theorem. -/
theorem strictFinalizedResetCandidateInput_safeFrom_anchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    {v : ValidatorIndex} {n : ℕ}
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (hinput : FinalizedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace) :
    E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
  exact E.finalizedResetCandidateInput_safeFrom_anchor_of_recent
    cfg ext B hT hanchor hboundary hDelay hinput hselector.input_recent

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1400000 in
-- The dependent dispatcher elaborates separately in all strict input origins.
/-- **All-seconds form of the accepted actual-FCR next-slot safety fold.**

Same content as `confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold`
below, but with the induction motive strengthened in two ways: from "the
invariant at `n`" to "the invariant at **every** second `k ≤ n`", and from
`ConfirmedSafeFromFollowingSlot` alone to the pair `AcceptedFoldSafetyAt`,
which additionally exposes the *unweakened* call-second safety
`E.SafeFrom cfg ext (E.confirmed cfg ext v (k + 1)) (k + 1)` of a strictly
advanced write-back.

*Why the strengthening is wanted* (`docs/trunkA-final-discharge.md` §2.4,
§5.3; strong twin of the weak
`weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`,
`WeakTrajectorySafety.lean`).  The A3.2 write-back recursion replays **every
earlier call second `k < n`**, and the lazy origin-call transport of the
historical A3.2 payload reconstructs the target-support proviso at the
*crossing* call `k + 1` from safety of that call's own confirmed result at
second `k + 1`.  Both the all-`k` quantification and the unweakened
`slot_start`-indexed deadline are therefore needed, and neither survives the
plain single-second `followingSlotStart` motive.  The demand is never at a
second beyond `n`, so the strengthened induction is well-founded exactly as
the plain one is; this theorem simply keeps the witnesses around.

Finalized unchanged resets use synchrony at the following-slot deadline.
Strict finalized resets reduce to the trusted anchor before the strict-helper
dispatcher is invoked.  Active observed resets use the accepted dynamic
checkpoint proof.

Purely enabling: no signature below changes, and the historical single-second
theorem is recovered by instantiating `k := n` and projecting
`followingSlot`. -/
theorem confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold_all_le
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity) :
    ∀ n : ℕ, ∀ k ≤ n, E.WithinHorizon cfg k → ∀ v ∈ E.honest,
      E.AcceptedFoldSafetyAt cfg ext v k := by
  have hdomain : SelectedMarginDomain cfg ext E :=
    E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hC.synchrony hanchor hboundary
  have hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch :=
    acceptedAnchorExact_of_trajectory cfg ext E B hT hanchor hboundary
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hacc : FFGAccountabilityAssumptions cfg ext E :=
    SelectedMarginAssumptions.toFFGAccountabilityAssumptions
      cfg ext E hMargin
  intro n
  induction n with
  | zero =>
      intro k hk _hH0 v hv
      rw [Nat.le_zero.mp hk]
      refine { followingSlot := ?_, callSecond := ?_ }
      · unfold ConfirmedSafeFromFollowingSlot
        exact (E.confirmed_zero_safeFrom_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary v).mono cfg ext E (Nat.zero_le _)
      · intro j hj _ _
        exact absurd hj.symm (Nat.succ_ne_zero j)
  | succ n ih =>
      intro k hk hHn1 v hv
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      swap
      · exact ih k (Nat.lt_succ_iff.mp hlt) hHn1 v hv
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hsafeN := (ih n (Nat.le_refl n) hHn v hv).followingSlot
      -- The strengthened induction hypothesis *is* the threaded lazy-transport
      -- input: at every strictly advanced call second `k < n` the write-back is
      -- safe from its own second (`docs/crossing-call-support-residue.md` §4.3,
      -- the `k < n` arm of the consumer-side discharge).
      have hprior : E.PriorStrictCallWriteBackSafe cfg ext n :=
        fun i hi k hk hHk1 hcallK hstrictK =>
          (ih (k + 1) (Nat.succ_le_of_lt hk) hHk1 i hi).callSecond k rfl
            hcallK hstrictK
      by_cases hcall : E.IsScheduledFCRCallAt cfg ext v n
      · let trace := E.getLatestConfirmedTraceAt cfg ext v n
        have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
        have hpreviousDeadline : E.followingSlotStart cfg n = n + 1 :=
          E.followingSlotStart_eq_succ_of_call
            cfg ext hT hMargin hHn1 hcall
        have hsafePreviousAtCall : E.SafeFrom cfg ext
            (E.confirmed cfg ext v n) (n + 1) := by
          simpa only [ConfirmedSafeFromFollowingSlot,
            hpreviousDeadline] using hsafeN
        have hknownN : E.confirmed cfg ext v n ∈
            (E.store cfg ext v n).block_roots :=
          E.confirmed_known_of_acceptedGlobalTrajectory
            cfg ext B hT hanchor hboundary hv n hHn
        have hinputKnown : trace.afterObserved ∈
            (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
          simpa only [trace] using
            E.getLatestConfirmedTraceAt_input_known
              cfg ext B hT hanchor hboundary hknownN
        have hcallToDeadline : n + 1 ≤
            E.followingSlotStart cfg (n + 1) :=
          Nat.le_of_lt (E.lt_followingSlotStart cfg ext hT (n + 1))
        have hdeadlineSlot : E.slot_at cfg (n + 1) + 1 ≤
            E.slot_at cfg (E.followingSlotStart cfg (n + 1)) := by
          rw [E.slot_at_followingSlotStart cfg ext hT (n + 1)]
        have hbranch : CandidateHistoryCallBranch cfg ext
            (E.fcrStoreAtCall cfg ext v n) trace := by
          simpa only [trace] using hrec.branch
        -- One pass over the four-way branch classification, producing both
        -- the following-slot form and the unweakened strict call-second form.
        have hresultSafe : E.SafeFrom cfg ext trace.result
              (E.followingSlotStart cfg (n + 1)) ∧
            (trace.result ≠ trace.afterObserved →
              E.SafeFrom cfg ext trace.result (n + 1)) := by
          cases hbranch with
          | carriedUnchanged hinput hselector =>
              have hinputSafe : E.SafeFrom cfg ext trace.afterObserved
                  (n + 1) := by
                rw [hinput.input_eq, E.fcrStep_confirmed_root]
                exact hsafePreviousAtCall
              have heq : trace.result = trace.afterObserved :=
                hselector.result_eq_input cfg ext
              refine ⟨?_, fun hne => absurd heq hne⟩
              rw [heq]
              exact hinputSafe.mono cfg ext E hcallToDeadline
          | finalizedResetUnchanged hinput hselector =>
              have heq : trace.result = trace.afterObserved :=
                hselector.result_eq_input cfg ext
              refine ⟨?_, fun hne => absurd heq hne⟩
              rw [heq]
              exact E.finalizedResetCandidateInput_safeFrom_of_nextSlotSynchrony
                cfg ext B hT hacc hanchor hboundary hC.synchrony hv hHn1
                  hinput hdeadlineSlot
          | observedResetUnchanged hinput hselector =>
              have hinputSafe :=
                Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
                  (E := E) cfg ext B hT hC.synchrony hC.static_validators
                    hC.byzantine_bound hanchor hboundary hspe hv hHn1 hcall hinput
              have heq : trace.result = trace.afterObserved :=
                hselector.result_eq_input cfg ext
              refine ⟨?_, fun hne => absurd heq hne⟩
              rw [heq]
              exact hinputSafe.mono cfg ext E hcallToDeadline
          | strictSelected horigin hselector =>
              have hinputSafe : E.SafeFrom cfg ext trace.afterObserved
                  (n + 1) := by
                cases horigin with
                | carried hinput =>
                    rw [hinput.input_eq, E.fcrStep_confirmed_root]
                    exact hsafePreviousAtCall
                | finalizedReset hinput =>
                    exact E.strictFinalizedResetCandidateInput_safeFrom_anchor
                      cfg ext B hT hanchor hboundary hDelay hinput hselector
                | observedReset hinput =>
                    exact
                      Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
                        (E := E) cfg ext B hT hC.synchrony hC.static_validators
                          hC.byzantine_bound hanchor hboundary hspe hv hHn1
                            hcall hinput
              have hstrictSafe : E.SafeFrom cfg ext trace.result (n + 1) := by
                simpa only [trace] using
                  E.getLatestConfirmedTraceAt_result_safeFrom_of_acceptedDispatcher
                    cfg ext B hT hC hfit hdomain hanchor hboundary hDelay
                      hspe hpaper P V hanchorExact hv hHn1 hcall hprior
                        hinputKnown hinputSafe
              exact ⟨hstrictSafe.mono cfg ext E hcallToDeadline,
                fun _ => hstrictSafe⟩
        have hwrite : E.confirmed cfg ext v (n + 1) = trace.result := by
          simpa only [trace] using hrec.result_writeback
        refine { followingSlot := ?_, callSecond := ?_ }
        · unfold ConfirmedSafeFromFollowingSlot
          rw [hwrite]
          exact hresultSafe.1
        · intro j hj _hcallJ hne
          cases Nat.succ_injective hj
          rw [hwrite] at hne ⊢
          exact hresultSafe.2 hne
      · have hdeadlineEq : E.followingSlotStart cfg (n + 1) =
            E.followingSlotStart cfg n :=
          E.followingSlotStart_succ_eq_of_noCall cfg ext hcall
        refine { followingSlot := ?_, callSecond := ?_ }
        · unfold ConfirmedSafeFromFollowingSlot at hsafeN ⊢
          rw [E.confirmed_succ_of_no_advance cfg ext v n hcall,
            hdeadlineEq]
          exact hsafeN
        · intro j hj hcallJ _
          cases Nat.succ_injective hj
          exact absurd hcallJ hcall

/-- Every honest node's exact executable confirmed cache is safe from the
start of the following slot.

Finalized unchanged resets use synchrony at that deadline.  Strict finalized
resets reduce to the trusted anchor before the strict-helper dispatcher is
invoked.  Active observed resets use the accepted dynamic checkpoint proof.

Corollary of `…_all_le` at `k := n`; the statement is unchanged. -/
theorem confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.ConfirmedSafeFromFollowingSlot cfg ext v n :=
  fun n hHn =>
    (E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold_all_le
      cfg ext B hT hC hfit hanchor hboundary hDelay hspe hpaper P V
      n n (Nat.le_refl n) hHn v hv).followingSlot

/-- The lazy A3.2 transport's threaded input, straight off the strengthened
fold.

`PriorStrictCallWriteBackSafe n` is exactly the `callSecond` component of
`AcceptedFoldSafetyAt` at the seconds `k + 1 ≤ n`, so this is a projection, not
a new proof.  It is the object wave T3 threads down the strong dispatcher
chain to the two `currentHistorical`/late-seed consumption sites. -/
theorem priorStrictCallWriteBackSafe_of_acceptedActualFCRFold
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (n : ℕ) :
    E.PriorStrictCallWriteBackSafe cfg ext n :=
  fun i hi k hk hHk1 hcall hstrict =>
    (E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold_all_le
      cfg ext B hT hC hfit hanchor hboundary hDelay hspe hpaper P V
      n (k + 1) hk hHk1 i hi).callSecond k rfl hcall hstrict

/-- Endpoint form matching the paper's timing: a cached output is canonical
at every in-horizon honest endpoint in a strictly later slot. -/
theorem confirmed_head_of_acceptedActualFCRFold_nextSlot
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.confirmed cfg ext v n)) = true := by
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg hnm hHm
  have hsafe := E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold
    cfg ext B hT hC hfit hanchor hboundary hDelay hspe hpaper P V
      hv n hHn
  have hdeadlineLe : E.followingSlotStart cfg n ≤ m := by
    by_contra hnot
    have hmLt : m < E.followingSlotStart cfg n := Nat.lt_of_not_ge hnot
    have hslotLt := (E.slot_at_lt_iff cfg hT.whole_seconds
      (E.nextSlotFold_genesisTime_le cfg ext hT)).2 hmLt
    exact (Nat.not_lt_of_ge hnext) hslotLt
  exact hsafe w hw m hdeadlineLe hHm

end Execution

end FastConfirmation.Spec

end
