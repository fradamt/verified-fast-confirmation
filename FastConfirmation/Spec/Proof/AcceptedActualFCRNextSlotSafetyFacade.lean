module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRNextSlotSafetyFold

@[expose] public section

/-!
# Accepted actual-FCR next-slot safety facade

This module proves following-slot safety for stored FCR outputs without
placing a reset law in the accepted assumption bundle.  Finalized and
active-observed restart safety are both derived from the accepted execution
dynamics.

The property says directly that a stored output at second `n` is canonical at
every in-horizon honest
endpoint whose slot is at least `slot_at n + 1`.

The theorem covers stored outputs at completed execution boundaries. It does
not cover optional calls at arbitrary in-slot action prefixes.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Assumptions for the stored-output following-slot theorem.

There is deliberately no finalized-reset, observed-adoption, observed-lock,
head-ancestry, filter-result, or safety field.  Finalized next-slot safety and
active-observed restart safety are already derived by the fold. -/
structure AcceptedActualFCRNextSlotSafetyAssumptions where
  semantics : ExactPrefixAcceptedFFGSemantics cfg ext E
  trajectory : E.ScheduledPrefixTrajectoryAssumptions cfg ext
  completed_calls :
    E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  anchor_eq : semantics.anchor = E.genesis_store.justified_checkpoint
  anchor_boundary : TrustedAnchorBoundaryAligned (cfg := cfg)
    (E := E) (anchor := semantics.anchor)
  finalization_delay :
    E.AcceptedRealizedFinalizationDelay cfg ext semantics
  slots_per_epoch_gt_one : 1 < cfg.slots_per_epoch
  paper_a32 : semantics.state.PaperA32Inclusion cfg ext
  checkpoint_projection : AcceptedEpochCheckpointProjection
    semantics.anchor (E.AcceptedRoot cfg ext) semantics.state.C
  exact_link_validity : semantics.state.ExactLinkValidity

namespace AcceptedActualFCRNextSlotSafetyAssumptions

/-- Bundle-facing following-slot invariant. -/
theorem confirmed_safeFromFollowingSlot
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    E.ConfirmedSafeFromFollowingSlot cfg ext v n := by
  exact E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold
    cfg ext h.semantics h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.paper_a32 h.checkpoint_projection
      h.exact_link_validity hv n hHn

/-- Bundle-facing form of the strengthened fold invariant.

`AcceptedFoldSafetyAt` bundles the following-slot invariant with the
*unweakened* call-second safety of a strictly advanced write-back; the fold
proves it at every second, so no `k ≤ n` binder survives here.  This is the
form the lazy A3.2 origin-call transport consumes at an earlier crossing call
(`docs/trunkA-final-discharge.md` §5.3). -/
theorem foldSafetyAt
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    E.AcceptedFoldSafetyAt cfg ext v n :=
  E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold_all_le
    cfg ext h.semantics h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.paper_a32 h.checkpoint_projection
      h.exact_link_validity n n (Nat.le_refl n) hHn v hv

/-- Unweakened safety of the root a call at second `n` writes back, when that
call's selector strictly advanced.

At a call `E.slot_start_eq_succ_of_advance_minimal` gives
`slot_start (slot_at (n + 1)) = n + 1`, so this is exactly the
`slot_start`-indexed input of
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` at the crossing
call.  Strictness is supplied at an A3.2 crossing by
`StrictSelectorAdvanceAt.result_ne_input`. -/
theorem confirmed_safeFrom_strictCallSecond
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstrict : E.confirmed cfg ext v (n + 1) ≠
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved) :
    E.SafeFrom cfg ext (E.confirmed cfg ext v (n + 1)) (n + 1) :=
  (h.foldSafetyAt cfg ext E hv hHn1).callSecond n rfl hcall hstrict

/-- Bundle-facing form of the threaded lazy-transport input. -/
theorem priorStrictCallWriteBackSafe
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) (n : ℕ) :
    E.PriorStrictCallWriteBackSafe cfg ext n :=
  E.priorStrictCallWriteBackSafe_of_acceptedActualFCRFold
    cfg ext h.semantics h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.paper_a32 h.checkpoint_projection
      h.exact_link_validity n

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1400000 in
-- The dependent dispatcher elaborates all executable input/reset origins here.
/-- Reset-free form of the mandatory descendant-helper guarantee.

At an actual boundary call, the preceding cached root is already safe at the
call boundary by the following-slot invariant.  A selector-eligible finalized
reset is forced to the trusted anchor by causal finalization lag, and an
observed reset is safe by the accepted dynamic checkpoint theorem.  The
accepted dispatcher then proves the literal helper return safe, including the
case where the helper runs but returns its input unchanged. -/
theorem findLatestConfirmedDescendant_safeFrom_of_actualCall
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
      (n + 1) := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hselectorTrace : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      trace.afterObserved := by
    simpa only [trace] using hselector
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hdomain : SelectedMarginDomain cfg ext E :=
    E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext h.semantics h.trajectory h.completed_calls.synchrony
        h.anchor_eq h.anchor_boundary
  have hanchorExact : h.semantics.anchor =
      h.semantics.state.C h.semantics.anchor.root h.semantics.anchor.epoch :=
    acceptedAnchorExact_of_trajectory cfg ext E h.semantics h.trajectory
      h.anchor_eq h.anchor_boundary
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := h.trajectory.genesis_structure
      wellFormed := h.trajectory.wellFormed
      whole_seconds := h.trajectory.whole_seconds
      honest_behavior := h.trajectory.honest_behavior
      synchrony := h.completed_calls.synchrony
      externals_coherence := h.trajectory.externals_coherence
      static_validators := h.completed_calls.static_validators
      byzantine_bound := h.completed_calls.byzantine_bound
      domain := hdomain }
  have hpreviousDeadline : E.followingSlotStart cfg n = n + 1 :=
    E.followingSlotStart_eq_succ_of_call
      cfg ext h.trajectory hMargin hHn1 hcall
  have hsafePreviousAtCall : E.SafeFrom cfg ext
      (E.confirmed cfg ext v n) (n + 1) := by
    have hsafePrevious :=
      h.confirmed_safeFromFollowingSlot cfg ext E hv hHn
    simpa only [ConfirmedSafeFromFollowingSlot, hpreviousDeadline] using
      hsafePrevious
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots :=
    E.confirmed_known_of_acceptedGlobalTrajectory
      cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary hv n hHn
  have hinputKnown : trace.afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    simpa only [trace] using
      E.getLatestConfirmedTraceAt_input_known
        cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary hknownN
  have hbranch : CandidateHistoryCallBranch cfg ext
      (E.fcrStep cfg ext v n) trace := by
    simpa only [trace] using hrec.branch
  have hinputSafe : E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
    cases hbranch with
    | carriedUnchanged hinput _ =>
        rw [hinput.input_eq, E.fcrStep_confirmed_root]
        exact hsafePreviousAtCall
    | finalizedResetUnchanged hinput _ =>
        exact E.finalizedResetCandidateInput_safeFrom_anchor_of_recent
          cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary
            h.finalization_delay hinput hselectorTrace
    | observedResetUnchanged hinput _ =>
        exact
          Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
            (E := E) cfg ext h.semantics h.trajectory
              h.completed_calls.synchrony h.completed_calls.static_validators
                h.completed_calls.byzantine_bound h.anchor_eq h.anchor_boundary
                  h.slots_per_epoch_gt_one hv hHn1 hcall hinput
    | strictSelected horigin _ =>
        cases horigin with
        | carried hinput =>
            rw [hinput.input_eq, E.fcrStep_confirmed_root]
            exact hsafePreviousAtCall
        | finalizedReset hinput =>
            exact E.finalizedResetCandidateInput_safeFrom_anchor_of_recent
              cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary
                h.finalization_delay hinput hselectorTrace
        | observedReset hinput =>
            exact
              Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
                (E := E) cfg ext h.semantics h.trajectory
                  h.completed_calls.synchrony
                    h.completed_calls.static_validators
                      h.completed_calls.byzantine_bound h.anchor_eq
                        h.anchor_boundary h.slots_per_epoch_gt_one hv hHn1
                          hcall hinput
  have hresultSafe : E.SafeFrom cfg ext trace.result (n + 1) := by
    simpa only [trace] using
      E.getLatestConfirmedTraceAt_result_safeFrom_of_acceptedDispatcher
        cfg ext h.semantics h.trajectory h.completed_calls h.epoch_ends_fit
          hdomain h.anchor_eq h.anchor_boundary h.finalization_delay
            h.slots_per_epoch_gt_one h.paper_a32 h.checkpoint_projection
              h.exact_link_validity hanchorExact hv hHn1 hcall
                (h.priorStrictCallWriteBackSafe cfg ext E n) hinputKnown
                  hinputSafe
  have hselected : trace.result =
      find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v n)
        trace.afterObserved :=
    trace.selected_facts cfg ext hselectorTrace
  rw [hselected] at hresultSafe
  simpa only [trace] using hresultSafe

/-- Bundle-facing endpoint form with the literal next-slot timing premise. -/
theorem confirmed_head_nextSlot
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.confirmed cfg ext v n)) = true := by
  exact E.confirmed_head_of_acceptedActualFCRFold_nextSlot
    cfg ext h.semantics h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.paper_a32 h.checkpoint_projection
      h.exact_link_validity hv hw hnm hnext hHm

end AcceptedActualFCRNextSlotSafetyAssumptions

end Execution

/-- Accepted whole-output safety with the same endpoint quantifiers and timing
as `Spec_Safety_next_slot`, under the accepted executable-semantics bundle.

The global `PaperSafetySynchrony` inside `completed_calls` makes this the
current model's GST-0 specialization. Its three fields are honest-attestation
delivery, block relay, and equivocation-evidence relay; it does not require the
additional `latest_message_relay` premise of the full `Synchrony` bundle. -/
def AcceptedSpec_Safety_next_slot : Prop :=
  ∀ E : Execution Root,
    E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
          E.WithinHorizon cfg m →
            is_ancestor (E.store cfg ext w m)
              (get_head cfg (E.store cfg ext w m))
              (get_node_for_root (E.confirmed cfg ext v n)) = true

/-- Stored-output safety theorem at the following-slot deadline. -/
theorem acceptedSpec_safety_next_slot :
    AcceptedSpec_Safety_next_slot cfg ext := by
  intro E h v hv n w hw m hnm hnext hHm
  exact h.confirmed_head_nextSlot cfg ext E hv hw hnm hnext hHm

end FastConfirmation.Spec

end
