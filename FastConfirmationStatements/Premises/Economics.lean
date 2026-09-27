module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Defines the Byzantine committee-weight bounds used by the safety claim.

Paper references use arXiv:2405.00549v4 (https://arxiv.org/abs/2405.00549v4).
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- The economic assumptions: the `CONFIRMATION_BYZANTINE_THRESHOLD` bound and
the committee-weight-estimation soundness — both against the ground truth,
both exactly the spec's own stated assumptions (the estimation soundness is
the "high probability" claim behind
`COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR`; see the spec's gist link). -/
structure ByzantineWeightPremises (E : Execution Root) : Prop where
  /-- Effective balances used by the economic model are phase0-quantized.
      This is an executable registry invariant, not part of the probabilistic
      committee estimate.  Out-of-range totalized reads have weight zero. -/
  effective_balance_quantized : ∀ i : ValidatorIndex,
    cfg.effective_balance_increment ∣ E.weight_of i
  /-- The spec-level high-probability committee estimate: the actual span
      weight does not exceed `estimate_committee_weight_between_slots`.
      The stronger post-`//100` inequality used by the arithmetic is derived
      from this field and effective-balance quantization in
      `FastConfirmationProofs/Discount/EconomicRounding.lean`. Committee
      sampling is idealized (class I): this field takes the estimate as
      exact, and the specification claims it only with high probability
      (`COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR`). The idealization has
      two intended parts: (i) equal slot-committee weights inside an epoch
      (with the fixed schedule and coverage,
      `EstimateForcesBalance.slot_committee_weight_forced`); (ii) a perfectly
      mixed reshuffle across an epoch boundary, so the weight of a
      cross-boundary span is at most the pro-rated estimate, which is the
      expected overlap. The statistical properties of committee sampling are
      out of scope by design. -/
  estimate_sound : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    E.weight (E.span_committee a b) ≤
      estimate_committee_weight_between_slots cfg (E.total_active cfg) a b
  /-- Non-honest weight is at most the threshold fraction of each committee
      union for every in-horizon slot span, including a one-slot span. This is
      the repository's formal paper Assumption 2, `CommitteeHonestMajority`,
      at `β = CONFIRMATION_BYZANTINE_THRESHOLD / 100`:
      `100 · byz(span) ≤ CONFIRMATION_BYZANTINE_THRESHOLD · W(span)`.
      A global fault share does not establish this bound for each span.
      There is no `a ≤ b` guard; an empty span gives `0 ≤ 0`. The proofs use
      one-slot and longer-span instances. -/
  span_fraction : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    100 * E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold *
        E.weight (E.span_committee a b)

end FastConfirmation.Spec

end
