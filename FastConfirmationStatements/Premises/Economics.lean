module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Externals

@[expose] public section

/-! Defines the static validator-set and Byzantine committee-weight bounds used by the safety claim. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- The static-validator-set idealization over the verified execution segment.
The trusted genesis initialization itself seeds registry constancy
mechanically; this record carries only the horizon and activity facts that are
not consequences of `get_forkchoice_store`. -/
structure StaticValidatorSet (cfg : Config) (E : Execution Root) : Prop where
  /-- The trusted anchor itself belongs to the verified uint64 segment, so the
      public conclusion domain cannot be empty merely because the chosen
      horizon predates initialization. -/
  genesis_within_horizon : E.WithinHorizon cfg 0
  /-- Paper Assumption 1, restricted to the concrete execution segment: the
      active validator set is constant at epochs below the exclusive
      verification horizon. This places no finite upper bound on the
      execution's unbounded `ℕ` clock. -/
  activity_constant : ∀ i : ValidatorIndex, ∀ e e' : Epoch,
    e < E.verification_horizon → e' < E.verification_horizon →
      is_active_validator (E.registry.getD i default) e =
        is_active_validator (E.registry.getD i default) e'
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
      `FastConfirmationProofs/Discount/EconomicRounding.lean`. -/
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
