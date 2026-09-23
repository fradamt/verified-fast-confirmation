module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Externals

@[expose] public section

/-! Economics declarations from FastConfirmation.Spec.Model.Assumptions. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
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
      `Proof/EconomicRounding.lean`. -/
  estimate_sound : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    E.weight (E.span_committee a b) ≤
      estimate_committee_weight_between_slots cfg (E.total_active cfg) a b
  /-- Per-span Byzantine *fraction* bound (the paper's Assumption 2 at the spec's own design point
      `β = CONFIRMATION_BYZANTINE_THRESHOLD / 100`): in every slot span's
      committee union the non-honest weight is at most `β` of the whole,
      cross-multiplied to avoid division:
      `100 · byz(span) ≤ CONFIRMATION_BYZANTINE_THRESHOLD · W(span)`. Ground
      truth, uniform over spans — no `a ≤ b` guard, empty spans are trivially
      `0 ≤ 0`; same committee-sampling concentration family as `span_bound`.
      The proof uses both per-slot (`[t,t]`) and per-window instances. -/
  span_fraction : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    100 * E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold *
        E.weight (E.span_committee a b)

end FastConfirmation.Spec

end
