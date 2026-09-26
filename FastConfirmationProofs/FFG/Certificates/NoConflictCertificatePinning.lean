module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.FFG.Certificates.FFGAccountability

@[expose] public section

/-!
# No-conflict certificate pinning (paper Lemma 42)

This module proves the certificate-level meaning of the executable
`will_no_conflicting_checkpoint_be_justified` helper.

There are exactly two executable branches.  If the current target already is
the store's unrealized justified checkpoint, the common semantic FFG state
supplies a concrete certificate for that same checkpoint, and ordinary Casper
accountability pins every same-epoch certificate to it.  Otherwise the helper
commits strictly more than one third of the total weight in *honest* concrete
current-target voters.  Such a set intersects the terminal two-thirds link of
any competing same-epoch certificate; no-forgery and honest non-slashability
then rule out a different target root.

No competing-certificate absence, pinning conclusion, latest-message
provenance, or quorum is assumed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Exact lower protocol bundle used by certificate pinning.  In particular it
contains neither `JustificationInterface` nor synchrony.  The sole endpoint
domain fact is justified-root knownness, used only to keep `get_head` and the
common semantic checkpoint projection in-domain. -/
structure NoConflictPinningAssumptions (E : Execution Root) : Prop where
  genesis : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
    anchor_state.slot = anchor_block.message.slot ∧
    anchor_block.message.parent_root ≠ anchor_block.root
  wellFormed : WellFormedExecution E
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  honest_behavior : HonestBehavior cfg ext E
  externals_coherence : BeaconExternalsPremises cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineWeightPremises cfg E
  justified_root_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots



namespace Execution

variable (E : Execution Root)

/-! ## Arithmetic branch of the executable helper -/

/-- In the non-equality branch, the actual helper arithmetic puts strictly
more than one third of total active weight in the same concrete honest signer
set used by the current-target support bridge. -/
theorem noConflict_arithmeticBranch_oneThird
    (hA : NoConflictPinningAssumptions cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hne : get_current_target cfg (E.store cfg ext v n) ≠
      (E.store cfg ext v n).unrealized_justified_checkpoint)
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v n) = true) :
    E.total_active cfg < 3 * E.weight
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state) := by
  obtain ⟨hgen, hwf, hdiv, hhb, hec, hsv, hbb, _hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let store := E.store cfg ext v n
  let observedHonest := E.currentTargetObservedHonestSupporters cfg store state
  let observedNonhonest :=
    E.currentTargetObservedNonhonestSupporters cfg store state
  let futureHonest := (E.currentTargetFutureSpan cfg store).filter
    (fun i => i ∈ E.honest)
  let score := get_current_target_score cfg ext store
  let start := currentTargetEpochStart cfg store
  let finish := get_current_slot cfg store - 1
  let estimate := estimate_committee_weight_between_slots cfg
    (E.total_active cfg) start finish
  let adversarial := compute_adversarial_weight cfg ext store state start finish
  let remaining := (E.total_active cfg - estimate) / 100 *
    (100 - cfg.confirmation_byzantine_threshold)
  have hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store) := by
    rw [show get_current_slot cfg store = E.slot_at cfg n by
      exact E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hscore : score =
      E.weight observedHonest + E.weight observedNonhonest := by
    simpa only [score, observedHonest, observedNonhonest, store,
      Execution.currentTargetObservedHonestSupporters,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.current_target_score_eq_honest_add_nonhonest_weight
        cfg ext hstate hval
  have hprov := E.latestMessageProvenance cfg ext hwf hec hgen0 v n (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v n] at hprov
  have hbyz : E.weight observedNonhonest ≤ adversarial := by
    simpa only [observedNonhonest, adversarial, start, finish, store,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.currentTarget_nonhonest_weight_le_adversarial cfg ext
        hhb hec hbb hgen0 hv hnH (E.anchor_state_slot_le_slot_at cfg hdiv hgen0 n)
        hval htab hprov
  have hobserved : score - adversarial ≤
      E.weight observedHonest := by
    rw [hscore]
    apply (Nat.sub_le_iff_le_add).2
    exact Nat.add_le_add_left hbyz _
  have hfuture : remaining ≤ E.weight futureHonest := by
    simpa only [remaining, estimate, start, finish, futureHonest, store] using
      E.currentTarget_remaining_honest_le_future_weight cfg ext
        hec hsv hbb hcurrentH hendH hanchorH hfloor
  have hdisjoint : Disjoint observedHonest futureHonest := by
    simpa only [observedHonest, futureHonest, store] using
      E.currentTarget_observed_future_disjoint cfg ext hec hprov
  have hgateArithmetic := hgate
  simp only [will_no_conflicting_checkpoint_be_justified, hne, if_false,
    compute_honest_ffg_support_for_current_target,
    decide_eq_true_eq] at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  have hgateArithmetic' : E.total_active cfg <
      3 * (score - adversarial + remaining) := by
    simpa only [score, adversarial, remaining, estimate, start, finish,
      store, one_mul] using hgateArithmetic
  have hpredict : score - adversarial + remaining ≤
      E.weight observedHonest + E.weight futureHonest :=
    Nat.add_le_add hobserved hfuture
  have honeThird : E.total_active cfg <
      3 * (E.weight observedHonest + E.weight futureHonest) :=
    hgateArithmetic'.trans_le (Nat.mul_le_mul_left 3 hpredict)
  change E.total_active cfg <
    3 * E.weight (observedHonest ∪ futureHonest)
  rw [E.weight_union_disjoint hdisjoint]
  exact honeThird





/-! ## Certificate pinning -/



end Execution

end FastConfirmation.Spec

end
