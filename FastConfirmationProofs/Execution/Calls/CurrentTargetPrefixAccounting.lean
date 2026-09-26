module
public import FastConfirmationProofs.Execution.History.CausalQueryTraceAdapter
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport

@[expose] public section

/-!
# Current-target accounting at an exact scheduled prefix

The existing current-target gate accounting theorem is stated at a completed
`Execution.store`.  An allowed FCR query may instead read an exact strict
`ScheduledEventPrefix`.  This file isolates the one additional safety-free
adapter fact needed to replay the same arithmetic there: committees computed
from the prefix head state agree with the ground-truth execution committees.

All other store facts used below (causality, exact current slot, ordinary
latest-message provenance, and exclusion of honest equivocators) are fields
of `ScheduledPrefixOperationalEvidence`, hence are derived by replaying the
actual prefix.  No target agreement, quorum, certificate, ancestry, endpoint,
or safety conclusion is included in the adapter.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- Committee readback at an exact query store.  `BeaconExternalsPremises` exposes
this equality only for completed `Execution.store` boundaries; strict
scheduled prefixes need the same implementation-coherence fact explicitly.
-/
def PrefixCommitteeAgreement (store : Store Root) : Prop :=
  ∀ slot : Slot, E.SlotWithinHorizon cfg slot →
    get_slot_committee cfg ext store slot = E.committee slot



/-- The safety-free accounting projection of one exact scheduled-prefix
query.  The first field is produced by `ScheduledEventPrefix`; the second is
the required strict-prefix specialization of committee coherence.
-/
structure CurrentTargetPrefixAccountingEvidence
    (store : Store Root) (querySecond : ℕ) : Prop where
  operational : E.ScheduledPrefixOperationalEvidence cfg ext store querySecond
  committees : E.PrefixCommitteeAgreement cfg ext store

omit [LinearOrder Root] [Inhabited Root] in
private theorem prefix_byz_le_net_of_add
    {byz equiv budget : ℕ} (hbudget : byz + equiv ≤ budget) :
    byz ≤ if budget > equiv then budget - equiv else 0 := by
  split_ifs <;> omega

/-- Store-generic equivocation-score readback.  This is the completed-boundary
theorem `get_equivocation_score_eq_weight` with its only boundary-specific
step, committee equality, made explicit.
-/
theorem get_equivocation_score_eq_weight_of_prefix
    {store : Store Root}
    (hcommittees : E.PrefixCommitteeAgreement cfg ext store)
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    (sa es : Slot) (hesH : E.SlotWithinHorizon cfg es) :
    get_equivocation_score cfg ext store bs sa es =
      E.weight (EquivActive cfg E store bs sa es) := by
  have hce : (Finset.Icc sa es).biUnion
        (fun slot => get_slot_committee cfg ext store slot) =
      (Finset.Icc sa es).biUnion E.committee := by
    apply Finset.biUnion_congr rfl
    intro slot hslot
    exact hcommittees slot
      ⟨(Finset.mem_Icc.mp hslot).2.trans hesH.1,
        lt_of_le_of_lt
          (Nat.div_le_div_right (Finset.mem_Icc.mp hslot).2) hesH.2⟩
  simp only [get_equivocation_score, EquivActive, Execution.weight,
    Execution.weight_of, Execution.span_committee, hce]
  exact Finset.sum_congr rfl (fun i _ => by rw [hval])

/-- At an exact scheduled-prefix query, non-honest current-target score
contributors plus active equivocators fit the elapsed-epoch Byzantine budget.
The proof uses only operational prefix evidence and committee readback.
-/
theorem currentTarget_nonhonest_add_equiv_le_budget_of_prefix
    (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root} {querySecond : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext store
      querySecond)
    (hqH : E.WithinHorizon cfg querySecond)
    {state : BeaconState Root}
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg) :
    E.weight (((CurrentTargetSupporters cfg store state).filter
        (fun i => i ∉ E.honest)).toFinset) +
      get_equivocation_score cfg ext store state
        (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
        (get_current_slot cfg store - 1) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg state)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg store))
          (get_current_slot cfg store - 1) /
            100 * cfg.confirmation_byzantine_threshold := by
  let start := compute_start_slot_at_epoch cfg
    (get_current_store_epoch cfg store)
  let finish := get_current_slot cfg store - 1
  have hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store) := by
    rw [hevidence.operational.current_slot]
    exact ⟨hqH.2.1, hqH.2.2⟩
  have hstartLe : start ≤ get_current_slot cfg store := by
    simp only [start, compute_start_slot_at_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_mul_le_self _ _
  have hstartH : E.SlotWithinHorizon cfg start :=
    ⟨hstartLe.trans hcurrentH.1,
      by
        simp only [start, compute_start_slot_at_epoch,
          get_current_store_epoch, compute_epoch_at_slot]
        calc
          get_current_slot cfg store / cfg.slots_per_epoch *
                cfg.slots_per_epoch / cfg.slots_per_epoch =
              get_current_slot cfg store / cfg.slots_per_epoch := by
            rw [Nat.mul_comm]
            exact Nat.mul_div_cancel_left _ cfg.slots_per_epoch_pos
          _ < E.verification_horizon := by
            simpa only [compute_epoch_at_slot] using hcurrentH.2⟩
  have hfinishH : E.SlotWithinHorizon cfg finish :=
    ⟨(Nat.sub_le _ _).trans hcurrentH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurrentH.2⟩
  rw [E.get_equivocation_score_eq_weight_of_prefix cfg ext
    hevidence.committees hval start finish hfinishH, htab]
  let BS := ((CurrentTargetSupporters cfg store state).filter
    (fun i => i ∉ E.honest)).toFinset
  let EA := EquivActive cfg E store state start finish
  refine (E.weight_add_le ?_ ?_ ?_).trans
    (hbb.span_bound start finish hstartH hfinishH)
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨_hactive, _hunslashed, _lm, _hlm, hnotEquiv, _htarget⟩ :=
      mem_CurrentTargetSupporters cfg hiBS.1
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnotEquiv hiEA.1.2
  · intro i hi
    simp only [List.mem_toFinset, List.mem_filter] at hi
    have hnonhonest : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr
      ⟨E.currentTargetSupporter_mem_elapsed_span cfg
          hevidence.operational.latest_message_provenance hi.1,
        hnonhonest⟩
  · intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    have hnonhonest : i ∉ E.honest := by
      intro hhonest
      exact hevidence.operational.honest_not_equivocating i hhonest hi.1.2
    exact Finset.mem_filter.mpr
      ⟨hi.1.1, hnonhonest⟩

/-- The actual non-honest score contribution at a scheduled prefix is bounded
by the helper's post-equivocation adversarial budget.
-/
theorem currentTarget_nonhonest_weight_le_adversarial_of_prefix
    (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root} {querySecond : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext store
      querySecond)
    (hqH : E.WithinHorizon cfg querySecond)
    {state : BeaconState Root}
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg) :
    E.weight (((CurrentTargetSupporters cfg store state).filter
        (fun i => i ∉ E.honest)).toFinset) ≤
      compute_adversarial_weight cfg ext store state
        (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
        (get_current_slot cfg store - 1) := by
  have hbudget :=
    E.currentTarget_nonhonest_add_equiv_le_budget_of_prefix cfg ext hbb
      hevidence hqH hval htab
  let byz := E.weight
    (((CurrentTargetSupporters cfg store state).filter
      (fun i => i ∉ E.honest)).toFinset)
  let equiv := get_equivocation_score cfg ext store state
    (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
    (get_current_slot cfg store - 1)
  let budget := estimate_committee_weight_between_slots cfg
    (get_total_active_balance cfg state)
    (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
    (get_current_slot cfg store - 1) /
      100 * cfg.confirmation_byzantine_threshold
  change byz ≤ if budget > equiv then budget - equiv else 0
  change byz + equiv ≤ budget at hbudget
  exact prefix_byz_le_net_of_add hbudget

/-- The executable current-target gate has exactly the same honest
two-thirds consequence at an exact strict scheduled prefix as at a completed
execution boundary.  The signer set is the concrete support set computed from
that query store; it is not an arbitrary or supplied set.
-/
theorem will_current_target_be_justified_honest_quorum_of_prefix
    (hec : BeaconExternalsPremises cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root} {querySecond : ℕ}
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext store
      querySecond)
    (hqH : E.WithinHorizon cfg querySecond)
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext store)
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext store = true) :
    2 * E.total_active cfg ≤
      3 * E.weight (E.currentTargetA32Signers cfg store state) := by
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
    rw [hevidence.operational.current_slot]
    exact ⟨hqH.2.1, hqH.2.2⟩
  have hscore : score =
      E.weight observedHonest + E.weight observedNonhonest := by
    simpa only [score, observedHonest, observedNonhonest,
      Execution.currentTargetObservedHonestSupporters,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.current_target_score_eq_honest_add_nonhonest_weight cfg ext hstate hval
  have hbyz : E.weight observedNonhonest ≤ adversarial := by
    simpa only [observedNonhonest, adversarial, start, finish,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.currentTarget_nonhonest_weight_le_adversarial_of_prefix cfg ext hbb
        hevidence hqH hval htab
  have hobserved : score - adversarial ≤
      E.weight observedHonest := by
    rw [hscore]
    apply (Nat.sub_le_iff_le_add).2
    exact Nat.add_le_add_left hbyz _
  have hfuture : remaining ≤ E.weight futureHonest := by
    simpa only [remaining, estimate, start, finish, futureHonest] using
      E.currentTarget_remaining_honest_le_future_weight cfg ext
        hec hsv hbb hcurrentH hendH hanchorH hfloor
  have hdisjoint : Disjoint observedHonest futureHonest := by
    simpa only [observedHonest, futureHonest] using
      E.currentTarget_observed_future_disjoint cfg ext
        hec hevidence.operational.latest_message_provenance
  have hgateArithmetic := hgate
  simp only [will_current_target_be_justified,
    compute_honest_ffg_support_for_current_target, decide_eq_true_eq]
      at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  change 2 * E.total_active cfg ≤
    3 * (score - adversarial + remaining) at hgateArithmetic
  have hpredict : score - adversarial + remaining ≤
      E.weight observedHonest + E.weight futureHonest :=
    Nat.add_le_add hobserved hfuture
  have hquorum : 2 * E.total_active cfg ≤
      3 * (E.weight observedHonest + E.weight futureHonest) :=
    hgateArithmetic.trans (Nat.mul_le_mul_left 3 hpredict)
  change 2 * E.total_active cfg ≤
    3 * E.weight (observedHonest ∪ futureHonest)
  rw [E.weight_union_disjoint hdisjoint]
  exact hquorum

end Execution

namespace AllowedFCRCalls

open Execution


end AllowedFCRCalls

/-! ## Standalone contract non-vacuity -/

namespace ScheduledPrefixCommitteeCoherenceNonvacuity













end ScheduledPrefixCommitteeCoherenceNonvacuity


end FastConfirmation.Spec

end
