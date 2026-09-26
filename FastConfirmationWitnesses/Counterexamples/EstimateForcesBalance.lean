module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetFutureSupport

@[expose] public section

/-! r4 cold review: the premise bundle forces every slot committee of a full
in-horizon epoch to weigh exactly `total_active / SLOTS_PER_EPOCH`.
Only `estimate_sound` (one-slot spans), `committee_coverage`,
`activity_constant`, and the balance floor are used. -/

namespace FastConfirmation.Spec
namespace EstimateForcesBalance
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

private theorem one_slot_estimate (hspe : 1 < cfg.slots_per_epoch) (tab : Gwei) (s : Slot) :
    estimate_committee_weight_between_slots cfg tab s s = tab / cfg.slots_per_epoch := by
  have hcov : is_full_validator_set_covered cfg s s = false := by
    simp only [is_full_validator_set_covered, compute_epoch_at_slot,
      decide_eq_false_iff_not, not_lt]
    exact Nat.div_le_div_right (by omega)
  simp [estimate_committee_weight_between_slots, hcov]

private theorem weight_union_le (E : Execution Root) (A B : Finset ValidatorIndex) :
    E.weight (A ∪ B) ≤ E.weight A + E.weight B := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := E.weight_of)
  unfold Execution.weight
  exact (Nat.le_add_right _ _).trans h.le

private theorem weight_biUnion_le (E : Execution Root) (I : Finset Slot) :
    E.weight (I.biUnion E.committee) ≤ ∑ t ∈ I, E.weight (E.committee t) := by
  induction I using Finset.induction_on with
  | empty => simp [Execution.weight]
  | insert a I ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (weight_union_le E _ _).trans (Nat.add_le_add_left ih _)

private theorem epoch_mem_Icc {e t : ℕ} (hS : 0 < cfg.slots_per_epoch)
    (ht : compute_epoch_at_slot cfg t = e) :
    t ∈ Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := by
  simp only [compute_epoch_at_slot] at ht
  have hlo := Nat.div_mul_le_self t cfg.slots_per_epoch
  have hhi := Nat.lt_mul_div_succ t hS
  rw [ht] at hlo hhi
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at hhi
  apply Finset.mem_Icc.mpr
  generalize e * cfg.slots_per_epoch = P at *
  omega

private theorem last_epoch (e : ℕ) (hS : 0 < cfg.slots_per_epoch) :
    compute_epoch_at_slot cfg (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le
  · exact Nat.le_add_right _ _
  · rw [Nat.add_mul, one_mul]; omega

/-- Exact in-horizon estimate soundness and committee coverage force each
slot committee to equal the per-slot estimate. This limits the public
safety bundle to registries with perfectly balanced slot weights. -/
theorem slot_committee_weight_forced
    (E : Execution Root)
    (hec : BeaconExternalsPremises cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hspe : 1 < cfg.slots_per_epoch)
    (hfloor : cfg.effective_balance_increment ≤ E.weight (E.anchorActiveValidators cfg))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (e : Epoch)
    (hlastH : E.SlotWithinHorizon cfg (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)))
    (s : Slot)
    (hs : s ∈ Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))) :
    E.weight (E.committee s) = E.total_active cfg / cfg.slots_per_epoch := by
  have hS := cfg.slots_per_epoch_pos
  have slotH : ∀ t ∈ Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)), E.SlotWithinHorizon cfg t := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    exact ⟨ht'.2.trans hlastH.1, (Nat.div_le_div_right ht'.2).trans_lt hlastH.2⟩
  have hle : ∀ t ∈ Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)),
      E.weight (E.committee t) ≤ E.total_active cfg / cfg.slots_per_epoch := by
    intro t ht
    have h := hbb.estimate_sound t t (slotH t ht) (slotH t ht)
    rw [one_slot_estimate cfg hspe] at h
    simpa [Execution.span_committee] using h
  have heH : e < E.verification_horizon := by
    have h := hlastH.2
    rwa [last_epoch cfg e hS] at h
  have hsub : E.anchorActiveValidators cfg ⊆ (Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))).biUnion E.committee := by
    intro i hi
    rw [Execution.anchorActiveValidators, List.mem_toFinset] at hi
    have hactA : is_active_validator (E.registry.getD i default)
        (get_current_epoch cfg E.anchor_state) = true := by
      simpa only [Execution.registry] using (List.mem_filter.mp hi).2
    have hactE : is_active_validator (E.registry.getD i default) e = true := by
      rw [hsv.activity_constant i e _ heH hanchorH]; exact hactA
    obtain ⟨t, _htH, htE, hit⟩ := hec.committee_coverage i e heH hactE
    exact Finset.mem_biUnion.mpr ⟨t, epoch_mem_Icc cfg hS htE, hit⟩
  have htotal : E.total_active cfg = E.weight (E.anchorActiveValidators cfg) :=
    Execution.total_active_eq_anchorActive_weight cfg E hfloor
  have hsum_ge : E.total_active cfg ≤ ∑ t ∈ Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)), E.weight (E.committee t) := by
    rw [htotal]
    exact (Finset.sum_le_sum_of_subset hsub).trans (weight_biUnion_le E _)
  have hcard : (Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))).card = cfg.slots_per_epoch := by
    rw [Nat.card_Icc]; omega
  have hqle : cfg.slots_per_epoch * (E.total_active cfg / cfg.slots_per_epoch) ≤
      E.total_active cfg := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  apply le_antisymm (hle s hs)
  by_contra hlt
  push Not at hlt
  have hlt'' := Finset.sum_lt_sum (s := Finset.Icc (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)))
    (f := fun t => E.weight (E.committee t))
    (g := fun _ => E.total_active cfg / cfg.slots_per_epoch) hle ⟨s, hs, hlt⟩
  rw [Finset.sum_const, hcard, smul_eq_mul] at hlt''
  exact lt_irrefl _ (hsum_ge.trans_lt (hlt''.trans_le hqle))


end EstimateForcesBalance
end FastConfirmation.Spec

end
