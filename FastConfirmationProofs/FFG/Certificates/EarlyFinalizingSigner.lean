module
public import FastConfirmationProofs.FFG.Certificates.FFGCertificates
public import FastConfirmationProofs.Discount.CommitteeWindowWeight
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-! A certificate has an honest signer before the final slot of its target epoch. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

namespace Execution

variable {E : Execution Root}

private theorem early_signer_arithmetic {W D S b l q p : ℕ}
    (hW : 0 < W) (hS : 1 < S) (hQ : 2 * W ≤ 3 * q)
    (hweight : q ≤ b + l) (hB : 100 * b ≤ 25 * p)
    (hL : l ≤ D) (hdivision : D * S ≤ W)
    (hproduct : p + D = D * S) : False := by
  have htwo : 2 * D ≤ D * S := by nlinarith
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- A two-thirds quorum cannot consist only of one slot's committee and
Byzantine validators from the preceding slots. Each slot has at most its
equal share of total weight, and the preceding span has at most 25 percent
Byzantine weight. -/
theorem quorum_has_honest_in_prefix
    {earlier last signers : Finset ValidatorIndex}
    (hspe : 1 < cfg.slots_per_epoch)
    (hsub : signers ⊆ earlier ∪ last)
    (hprefix : E.weight earlier ≤
      E.total_active cfg / cfg.slots_per_epoch * (cfg.slots_per_epoch - 1))
    (hlast : E.weight last ≤ E.total_active cfg / cfg.slots_per_epoch)
    (hbyz : 100 * E.weight (earlier.filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold * E.weight earlier)
    (hquorum : 2 * E.total_active cfg ≤ 3 * E.weight signers) :
    ∃ i ∈ signers, i ∈ earlier ∧ i ∈ E.honest := by
  classical
  by_contra hnone
  push Not at hnone
  have hsigners : signers ⊆
      earlier.filter (fun i => i ∉ E.honest) ∪ last := by
    intro i hi
    rcases Finset.mem_union.mp (hsub hi) with hp | hl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hp, hnone i hi hp⟩)
    · exact Finset.mem_union_right _ hl
  have hweight : E.weight signers ≤
      E.weight (earlier.filter (fun i => i ∉ E.honest)) + E.weight last :=
    (weight_mono hsigners).trans (weight_union_le _ _)
  have hbyz' : 100 * E.weight (earlier.filter (fun i => i ∉ E.honest)) ≤
      25 * (E.total_active cfg / cfg.slots_per_epoch *
        (cfg.slots_per_epoch - 1)) :=
    hbyz.trans (Nat.mul_le_mul cfg.confirmation_byzantine_threshold_le hprefix)
  have hdivision : E.total_active cfg / cfg.slots_per_epoch *
      cfg.slots_per_epoch ≤ E.total_active cfg := Nat.div_mul_le_self _ _
  have hpositive := E.total_active_pos cfg
  have hslotSum : cfg.slots_per_epoch - 1 + 1 = cfg.slots_per_epoch := by omega
  have hproduct : E.total_active cfg / cfg.slots_per_epoch *
      (cfg.slots_per_epoch - 1) + E.total_active cfg / cfg.slots_per_epoch =
      E.total_active cfg / cfg.slots_per_epoch * cfg.slots_per_epoch := by
    rw [← Nat.mul_add_one, hslotSum]
  exact early_signer_arithmetic hpositive hspe hquorum hweight hbyz'
    hlast hdivision hproduct

/-- A proper initial part of an epoch has its exact same-epoch estimate. -/
private theorem estimate_epoch_prefix (tab e k : ℕ)
    (hk : k + 1 < cfg.slots_per_epoch) :
    estimate_committee_weight_between_slots cfg tab
      (e * cfg.slots_per_epoch) (e * cfg.slots_per_epoch + k) =
        tab / cfg.slots_per_epoch * (k + 1) := by
  have hS := cfg.slots_per_epoch_pos
  have hdiv (j : ℕ) (hj : j < cfg.slots_per_epoch) :
      (e * cfg.slots_per_epoch + j) / cfg.slots_per_epoch = e := by
    rw [Nat.mul_comm e cfg.slots_per_epoch, Nat.mul_add_div hS,
      Nat.div_eq_of_lt hj, Nat.add_zero]
  have hcovered : is_full_validator_set_covered cfg
      (e * cfg.slots_per_epoch) (e * cfg.slots_per_epoch + k) = false := by
    simp only [is_full_validator_set_covered, compute_epoch_at_slot,
      decide_eq_false_iff_not]
    rw [hdiv _ (by omega), Nat.add_assoc, hdiv _ hk]
    exact Nat.lt_irrefl e
  simp only [estimate_committee_weight_between_slots, Nat.not_lt_of_ge
    (Nat.le_add_right (e * cfg.slots_per_epoch) k), ↓reduceIte,
    hcovered, Bool.false_eq_true]
  have hepoch : compute_epoch_at_slot cfg (e * cfg.slots_per_epoch) =
      compute_epoch_at_slot cfg (e * cfg.slots_per_epoch + k) := by
    simp only [compute_epoch_at_slot, hdiv k (by omega)]
    simp [hS]
  rw [if_pos hepoch]
  simp

private theorem estimate_epoch_last (tab e : ℕ)
    (hspe : 1 < cfg.slots_per_epoch) :
    estimate_committee_weight_between_slots cfg tab
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) =
        tab / cfg.slots_per_epoch := by
  have hS := cfg.slots_per_epoch_pos
  let last : ℕ := e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)
  have hsum : cfg.slots_per_epoch - 1 + 1 = cfg.slots_per_epoch := by omega
  have hstart : (last + (cfg.slots_per_epoch - 1)) / cfg.slots_per_epoch = e + 1 := by
    have heq : last + (cfg.slots_per_epoch - 1) =
        (e + 1) * cfg.slots_per_epoch + (cfg.slots_per_epoch - 2) := by
      dsimp only [last]
      rw [Nat.add_mul, one_mul]
      omega
    rw [heq]
    simp [Nat.add_div, Nat.div_eq_of_lt (show cfg.slots_per_epoch - 2 <
      cfg.slots_per_epoch by omega), hS]
  have hend : (last + 1) / cfg.slots_per_epoch = e + 1 := by
    dsimp only [last]
    rw [Nat.add_assoc, hsum, ← Nat.add_one_mul]
    simp [hS]
  have hcovered : is_full_validator_set_covered cfg last last = false := by
    simp only [is_full_validator_set_covered, compute_epoch_at_slot, hstart, hend]
    simp
  change estimate_committee_weight_between_slots cfg tab last last = _
  simp [estimate_committee_weight_between_slots, hcovered]

/-- The public committee bounds force an honest certificate signer into a
slot strictly before the final slot of the certificate's target epoch. -/
theorem supermajority_honest_signer_before_last_slot
    (hbyz : ByzantineWeightPremises cfg E)
    (hspe : 1 < cfg.slots_per_epoch)
    {e : Epoch} {signers : Finset ValidatorIndex}
    (hfirstH : E.SlotWithinHorizon cfg (e * cfg.slots_per_epoch))
    (hlastH : E.SlotWithinHorizon cfg
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)))
    (hsub : signers ⊆ E.span_committee (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)))
    (hquorum : 2 * E.total_active cfg ≤ 3 * E.weight signers) :
    ∃ i ∈ signers, i ∈ E.honest ∧ ∃ s,
      e * cfg.slots_per_epoch ≤ s ∧
      s < e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) ∧
      i ∈ E.committee s := by
  let first : ℕ := e * cfg.slots_per_epoch
  let last : ℕ := first + (cfg.slots_per_epoch - 1)
  have hlastPos : 0 < last := by dsimp only [last]; omega
  have hprevious : last - 1 = first + (cfg.slots_per_epoch - 2) := by
    dsimp only [last]; omega
  have hpreviousH : E.SlotWithinHorizon cfg (last - 1) := by
    exact ⟨(Nat.sub_le last 1).trans hlastH.1,
      (Nat.div_le_div_right (Nat.sub_le last 1)).trans_lt hlastH.2⟩
  have hprefixWeight := hbyz.estimate_sound first (last - 1) hfirstH hpreviousH
  rw [hprevious, estimate_epoch_prefix cfg _ e (cfg.slots_per_epoch - 2)
    (by omega)] at hprefixWeight
  have hcount : cfg.slots_per_epoch - 2 + 1 = cfg.slots_per_epoch - 1 := by omega
  rw [hcount] at hprefixWeight
  rw [← hprevious] at hprefixWeight
  have hlastWeight := hbyz.estimate_sound last last hlastH hlastH
  rw [estimate_epoch_last cfg _ e hspe] at hlastWeight
  obtain ⟨i, hi, hiEarlier, hiHonest⟩ := E.quorum_has_honest_in_prefix cfg hspe
    (hsub.trans (span_committee_subset_union first last last)) hprefixWeight
    hlastWeight (hbyz.span_fraction first (last - 1) hfirstH hpreviousH) hquorum
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiEarlier
  obtain ⟨s, ⟨hfirst, hbefore⟩, hiSlot⟩ := hiEarlier
  exact ⟨i, hi, hiHonest, s, hfirst,
    hbefore.trans_lt (Nat.sub_lt hlastPos (by decide)), hiSlot⟩

end Execution

namespace IncludedSupermajorityLink

/-- The early honest signer has a genuine deadline-bounded vote. Inclusion
fixes its epoch, committee uniqueness fixes its slot, and vote-head behavior
fixes the attestation and its in-horizon creation second. -/
theorem honest_vote_before_last_slot
    {ext : BeaconFunctionInterface Root} {E : Execution Root}
    (I : Execution.BlockAttestationInclusion cfg E)
    (hhb : HonestBehavior cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hspe : 1 < cfg.slots_per_epoch)
    {carrier : Root} {source target : Checkpoint Root}
    (L : IncludedSupermajorityLink cfg E I.Included carrier source target)
    (hs0 : E.slot_at cfg 0 ≤ target.epoch * cfg.slots_per_epoch) :
    ∃ (i : ValidatorIndex) (s k : ℕ) (index : CommitteeIndex),
      i ∈ E.honest ∧ E.WithinHorizon cfg k ∧ E.slot_at cfg k = s ∧
      target.epoch * cfg.slots_per_epoch ≤ s ∧
      s < target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) ∧
      E.vote i s = some (k,
        honest_attestation cfg ext (E.store cfg ext i k) s index i) ∧
      k ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 ∧
      CheckpointReadsAs (honest_attestation cfg ext (E.store cfg ext i k) s index i
        ).data.source source ∧
      (honest_attestation cfg ext (E.store cfg ext i k) s index i
        ).data.target = target := by
  obtain ⟨i, hi, hhi, s, hstart, hbefore, hcommittee⟩ :=
    E.supermajority_honest_signer_before_last_slot cfg hbyz hspe
      L.target_span_within.1 L.target_span_within.2 L.signers_in_epoch
      L.supermajority
  obtain ⟨a, ⟨body, _hdesc, hincluded⟩, hia, hsource, htarget⟩ :=
    L.signer_attestation i hi
  have evidence := I.evidence hincluded
  have hsEpoch : compute_epoch_at_slot cfg s = target.epoch := by
    apply Nat.div_eq_of_lt_le hstart
    have hbefore' : s < target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1) := hbefore
    change s < (target.epoch + 1) * cfg.slots_per_epoch
    rw [Nat.add_mul, one_mul]
    exact hbefore'.trans_le (Nat.add_le_add_left
      (Nat.sub_le cfg.slots_per_epoch 1) _)
  have haEpoch : compute_epoch_at_slot cfg a.data.slot = target.epoch := by
    rw [← evidence.target_epoch, htarget]
  have haSlot : a.data.slot = s :=
    hec.committee_assignment_unique i a.data.slot s
      (evidence.attesters_in_committee i hia) hcommittee
      (haEpoch.trans hsEpoch.symm)
  obtain ⟨w, q, hsched⟩ := evidence.received_from_block
  obtain ⟨k0, own, _hcausal, hvote0, hdata⟩ :=
    hhb.no_forgery w q a true hsched i hhi hia
  rw [haSlot] at hvote0
  have hsH : E.SlotWithinHorizon cfg s := haSlot ▸ evidence.slot_within_horizon
  obtain ⟨k, index, hHk, hk, hvote⟩ :=
    hhb.votes_head i hhi s hcommittee hsH (hs0.trans hstart)
  have hsame := hvote0
  rw [hvote] at hsame
  have heq := (Prod.mk.inj (Option.some.inj hsame)).2
  have hdata' : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data := by
    rw [heq]
    exact hdata
  refine ⟨i, s, k, index, hhi, hHk, hk, hstart, hbefore, hvote,
    (hhb.vote_deadline i hhi s k _ hvote).2, ?_, ?_⟩
  · rw [← hdata']; exact hsource
  · rw [← hdata']; exact htarget

end IncludedSupermajorityLink
end FastConfirmation.Spec

end
