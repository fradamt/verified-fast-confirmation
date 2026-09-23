module
public import FastConfirmation.Spec.Proof.MonotonicityLiveBridge
public import FastConfirmation.Spec.Proof.MonotonicityLiveMessagePersistence

@[expose] public section

/-!
# Full-window one-confirmation inputs for live monotonicity

Recorded honest votes contribute their weight to the executable score.
The configured liveness margin then suffices when the confirmation window
has full-epoch estimate and the balance source uses the anchored registry.
The interval and balance-source equalities remain to be established at calls.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- An exact epoch window is recognized by the executable estimator as a
full validator-set window. -/
theorem full_epoch_estimate_eq (e : Epoch) (total : Gwei) :
    estimate_committee_weight_between_slots cfg total
      (compute_start_slot_at_epoch cfg e)
      (compute_start_slot_at_epoch cfg (e + 1) - 1) = total := by
  have hL : 0 < cfg.slots_per_epoch := cfg.slots_per_epoch_pos
  have hend : (e + 1) * cfg.slots_per_epoch - 1 =
      e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    simpa only [Nat.add_mul, one_mul] using
      (Nat.add_sub_assoc (show 1 ≤ cfg.slots_per_epoch from hL)
        (e * cfg.slots_per_epoch))
  have hfirst : (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) /
      cfg.slots_per_epoch = e := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) <
            e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
          Nat.add_lt_add_left (Nat.sub_lt hL (by omega)) _
        _ = (e + 1) * cfg.slots_per_epoch := by
          simp only [Nat.add_mul, one_mul]
  have hnext : (((e + 1) * cfg.slots_per_epoch - 1) + 1) /
      cfg.slots_per_epoch = e + 1 := by
    have hnum : ((e + 1) * cfg.slots_per_epoch - 1) + 1 =
        (e + 1) * cfg.slots_per_epoch :=
      Nat.sub_add_cancel (by
        simp only [Nat.add_mul, one_mul]
        exact (Nat.succ_le_of_lt hL).trans (Nat.le_add_left _ _))
    rw [hnum]
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_refl _
    · simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
        (Nat.lt_add_of_pos_right hL :
          (e + 1) * cfg.slots_per_epoch <
            (e + 1) * cfg.slots_per_epoch + cfg.slots_per_epoch)
  have hfull : is_full_validator_set_covered cfg
      (compute_start_slot_at_epoch cfg e)
      (compute_start_slot_at_epoch cfg (e + 1) - 1) = true := by
    simp only [is_full_validator_set_covered, compute_epoch_at_slot,
      compute_start_slot_at_epoch, decide_eq_true_eq]
    rw [hfirst, hnext]
    exact Nat.lt_succ_self e
  have hordered : compute_start_slot_at_epoch cfg e ≤
      compute_start_slot_at_epoch cfg (e + 1) - 1 := by
    simp only [compute_start_slot_at_epoch, hend]
    exact Nat.le_add_right _ _
  simp [estimate_committee_weight_between_slots, hordered, hfull]

/-- Every window containing a whole epoch has exact total-balance estimate,
even if it begins before the epoch or ends after it. -/
theorem estimate_eq_total_of_full_epoch_inside
    (e : Epoch) (total : Gwei) (a b : Slot)
    (ha : a ≤ compute_start_slot_at_epoch cfg e)
    (hb : compute_start_slot_at_epoch cfg (e + 1) - 1 ≤ b) :
    estimate_committee_weight_between_slots cfg total a b = total := by
  have hL : 0 < cfg.slots_per_epoch := cfg.slots_per_epoch_pos
  have hend : (e + 1) * cfg.slots_per_epoch - 1 =
      e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    simpa only [Nat.add_mul, one_mul] using
      (Nat.add_sub_assoc (show 1 ≤ cfg.slots_per_epoch from hL)
        (e * cfg.slots_per_epoch))
  have hfirst : (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) /
      cfg.slots_per_epoch = e := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) <
            e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
          Nat.add_lt_add_left (Nat.sub_lt hL (by omega)) _
        _ = (e + 1) * cfg.slots_per_epoch := by
          simp only [Nat.add_mul, one_mul]
  have hnext : (((e + 1) * cfg.slots_per_epoch - 1) + 1) /
      cfg.slots_per_epoch = e + 1 := by
    have hnum : ((e + 1) * cfg.slots_per_epoch - 1) + 1 =
        (e + 1) * cfg.slots_per_epoch :=
      Nat.sub_add_cancel (by
        simp only [Nat.add_mul, one_mul]
        exact (Nat.succ_le_of_lt hL).trans (Nat.le_add_left _ _))
    rw [hnum]
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_refl _
    · simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
        (Nat.lt_add_of_pos_right hL :
          (e + 1) * cfg.slots_per_epoch <
            (e + 1) * cfg.slots_per_epoch + cfg.slots_per_epoch)
  have hleft : compute_epoch_at_slot cfg (a + (cfg.slots_per_epoch - 1)) ≤ e := by
    calc
      compute_epoch_at_slot cfg (a + (cfg.slots_per_epoch - 1)) ≤
          compute_epoch_at_slot cfg
            (compute_start_slot_at_epoch cfg e + (cfg.slots_per_epoch - 1)) :=
        Nat.div_le_div_right (Nat.add_le_add_right ha _)
      _ = e := by simpa only [compute_epoch_at_slot, compute_start_slot_at_epoch]
        using hfirst
  have hright : e + 1 ≤ compute_epoch_at_slot cfg (b + 1) := by
    calc
      e + 1 = compute_epoch_at_slot cfg
          (compute_start_slot_at_epoch cfg (e + 1) - 1 + 1) := by
        simpa only [compute_epoch_at_slot, compute_start_slot_at_epoch] using hnext.symm
      _ ≤ compute_epoch_at_slot cfg (b + 1) :=
        Nat.div_le_div_right (Nat.add_le_add_right hb 1)
  have hfull : is_full_validator_set_covered cfg a b = true := by
    simp only [is_full_validator_set_covered, decide_eq_true_eq]
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le (Nat.lt_succ_self e) hright)
  have hordered : a ≤ b := by
    calc
      a ≤ compute_start_slot_at_epoch cfg e := ha
      _ ≤ compute_start_slot_at_epoch cfg (e + 1) - 1 := by
        simp only [compute_start_slot_at_epoch, hend]
        exact Nat.le_add_right _ _
      _ ≤ b := hb
  simp [estimate_committee_weight_between_slots, hordered, hfull]

/-- A first block of an epoch uses that whole epoch as its adversarial
window at the next epoch start. The executable equivocation discount can
only reduce the configured budget. -/
theorem first_epoch_block_adversarial_bound
    (store : Store Root) (balanceSource : BeaconState Root)
    (r : Root) (e : Epoch)
    (hblockEpoch : get_block_epoch cfg store r = e)
    (hparentEpoch : get_block_epoch cfg store (store.blocks r).parent_root < e)
    (hcurrentSlot : get_current_slot cfg store =
      compute_start_slot_at_epoch cfg (e + 1)) :
    get_adversarial_weight cfg ext store balanceSource r ≤
      get_total_active_balance cfg balanceSource / 100 *
        cfg.confirmation_byzantine_threshold := by
  rw [get_adversarial_weight_eq]
  have hspan : (if get_block_epoch cfg store r >
      get_block_epoch cfg store (store.blocks r).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg store r)
      else (store.blocks r).slot) = compute_start_slot_at_epoch cfg e := by
    simp [hblockEpoch, hparentEpoch]
  rw [hspan, hcurrentSlot]
  have hle := compute_adversarial_weight_le cfg ext
    (store := store) (bs := balanceSource)
    (compute_start_slot_at_epoch cfg e)
    (compute_start_slot_at_epoch cfg (e + 1) - 1)
  simpa only [full_epoch_estimate_eq] using hle

/-- Once two disjoint parts exhaust a full epoch, estimation soundness on
both parts forces exact accounting whenever their estimates exhaust the
full-epoch estimate. -/
theorem complementary_epoch_window_exact
    {whole left right estimateLeft estimateRight : ℕ}
    (hwhole : left + right = whole)
    (hest : estimateLeft + estimateRight = whole)
    (hleft : left ≤ estimateLeft)
    (hright : right ≤ estimateRight) :
    left = estimateLeft ∧ right = estimateRight := by
  omega

theorem complementary_epoch_window_exact_of_le
    {whole left right estimateLeft estimateRight : ℕ}
    (hwhole : left + right = whole)
    (hest : estimateLeft + estimateRight ≤ whole)
    (hleft : left ≤ estimateLeft)
    (hright : right ≤ estimateRight) :
    left = estimateLeft ∧ right = estimateRight := by
  omega

/-- Two adjacent partial windows with a combined length of one epoch cannot
overestimate the active total. The divisor truncation only makes the sum
smaller. -/
theorem complementary_partial_estimates_le_total
    (tab : Gwei) (a b c : Slot)
    (hab : a ≤ b) (hbc : b + 1 ≤ c)
    (hcovLeft : is_full_validator_set_covered cfg a b = false)
    (hcovRight : is_full_validator_set_covered cfg (b + 1) c = false)
    (hepochLeft : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b)
    (hepochRight : compute_epoch_at_slot cfg (b + 1) = compute_epoch_at_slot cfg c)
    (hlength : b - a + 1 + (c - (b + 1) + 1) = cfg.slots_per_epoch) :
    estimate_committee_weight_between_slots cfg tab a b +
      estimate_committee_weight_between_slots cfg tab (b + 1) c ≤ tab := by
  rw [estimate_same_epoch cfg tab a b hab hcovLeft hepochLeft,
    estimate_same_epoch cfg tab (b + 1) c hbc hcovRight hepochRight,
    ← Nat.mul_add, hlength]
  exact Nat.div_mul_le_self tab cfg.slots_per_epoch

private theorem partial_slot_count
    {a b length : ℕ} (hpositive : 0 < length)
    (hab : a ≤ b) (hbc : b + 1 ≤ a + (length - 1)) :
    b - a + 1 + (a + (length - 1) - (b + 1) + 1) = length := by
  omega

/-- The configured at-most-25% Byzantine fraction makes the honest part
of any committee span at least three quarters of its weight. -/
theorem Config.honest_span_three_quarters
    {span byzantine honest : ℕ}
    (hpart : honest + byzantine = span)
    (hbound : 100 * byzantine ≤
      cfg.confirmation_byzantine_threshold * span) :
    3 * span ≤ 4 * honest := by
  have hcap : cfg.confirmation_byzantine_threshold * span ≤ 25 * span :=
    Nat.mul_le_mul_right span cfg.confirmation_byzantine_threshold_le
  omega

/-- The integer margin retained by a previously confirmed block survives
an added window if its new honest support covers three quarters of that
window, the adversarial allowance grows by at most one quarter, and the
empty-slot discount does not shrink. -/
theorem reconfirm_margin_persists
    {score window boost adversarial discount added honestAdded
      adversarialNew discountNew : ℕ}
    (hconfirmed : window + boost + 2 * adversarial <
      2 * score + discount)
    (hhonest : 3 * added ≤ 4 * honestAdded)
    (hadversarial : 4 * adversarialNew ≤
      4 * adversarial + added)
    (hdiscount : discount ≤ discountNew) :
    window + added + boost + 2 * adversarialNew <
      2 * (score + honestAdded) + discountNew := by
  omega

/-- Gloas may remove an empty-slot discount as parent-root messages move to
the child. The strict margin still persists if the lost discount is covered
by twice that additional child support. -/
theorem reconfirm_margin_persists_with_discount_loss
    {score window boost adversarial discount added honestAdded movedSupport
      adversarialNew discountNew : ℕ}
    (hconfirmed : window + boost + 2 * adversarial <
      2 * score + discount)
    (hhonest : 3 * added ≤ 4 * honestAdded)
    (hadversarial : 4 * adversarialNew ≤
      4 * adversarial + added)
    (hdiscount : discount ≤ discountNew + 2 * movedSupport) :
    window + added + boost + 2 * adversarialNew <
      2 * (score + honestAdded + movedSupport) + discountNew := by
  have hmargin := reconfirm_margin_persists hconfirmed hhonest
    hadversarial hdiscount
  omega

/-- For quantized same-epoch windows, the configured adversarial allowance
grows by at most one quarter of the added committee weight. A larger
equivocation score can only reduce the remaining allowance. -/
theorem quantized_adversarial_budget_growth
    {old added cap oldEq newEq : ℕ}
    (hOld : 100 ∣ old) (hAdded : 100 ∣ added)
    (hcap : cap ≤ 25) (heq : oldEq ≤ newEq) :
    4 * (((old + added) / 100 * cap) - newEq) ≤
      4 * ((old / 100 * cap) - oldEq) + added := by
  obtain ⟨x, hx⟩ := hOld
  obtain ⟨y, hy⟩ := hAdded
  subst old
  subst added
  have hdivOld : (100 * x) / 100 = x := by omega
  have hdivNew : (100 * x + 100 * y) / 100 = x + y := by
    rw [← Nat.mul_add]
    omega
  rw [hdivOld, hdivNew, Nat.add_mul]
  have hsub : (x * cap + y * cap) - newEq ≤
      (x * cap - oldEq) + y * cap := by
    have harith {a b c d : ℕ} (hcd : c ≤ d) :
        (a + b) - d ≤ (a - c) + b := by omega
    exact harith heq
  calc
    4 * (x * cap + y * cap - newEq) ≤
        4 * ((x * cap - oldEq) + y * cap) :=
      Nat.mul_le_mul_left 4 hsub
    _ = 4 * (x * cap - oldEq) + 4 * (y * cap) := by ring
    _ ≤ 4 * (x * cap - oldEq) + 100 * y := by
      apply Nat.add_le_add_left
      calc
        4 * (y * cap) = (4 * y) * cap := by ring
        _ ≤ (4 * y) * 25 := Nat.mul_le_mul_left (4 * y) hcap
        _ = 100 * y := by ring

/-- If a previously supporting non-honest validator equivocates, its lost
support is charged to the same increase in the equivocation score. The
quantized allowance still covers the remaining new adversarial score and
the lost old support. -/
theorem quantized_adversarial_budget_growth_with_loss
    {old added cap oldEq newEq lost : ℕ}
    (hOld : 100 ∣ old) (hAdded : 100 ∣ added)
    (hcap : cap ≤ 25)
    (hOldEq : oldEq ≤ old / 100 * cap)
    (hlost : lost ≤ old / 100 * cap - oldEq)
    (heq : oldEq + lost ≤ newEq) :
    4 * ((((old + added) / 100 * cap) - newEq) + lost) ≤
      4 * ((old / 100 * cap) - oldEq) + added := by
  obtain ⟨x, hx⟩ := hOld
  obtain ⟨y, hy⟩ := hAdded
  subst old
  subst added
  have hdivOld : (100 * x) / 100 = x := by omega
  have hdivNew : (100 * x + 100 * y) / 100 = x + y := by
    rw [← Nat.mul_add]
    omega
  rw [hdivOld] at hOldEq hlost
  rw [hdivOld, hdivNew, Nat.add_mul]
  have hsub : (x * cap + y * cap - newEq) + lost ≤
      (x * cap - oldEq) + y * cap := by
    have harith {a b c d l : ℕ}
        (hc : c ≤ a) (hl : l ≤ a - c) (hcd : c + l ≤ d) :
        (a + b - d) + l ≤ (a - c) + b := by omega
    exact harith hOldEq hlost heq
  calc
    4 * ((x * cap + y * cap - newEq) + lost) ≤
        4 * ((x * cap - oldEq) + y * cap) :=
      Nat.mul_le_mul_left 4 hsub
    _ = 4 * (x * cap - oldEq) + 4 * (y * cap) := by ring
    _ ≤ 4 * (x * cap - oldEq) + 100 * y := by
      apply Nat.add_le_add_left
      calc
        4 * (y * cap) = (4 * y) * cap := by ring
        _ ≤ (4 * y) * 25 := Nat.mul_le_mul_left (4 * y) hcap
        _ = 100 * y := by ring

/-- Integer reconfirmation margin with equivocation-neutral support loss. -/
theorem reconfirm_margin_persists_with_equivocation_loss
    {score window boost adversarial added honestAdded lost
      adversarialNew scoreNew : ℕ}
    (hconfirmed : window + boost + 2 * adversarial < 2 * score)
    (hhonest : 3 * added ≤ 4 * honestAdded)
    (hscore : score + honestAdded ≤ scoreNew + lost)
    (hadversarial : 4 * (adversarialNew + lost) ≤
      4 * adversarial + added) :
    window + added + boost + 2 * adversarialNew < 2 * scoreNew := by
  omega

/-- Old supporters and new honest assignments fit inside the new supporter
set plus the old supporters that were lost. This set identity is the score
accounting shape needed before charging lost supporters to equivocation. -/
theorem Execution.weight_growth_with_support_loss (E : Execution Root)
    {old new added : Finset ValidatorIndex}
    (hadded : added ⊆ new \ old) :
    E.weight old + E.weight added ≤
      E.weight new + E.weight (old \ new) := by
  have hdisjLeft : Disjoint old added := by
    apply Finset.disjoint_left.mpr
    intro i hiOld hiAdded
    exact (Finset.mem_sdiff.mp (hadded hiAdded)).2 hiOld
  have hdisjRight : Disjoint new (old \ new) := by
    apply Finset.disjoint_left.mpr
    intro i hiNew hiLost
    exact (Finset.mem_sdiff.mp hiLost).2 hiNew
  have hsubset : old ∪ added ⊆ new ∪ (old \ new) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiOld | hiAdded
    · by_cases hiNew : i ∈ new
      · exact Finset.mem_union.mpr (Or.inl hiNew)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hiOld, hiNew⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mp (hadded hiAdded)).1)
  calc
    E.weight old + E.weight added = E.weight (old ∪ added) := by
      simpa only [Execution.weight] using
        (Finset.sum_union hdisjLeft).symm
    _ ≤ E.weight (new ∪ (old \ new)) := weight_mono (E := E) hsubset
    _ = E.weight new + E.weight (old \ new) := by
      simpa only [Execution.weight] using Finset.sum_union hdisjRight

/-- Old equivocators and newly lost supporters form disjoint subsets of
the new equivocation set. -/
theorem Execution.weight_growth_of_new_equivocators (E : Execution Root)
    {oldEquiv newEquiv lost : Finset ValidatorIndex}
    (hold : oldEquiv ⊆ newEquiv)
    (hlost : lost ⊆ newEquiv \ oldEquiv) :
    E.weight oldEquiv + E.weight lost ≤ E.weight newEquiv := by
  have hdisj : Disjoint oldEquiv lost := by
    apply Finset.disjoint_left.mpr
    intro i hiOld hiLost
    exact (Finset.mem_sdiff.mp (hlost hiLost)).2 hiOld
  have hsubset : oldEquiv ∪ lost ⊆ newEquiv := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiOld | hiLost
    · exact hold hiOld
    · exact (Finset.mem_sdiff.mp (hlost hiLost)).1
  calc
    E.weight oldEquiv + E.weight lost = E.weight (oldEquiv ∪ lost) := by
      simpa only [Execution.weight] using (Finset.sum_union hdisj).symm
    _ ≤ E.weight newEquiv := weight_mono (E := E) hsubset

/-- A disjoint set of newly recorded supporters raises the score, with the
old supporters absent at the new store charged explicitly as a loss. -/
theorem Execution.attestation_score_growth_with_loss (E : Execution Root)
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (node : ForkChoiceNode Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (added : Finset ValidatorIndex)
    (hadded : added ⊆
      (AttSupporters cfg newStore node newSource).toFinset \
        (AttSupporters cfg oldStore node oldSource).toFinset) :
    get_attestation_score cfg oldStore node oldSource + E.weight added ≤
      get_attestation_score cfg newStore node newSource +
        E.weight ((AttSupporters cfg oldStore node oldSource).toFinset \
          (AttSupporters cfg newStore node newSource).toFinset) := by
  rw [attestation_score_eq_weight cfg hvalOld,
    attestation_score_eq_weight cfg hvalNew]
  exact E.weight_growth_with_support_loss hadded

/-- An old supporter whose message and ancestry survive remains a supporter
unless it entered the new equivocation set. The active and unslashed base
lists are compared separately so cached sources may be different states. -/
theorem old_supporter_persists_or_equivocates
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (node : ForkChoiceNode Root)
    (hbase :
      (get_active_validator_indices oldSource
          (get_current_epoch cfg oldSource)).filter
            (fun i => !(oldSource.validators.getD i default).slashed) =
      (get_active_validator_indices newSource
          (get_current_epoch cfg newSource)).filter
            (fun i => !(newSource.validators.getD i default).slashed))
    (hlatest : ∀ i m, i ∈ AttSupporters cfg oldStore node oldSource →
      oldStore.latest_messages i = some m →
      newStore.latest_messages i = some m)
    (hancestry : ∀ i m, i ∈ AttSupporters cfg oldStore node oldSource →
      oldStore.latest_messages i = some m →
      is_ancestor oldStore (get_supported_node oldStore m) node = true →
      is_ancestor newStore (get_supported_node newStore m) node = true)
    {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg oldStore node oldSource) :
    i ∈ AttSupporters cfg newStore node newSource ∨
      i ∈ newStore.equivocating_indices := by
  by_cases hequiv : i ∈ newStore.equivocating_indices
  · exact Or.inr hequiv
  left
  obtain ⟨m, hm, _, hanc⟩ := mem_AttSupporters cfg hi
  simp only [AttSupporters, List.mem_filter] at hi ⊢
  refine ⟨?_, ?_⟩
  · have hmemOld : i ∈
        (get_active_validator_indices oldSource
          (get_current_epoch cfg oldSource)).filter
            (fun j => !(oldSource.validators.getD j default).slashed) :=
        List.mem_filter.mpr hi.1
    rw [hbase] at hmemOld
    exact List.mem_filter.mp hmemOld
  · rw [hlatest i m (by simpa only [AttSupporters, List.mem_filter] using hi) hm]
    simp [hequiv, hancestry i m
      (by simpa only [AttSupporters, List.mem_filter] using hi) hm hanc]

private theorem strict_margin_of_threshold
    {window boost adversarial discount score : ℕ}
    (hscore : score >
      if discount < window + boost + 2 * adversarial then
        (window + boost + 2 * adversarial - discount) / 2
      else 0) :
    window + boost + 2 * adversarial < 2 * score + discount := by
  split_ifs at hscore <;> omega

private theorem threshold_of_strict_margin
    {window boost adversarial discount score : ℕ}
    (hmargin : window + boost + 2 * adversarial <
      2 * score + discount)
    (hpositive : 0 < score) :
    score >
      if discount < window + boost + 2 * adversarial then
        (window + boost + 2 * adversarial - discount) / 2
      else 0 := by
  split_ifs <;> omega

/-- The executable Boolean one-confirmation result yields its exact strict
integer margin, including the threshold's underflow branch. -/
theorem one_confirmed_has_integer_margin
    (store : Store Root) (balanceSource : BeaconState Root) (r : Root)
    (hconfirmed : is_one_confirmed cfg ext store balanceSource r = true) :
    let support := get_attestation_score cfg store (get_node_for_root r)
      balanceSource
    let maximum := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      ((store.blocks (store.blocks r).parent_root).slot + 1)
      (get_current_slot cfg store - 1)
    let boost := compute_proposer_score cfg balanceSource
    let adversarial := get_adversarial_weight cfg ext store balanceSource r
    let discount := get_support_discount cfg ext store balanceSource r
    maximum + boost + 2 * adversarial < 2 * support + discount := by
  dsimp only
  simp only [is_one_confirmed, decide_eq_true_eq] at hconfirmed
  dsimp only [compute_safety_threshold] at hconfirmed
  exact strict_margin_of_threshold hconfirmed

/-- A block cannot pass the one-confirmation test on adversarial support
alone when the empty-slot discount does not exceed the unboosted window
budget. This is the arithmetic core of the live-chain exclusion argument. -/
theorem one_confirmed_requires_nonadversarial_support
    (store : Store Root) (balanceSource : BeaconState Root) (r : Root)
    (hdiscount : get_support_discount cfg ext store balanceSource r ≤
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg balanceSource)
        ((store.blocks (store.blocks r).parent_root).slot + 1)
        (get_current_slot cfg store - 1) +
      compute_proposer_score cfg balanceSource)
    (hconfirmed : is_one_confirmed cfg ext store balanceSource r = true) :
    get_adversarial_weight cfg ext store balanceSource r <
      get_attestation_score cfg store (get_node_for_root r) balanceSource := by
  have hmargin := one_confirmed_has_integer_margin cfg ext
    store balanceSource r hconfirmed
  dsimp only at hmargin
  have harith {W P A S D : ℕ}
      (hD : D ≤ W + P) (hM : W + P + 2 * A < 2 * S + D) :
      A < S := by omega
  exact harith hdiscount hmargin

/-- A known ancestor in the slot directly before a child is that child's
parent. This fact makes the live-chain parent link independent of payload
status. -/
theorem live_parent_eq_previous_slot_ancestor
    (store : Store Root) (child previous : Root)
    (hwf : ParentSlotLt store)
    (hchild : child ∈ store.block_roots)
    (hparent : (store.blocks child).parent_root ∈ store.block_roots)
    (hprevSlot : (store.blocks previous).slot + 1 =
      (store.blocks child).slot)
    (hwalk : WalkKnown store (store.blocks previous).slot
      (store.blocks child).parent_root)
    (hancestor : is_ancestor store (get_node_for_root child)
      (get_node_for_root previous) = true) :
    (store.blocks child).parent_root = previous := by
  have hparentSlot : (store.blocks (store.blocks child).parent_root).slot ≤
      (store.blocks previous).slot := by
    have hlt := hwf child hchild hparent
    rw [← hprevSlot] at hlt
    exact Nat.lt_succ_iff.mp hlt
  have hstep := get_ancestor_step hwf hchild
    (by rw [← hprevSlot]; exact Nat.lt_succ_self _ :
      (store.blocks previous).slot < (store.blocks child).slot) hwalk
  simp only [get_node_for_root, is_ancestor_pending,
    decide_eq_true_eq] at hancestor
  rw [get_ancestor_stop hparentSlot] at hstep
  exact hstep.symm.trans hancestor

/-- A direct parent-slot edge has no empty-slot support discount, for any
balance source. -/
theorem live_support_discount_zero_of_consecutive_slots
    (store : Store Root) (balanceSource : BeaconState Root) (b : Root)
    (hconsecutive :
      (store.blocks (store.blocks b).parent_root).slot + 1 =
        (store.blocks b).slot) :
    get_support_discount cfg ext store balanceSource b = 0 := by
  simp [get_support_discount, compute_empty_slot_support_discount,
    hconsecutive]

/-- A positive score satisfying the executable strict integer margin is
one-confirmed, even in the threshold's underflow branch. -/
theorem one_confirmed_of_integer_margin
    (store : Store Root) (balanceSource : BeaconState Root) (r : Root)
    (hpositive : 0 < get_attestation_score cfg store
      (get_node_for_root r) balanceSource)
    (hmargin :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg balanceSource)
          ((store.blocks (store.blocks r).parent_root).slot + 1)
          (get_current_slot cfg store - 1) +
        compute_proposer_score cfg balanceSource +
        2 * get_adversarial_weight cfg ext store balanceSource r <
      2 * get_attestation_score cfg store (get_node_for_root r) balanceSource +
        get_support_discount cfg ext store balanceSource r) :
    is_one_confirmed cfg ext store balanceSource r = true := by
  simp only [is_one_confirmed, decide_eq_true_eq]
  dsimp only [compute_safety_threshold]
  exact threshold_of_strict_margin hmargin hpositive

/-- Reconfirmation across two executable stores reduces to recorded-support
growth, window growth, adversarial growth, and discount persistence. The
current work leaves those concrete accounting facts to the execution proof. -/
theorem is_one_confirmed_reconfirm_of_growth
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (r : Root) (added honestAdded : ℕ)
    (hOld : is_one_confirmed cfg ext oldStore oldSource r = true)
    (hscore :
      get_attestation_score cfg oldStore (get_node_for_root r) oldSource +
        honestAdded ≤
      get_attestation_score cfg newStore (get_node_for_root r) newSource)
    (hwindow :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg oldSource)
          ((oldStore.blocks (oldStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg oldStore - 1) + added)
    (hboost : compute_proposer_score cfg newSource ≤
      compute_proposer_score cfg oldSource)
    (hadversarial :
      4 * get_adversarial_weight cfg ext newStore newSource r ≤
        4 * get_adversarial_weight cfg ext oldStore oldSource r + added)
    (hdiscount : get_support_discount cfg ext oldStore oldSource r ≤
      get_support_discount cfg ext newStore newSource r)
    (hhonest : 3 * added ≤ 4 * honestAdded) :
    is_one_confirmed cfg ext newStore newSource r = true := by
  have hOldMargin := one_confirmed_has_integer_margin cfg ext
    oldStore oldSource r hOld
  dsimp only at hOldMargin
  have hmarginGrowth := reconfirm_margin_persists hOldMargin
    hhonest hadversarial hdiscount
  have hmarginNew :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) +
        compute_proposer_score cfg newSource +
        2 * get_adversarial_weight cfg ext newStore newSource r <
      2 * get_attestation_score cfg newStore (get_node_for_root r) newSource +
        get_support_discount cfg ext newStore newSource r := by
    calc
      _ ≤
        (estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg oldSource)
            ((oldStore.blocks (oldStore.blocks r).parent_root).slot + 1)
            (get_current_slot cfg oldStore - 1) + added) +
          compute_proposer_score cfg oldSource +
          2 * get_adversarial_weight cfg ext newStore newSource r :=
        Nat.add_le_add (Nat.add_le_add hwindow hboost) (Nat.le_refl _)
      _ < 2 * (get_attestation_score cfg oldStore
          (get_node_for_root r) oldSource + honestAdded) +
          get_support_discount cfg ext newStore newSource r := hmarginGrowth
      _ ≤ 2 * get_attestation_score cfg newStore
          (get_node_for_root r) newSource +
          get_support_discount cfg ext newStore newSource r :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hscore) _
  have hOldPos : 0 < get_attestation_score cfg oldStore
      (get_node_for_root r) oldSource := by
    have hOldScore := hOld
    simp only [is_one_confirmed, decide_eq_true_eq] at hOldScore
    exact lt_of_le_of_lt (Nat.zero_le _) hOldScore
  have hNewPos : 0 < get_attestation_score cfg newStore
      (get_node_for_root r) newSource :=
    hOldPos.trans_le ((Nat.le_add_right _ _).trans hscore)
  exact one_confirmed_of_integer_margin cfg ext newStore newSource r
    hNewPos hmarginNew

/-- Executable reconfirmation with a zero discount and equivocation-neutral
support loss. The source and committee accounting are explicit inputs for
the live execution bridge. -/
theorem is_one_confirmed_reconfirm_of_growth_with_equivocation_loss
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (r : Root) (added honestAdded lost : ℕ)
    (hOld : is_one_confirmed cfg ext oldStore oldSource r = true)
    (hOldDiscount : get_support_discount cfg ext oldStore oldSource r = 0)
    (hNewDiscount : get_support_discount cfg ext newStore newSource r = 0)
    (hscore : get_attestation_score cfg oldStore
        (get_node_for_root r) oldSource + honestAdded ≤
      get_attestation_score cfg newStore
        (get_node_for_root r) newSource + lost)
    (hlost : lost < get_attestation_score cfg oldStore
      (get_node_for_root r) oldSource)
    (hwindow :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg oldSource)
          ((oldStore.blocks (oldStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg oldStore - 1) + added)
    (hboost : compute_proposer_score cfg newSource ≤
      compute_proposer_score cfg oldSource)
    (hadversarial :
      4 * (get_adversarial_weight cfg ext newStore newSource r + lost) ≤
        4 * get_adversarial_weight cfg ext oldStore oldSource r + added)
    (hhonest : 3 * added ≤ 4 * honestAdded) :
    is_one_confirmed cfg ext newStore newSource r = true := by
  have hOldMargin := one_confirmed_has_integer_margin cfg ext
    oldStore oldSource r hOld
  dsimp only at hOldMargin
  rw [hOldDiscount, Nat.add_zero] at hOldMargin
  have hmarginGrowth := reconfirm_margin_persists_with_equivocation_loss
    hOldMargin hhonest hscore hadversarial
  have hmarginNew :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) +
        compute_proposer_score cfg newSource +
        2 * get_adversarial_weight cfg ext newStore newSource r <
      2 * get_attestation_score cfg newStore
          (get_node_for_root r) newSource +
        get_support_discount cfg ext newStore newSource r := by
    rw [hNewDiscount, Nat.add_zero]
    exact lt_of_le_of_lt
      (Nat.add_le_add (Nat.add_le_add hwindow hboost) le_rfl)
      hmarginGrowth
  have hNewPos : 0 < get_attestation_score cfg newStore
      (get_node_for_root r) newSource := by
    have harith {a b c d : ℕ}
        (h1 : c < a) (h2 : a + b ≤ d + c) : 0 < d := by omega
    exact harith hlost hscore
  exact one_confirmed_of_integer_margin cfg ext newStore newSource r
    hNewPos hmarginNew

/-- Reconfirmation with Gloas discount loss charged to additional child
support. Its concrete moved-support inequality remains an execution-level
obligation. -/
theorem is_one_confirmed_reconfirm_of_growth_with_discount_loss
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (r : Root) (added honestAdded movedSupport : ℕ)
    (hOld : is_one_confirmed cfg ext oldStore oldSource r = true)
    (hscore :
      get_attestation_score cfg oldStore (get_node_for_root r) oldSource +
        honestAdded + movedSupport ≤
      get_attestation_score cfg newStore (get_node_for_root r) newSource)
    (hwindow :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg oldSource)
          ((oldStore.blocks (oldStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg oldStore - 1) + added)
    (hboost : compute_proposer_score cfg newSource ≤
      compute_proposer_score cfg oldSource)
    (hadversarial :
      4 * get_adversarial_weight cfg ext newStore newSource r ≤
        4 * get_adversarial_weight cfg ext oldStore oldSource r + added)
    (hdiscount : get_support_discount cfg ext oldStore oldSource r ≤
      get_support_discount cfg ext newStore newSource r + 2 * movedSupport)
    (hhonest : 3 * added ≤ 4 * honestAdded) :
    is_one_confirmed cfg ext newStore newSource r = true := by
  have hOldMargin := one_confirmed_has_integer_margin cfg ext
    oldStore oldSource r hOld
  dsimp only at hOldMargin
  have hmarginGrowth := reconfirm_margin_persists_with_discount_loss
    hOldMargin hhonest hadversarial hdiscount
  have hmarginNew :
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg newSource)
          ((newStore.blocks (newStore.blocks r).parent_root).slot + 1)
          (get_current_slot cfg newStore - 1) +
        compute_proposer_score cfg newSource +
        2 * get_adversarial_weight cfg ext newStore newSource r <
      2 * get_attestation_score cfg newStore (get_node_for_root r) newSource +
        get_support_discount cfg ext newStore newSource r := by
    calc
      _ ≤
        (estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg oldSource)
            ((oldStore.blocks (oldStore.blocks r).parent_root).slot + 1)
            (get_current_slot cfg oldStore - 1) + added) +
          compute_proposer_score cfg oldSource +
          2 * get_adversarial_weight cfg ext newStore newSource r :=
        Nat.add_le_add (Nat.add_le_add hwindow hboost) (Nat.le_refl _)
      _ < 2 * (get_attestation_score cfg oldStore
          (get_node_for_root r) oldSource + honestAdded + movedSupport) +
          get_support_discount cfg ext newStore newSource r := hmarginGrowth
      _ ≤ 2 * get_attestation_score cfg newStore
          (get_node_for_root r) newSource +
          get_support_discount cfg ext newStore newSource r :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hscore) _
  have hOldScore := hOld
  simp only [is_one_confirmed, decide_eq_true_eq] at hOldScore
  have hOldPos : 0 < get_attestation_score cfg oldStore
      (get_node_for_root r) oldSource :=
    lt_of_le_of_lt (Nat.zero_le _) hOldScore
  have hNewPos : 0 < get_attestation_score cfg newStore
      (get_node_for_root r) newSource := by
    apply hOldPos.trans_le
    calc
      get_attestation_score cfg oldStore (get_node_for_root r) oldSource ≤
          get_attestation_score cfg oldStore (get_node_for_root r) oldSource +
            honestAdded := Nat.le_add_right _ _
      _ ≤ get_attestation_score cfg oldStore (get_node_for_root r) oldSource +
          honestAdded + movedSupport := Nat.le_add_right _ _
      _ ≤ get_attestation_score cfg newStore
          (get_node_for_root r) newSource := hscore
  exact one_confirmed_of_integer_margin cfg ext newStore newSource r
    hNewPos hmarginNew

namespace Execution

variable (E : Execution Root)

private def AcceptedActualFCRNextSlotSafetyAssumptions.live_selected_margin
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := h.trajectory.genesis_structure
    wellFormed := h.trajectory.wellFormed
    whole_seconds := h.trajectory.whole_seconds
    honest_behavior := h.trajectory.honest_behavior
    synchrony := h.completed_calls.synchrony
    externals_coherence := h.trajectory.externals_coherence
    static_validators := h.completed_calls.static_validators
    byzantine_bound := h.completed_calls.byzantine_bound
    domain := E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext h.semantics h.trajectory h.completed_calls.synchrony
        h.anchor_eq h.anchor_boundary }

/-- A block that passes the actual current-source confirmation test at a
live call is the produced honest block of its slot. The accepted economic
engine supplies an honest recorded supporter; the live field makes that
supporter vote for the produced block as well. Equal ancestor slots then
identify the two roots. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_one_confirmed_is_produced
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hqm : q + 1 ≤ m)
    {b : Root}
    (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true)
    (hs0 : E.slot_at cfg 0 ≤
      get_block_slot (E.store cfg ext w (q + 1)) b)
    (hsm : get_block_slot (E.store cfg ext w (q + 1)) b <
      E.slot_at cfg m) :
    ∃ bb : BeaconBlock Root, E.BlockAt b bb ∧
      bb.slot = get_block_slot (E.store cfg ext w (q + 1)) b ∧
      bb.proposer_index ∈ E.honest := by
  let st := E.store cfg ext w (q + 1)
  let s := get_block_slot st b
  obtain ⟨r, br, hbr, hrs, hrHonest, _, hsupport⟩ :=
    live.honest_block_each_slot s hs0 hsm
  let hA := h.live_selected_margin cfg ext E
  obtain ⟨i, lm, hi, hlm, hancB⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA
      w hw (q + 1) (E.fcrStep cfg ext w q)
      (E.fcrStep_store cfg ext w q) b hHq1 hb hp hconf
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  obtain ⟨u, k, a, hvote, hlmSlot, huEnd⟩ :=
    E.latest_message_has_honest_vote_before_endpoint cfg ext
      h.trajectory.wellFormed h.trajectory.honest_behavior
      h.trajectory.externals_coherence hgen hi hw hHq1 hlm
  have hprov : LatestMessageProvenance E cfg (get_current_slot cfg st) st := by
    rw [E.store_current_slot cfg ext w (q + 1)]
    exact E.latestMessageProvenance cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence hgen w (q + 1) hw hHq1
  obtain ⟨aProv, _, _, _, _, _, _, hlmKnown, hlmRootSlot, hmsgSlot⟩ :=
    hprov i lm hlm
  have hwf : ParentSlotLt st :=
    E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      h.trajectory.wellFormed.anchor_parent_unscheduled w (q + 1)
  have hwalk : WalkKnown st (st.blocks b).slot lm.root :=
    E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      w (q + 1) b hb lm.root hlmKnown
  have hancB' : (get_ancestor st (get_node_for_root lm.root) s).root = b := by
    have hanc : is_ancestor st (get_node_for_root lm.root)
        (get_node_for_root b) = true := by
      simpa only [st, get_node_for_root, is_ancestor_supported_pending]
        using hancB
    simpa only [s, get_block_slot, get_node_for_root,
      is_ancestor_pending, decide_eq_true_eq] using hanc
  have hsu : s ≤ u := by
    have hslot := get_ancestor_slot_le hwf hwalk
    have hancRaw : (get_ancestor st (get_node_for_root lm.root)
        (st.blocks b).slot).root = b := by
      simpa only [s, get_block_slot] using hancB'
    change (st.blocks (get_ancestor st (get_node_for_root lm.root)
      (st.blocks b).slot).root).slot ≤ (st.blocks lm.root).slot at hslot
    rw [hancRaw] at hslot
    have huEq : lm.slot = u := by simpa only [hlmSlot]
    calc
      s ≤ (st.blocks lm.root).slot := hslot
      _ ≤ aProv.data.slot := hlmRootSlot
      _ = lm.slot := hmsgSlot.symm
      _ = u := huEq
  have hsupport' : ∀ j ∈ E.honest, ∀ t kt a',
      s ≤ t → t < E.slot_at cfg (q + 1) →
      E.vote j t = some (kt, a') →
      r ∈ (E.store cfg ext j kt).block_roots ∧
        is_ancestor (E.store cfg ext j kt)
          (get_node_for_root a'.data.beacon_block_root)
          (get_node_for_root r) = true := by
    intro j hj t kt a' ht htm hvt
    exact hsupport j hj t kt a' ht
      (htm.trans_le (E.slot_at_mono cfg hqm)) hvt
  have hsupportAt : r ∈ st.block_roots ∧
      is_ancestor st (get_node_for_root lm.root) (get_node_for_root r) = true := by
    exact h.recorded_fixed_live_block_support cfg ext E hi hHq1 hs0
      hsupport' hsu hvote hw hlm (by
        have huEq : lm.slot = u := by simpa only [hlmSlot]
        simp only [get_latest_message_epoch, huEq]
        exact le_rfl)
  have hrSlot : (st.blocks r).slot = s := by
    have hrBlock := E.blockAt_of_store_known cfg ext hsupportAt.1
    have heq := E.blockAt_unique h.trajectory.wellFormed hbr hrBlock
    simpa only [hrs, s, get_block_slot] using
      congrArg (fun x : BeaconBlock Root => x.slot) heq.symm
  have hancR : (get_ancestor st (get_node_for_root lm.root) s).root = r := by
    have hanc := hsupportAt.2
    simp only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] at hanc
    rwa [hrSlot] at hanc
  have hEq : b = r := hancB'.symm.trans hancR
  rw [hEq]
  exact ⟨br, hbr, by simpa only [s, get_block_slot, hEq] using hrs,
    hrHonest⟩

/-- The parent of a confirmed live block after the initial slot is the
honest block produced in the preceding slot. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_one_confirmed_parent
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hqm : q + 1 ≤ m)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true)
    (hs0 : E.slot_at cfg 0 <
      get_block_slot (E.store cfg ext w (q + 1)) b)
    (hsm : get_block_slot (E.store cfg ext w (q + 1)) b <
      E.slot_at cfg m) :
    ∃ r br, E.BlockAt r br ∧
      br.slot + 1 = get_block_slot (E.store cfg ext w (q + 1)) b ∧
      br.proposer_index ∈ E.honest ∧
      ((E.store cfg ext w (q + 1)).blocks b).parent_root = r := by
  let st := E.store cfg ext w (q + 1)
  let s := get_block_slot st b
  let sp := s - 1
  have hsp0 : E.slot_at cfg 0 ≤ sp := Nat.le_sub_one_of_lt hs0
  have hspm : sp < E.slot_at cfg m := (Nat.sub_le s 1).trans_lt hsm
  obtain ⟨r, br, hbr, hrs, hrHonest, _, hsupport⟩ :=
    live.honest_block_each_slot sp hsp0 hspm
  let hA := h.live_selected_margin cfg ext E
  obtain ⟨i, lm, hi, hlm, hancB⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA
      w hw (q + 1) (E.fcrStep cfg ext w q)
      (E.fcrStep_store cfg ext w q) b hHq1 hb hp hconf
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  obtain ⟨u, k, a, hvote, hlmSlot, _huEnd⟩ :=
    E.latest_message_has_honest_vote_before_endpoint cfg ext
      h.trajectory.wellFormed h.trajectory.honest_behavior
      h.trajectory.externals_coherence hgen hi hw hHq1 hlm
  have hprov : LatestMessageProvenance E cfg (get_current_slot cfg st) st := by
    rw [E.store_current_slot cfg ext w (q + 1)]
    exact E.latestMessageProvenance cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence hgen w (q + 1) hw hHq1
  obtain ⟨aProv, _, _, _, _, _, _, hlmKnown, hlmRootSlot, hmsgSlot⟩ :=
    hprov i lm hlm
  have hwf : ParentSlotLt st :=
    E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      h.trajectory.wellFormed.anchor_parent_unscheduled w (q + 1)
  have hwalkB : WalkKnown st (st.blocks b).slot lm.root :=
    E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      w (q + 1) b hb lm.root hlmKnown
  have hancBRaw : (get_ancestor st (get_node_for_root lm.root) s).root = b := by
    have hanc : is_ancestor st (get_node_for_root lm.root)
        (get_node_for_root b) = true := by
      simpa only [st, get_node_for_root, is_ancestor_supported_pending]
        using hancB
    simpa only [s, get_block_slot, get_node_for_root,
      is_ancestor_pending, decide_eq_true_eq] using hanc
  have hsu : s ≤ u := by
    have hslot := get_ancestor_slot_le hwf hwalkB
    change (st.blocks (get_ancestor st (get_node_for_root lm.root)
      (st.blocks b).slot).root).slot ≤ (st.blocks lm.root).slot at hslot
    have hancRaw : (get_ancestor st (get_node_for_root lm.root)
        (st.blocks b).slot).root = b := by
      simpa only [s, get_block_slot] using hancBRaw
    rw [hancRaw] at hslot
    have huEq : lm.slot = u := by simpa only [hlmSlot]
    calc
      s ≤ (st.blocks lm.root).slot := hslot
      _ ≤ aProv.data.slot := hlmRootSlot
      _ = lm.slot := hmsgSlot.symm
      _ = u := huEq
  have hsupport' : ∀ j ∈ E.honest, ∀ t kt a',
      sp ≤ t → t < E.slot_at cfg (q + 1) →
      E.vote j t = some (kt, a') →
      r ∈ (E.store cfg ext j kt).block_roots ∧
        is_ancestor (E.store cfg ext j kt)
          (get_node_for_root a'.data.beacon_block_root)
          (get_node_for_root r) = true := by
    intro j hj t kt a' ht htm hvt
    exact hsupport j hj t kt a' ht
      (htm.trans_le (E.slot_at_mono cfg hqm)) hvt
  have hsupportAt : r ∈ st.block_roots ∧
      is_ancestor st (get_node_for_root lm.root) (get_node_for_root r) = true := by
    exact h.recorded_fixed_live_block_support cfg ext E hi hHq1 hsp0
      hsupport' ((Nat.sub_le s 1).trans hsu) hvote hw hlm (by
        have huEq : lm.slot = u := by simpa only [hlmSlot]
        simp only [get_latest_message_epoch, huEq]
        exact le_rfl)
  have hrSlot : (st.blocks r).slot = sp := by
    have hrBlock := E.blockAt_of_store_known cfg ext hsupportAt.1
    have heq := E.blockAt_unique h.trajectory.wellFormed hbr hrBlock
    simpa only [hrs] using congrArg (fun x : BeaconBlock Root => x.slot) heq.symm
  have hancRRaw : (get_ancestor st (get_node_for_root lm.root) sp).root = r := by
    have hanc := hsupportAt.2
    simp only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] at hanc
    rwa [hrSlot] at hanc
  have hwalkR : WalkKnown st sp lm.root := by
    rw [← hrSlot]
    exact E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      w (q + 1) r hsupportAt.1 lm.root hlmKnown
  have hspLeS : sp ≤ s := Nat.sub_le s 1
  have hcomp := get_ancestor_comp_root hwf hspLeS hwalkR
  simp only [get_node_for_root] at hancBRaw hancRRaw
  rw [hancBRaw, hancRRaw] at hcomp
  have hancBR : is_ancestor st (get_node_for_root b)
      (get_node_for_root r) = true := by
    simp only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq]
    rw [hrSlot]
    exact hcomp
  have hwalkParent : WalkKnown st sp (st.blocks b).parent_root := by
    rw [← hrSlot]
    exact E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      w (q + 1) r hsupportAt.1 _ hp
  have hspSucc : sp + 1 = s :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hs0))
  have hparentEq : (st.blocks b).parent_root = r :=
    live_parent_eq_previous_slot_ancestor st b r hwf hb hp
      (by rw [hrSlot]; exact hspSucc)
      (by rw [hrSlot]; exact hwalkParent) hancBR
  exact ⟨r, br, hbr, by rw [hrs, hspSucc], hrHonest, hparentEq⟩

/-- The same live parent link removes the discount from the actual
confirmation call, independently of which checkpoint state supplied the
balance source. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_one_confirmed_discount_zero
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hqm : q + 1 ≤ m)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true)
    (hs0 : E.slot_at cfg 0 <
      get_block_slot (E.store cfg ext w (q + 1)) b)
    (hsm : get_block_slot (E.store cfg ext w (q + 1)) b <
      E.slot_at cfg m)
    (bs : BeaconState Root) :
    get_support_discount cfg ext (E.store cfg ext w (q + 1)) bs b = 0 := by
  let st := E.store cfg ext w (q + 1)
  obtain ⟨r, br, hbr, hslot, _, hparent⟩ :=
    h.live_one_confirmed_parent cfg ext E live hw hHq1 hqm
      hb hp hconf hs0 hsm
  have hrKnown : r ∈ st.block_roots := by
    rw [← hparent]
    exact hp
  have hrBlock := E.blockAt_of_store_known cfg ext hrKnown
  have hrEq := E.blockAt_unique h.trajectory.wellFormed hbr hrBlock
  have hconsecutive :
      (st.blocks (st.blocks b).parent_root).slot + 1 =
        (st.blocks b).slot := by
    rw [hparent]
    rw [hrEq] at hslot
    simpa only [st, get_block_slot] using hslot
  exact live_support_discount_zero_of_consecutive_slots cfg ext st bs b
    hconsecutive

omit [LinearOrder Root] [Inhabited Root] in
/-- The initial active weight splits into honest and non-honest parts. -/
theorem initial_active_weight_partition :
    E.weight ((Finset.range E.registry.length).filter fun i =>
      i ∈ E.honest ∧
        is_active_validator (E.registry.getD i default)
          (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true) +
      E.activeNonHonestWeight cfg =
    E.weight ((Finset.range E.registry.length).filter fun i =>
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true) := by
  let active := (Finset.range E.registry.length).filter fun i =>
    is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true
  have hsplit := Finset.sum_filter_add_sum_filter_not active
    (fun i => i ∈ E.honest) E.weight_of
  simpa only [Execution.weight, Execution.activeNonHonestWeight,
    active, Finset.filter_filter, and_comm] using hsplit

/-- In an accepted execution, the anchor state and initial execution slot
name the same epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.anchor_epoch_eq_initial
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) :
    get_current_epoch cfg E.anchor_state =
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
  obtain ⟨ast, ablk, hgenEq, hslot, _⟩ := h.trajectory.genesis_structure
  have hanchorState : E.anchor_state = ast := by
    simp only [Execution.anchor_state, hgenEq, get_forkchoice_store,
      Function.update_self]
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext 0 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg
      h.trajectory.whole_seconds] at hcurrent0
    exact hcurrent0.symm
  rw [hanchorState, hslot0]
  rfl

/-- In every in-horizon committee span, accepted Byzantine concentration
leaves at least three quarters of the assigned weight honest. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.honest_span_three_quarters
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (a b : Slot)
    (haH : E.SlotWithinHorizon cfg a)
    (hbH : E.SlotWithinHorizon cfg b) :
    3 * E.weight (E.span_committee a b) ≤
      4 * E.weight ((E.span_committee a b).filter fun i => i ∈ E.honest) := by
  have hpart :
      E.weight ((E.span_committee a b).filter fun i => i ∈ E.honest) +
        E.weight ((E.span_committee a b).filter fun i => i ∉ E.honest) =
      E.weight (E.span_committee a b) := by
    simpa only [Execution.weight] using
      Finset.sum_filter_add_sum_filter_not (E.span_committee a b)
        (fun i => i ∈ E.honest) E.weight_of
  exact cfg.honest_span_three_quarters hpart
    (h.completed_calls.byzantine_bound.span_fraction a b haH hbH)

/-- Disjoint consecutive slot spans inside one epoch have disjoint
validator assignments. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.same_epoch_spans_disjoint
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {a b c : Slot}
    (hepoch : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg c) :
    Disjoint (E.span_committee a b) (E.span_committee (b + 1) c) := by
  apply Finset.disjoint_left.mpr
  intro i hiLeft hiRight
  simp only [Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc] at hiLeft hiRight
  obtain ⟨s, hs, his⟩ := hiLeft
  obtain ⟨t, ht, hit⟩ := hiRight
  have hst : s < t :=
    lt_of_le_of_lt hs.2 (Nat.lt_of_succ_le ht.1)
  have hse : compute_epoch_at_slot cfg s = compute_epoch_at_slot cfg t := by
    apply Nat.le_antisymm
    · exact Nat.div_le_div_right hst.le
    · calc
        compute_epoch_at_slot cfg t ≤ compute_epoch_at_slot cfg c :=
          Nat.div_le_div_right ht.2
        _ = compute_epoch_at_slot cfg a := hepoch.symm
        _ ≤ compute_epoch_at_slot cfg s :=
          Nat.div_le_div_right hs.1
  have heq := h.trajectory.externals_coherence.committee_assignment_unique
    i s t his hit hse
  exact (Nat.ne_of_lt hst) heq

omit [LinearOrder Root] [Inhabited Root] in
/-- Splitting an inclusive slot span after `b` preserves exactly the
assigned-validator set. -/
theorem span_committee_split (a b c : Slot)
    (hab : a ≤ b) (hbc : b < c) :
    E.span_committee a c =
      E.span_committee a b ∪ E.span_committee (b + 1) c := by
  ext i
  simp only [Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_union]
  constructor
  · rintro ⟨s, hs, his⟩
    by_cases hsb : s ≤ b
    · exact Or.inl ⟨s, ⟨hs.1, hsb⟩, his⟩
    · exact Or.inr ⟨s, ⟨Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hsb), hs.2⟩, his⟩
  · rintro (⟨s, hs, his⟩ | ⟨s, hs, his⟩)
    · exact ⟨s, ⟨hs.1, hs.2.trans hbc.le⟩, his⟩
    · exact ⟨s, ⟨hab.trans ((Nat.le_succ b).trans hs.1), hs.2⟩, his⟩

/-- Within one epoch, disjoint adjacent slot ranges partition committee
weight exactly. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.same_epoch_span_weight_partition
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {a b c : Slot} (hab : a ≤ b) (hbc : b < c)
    (hepoch : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg c) :
    E.weight (E.span_committee a b) +
      E.weight (E.span_committee (b + 1) c) =
      E.weight (E.span_committee a c) := by
  rw [span_committee_split E a b c hab hbc]
  exact (Finset.sum_union (h.same_epoch_spans_disjoint cfg ext E hepoch)).symm

/-- In an accepted horizon-bounded epoch, the committee union has the exact
anchored total active weight. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.full_epoch_span_weight_eq_total
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (store : Store Root)
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hendH : E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store)) :
    E.weight (E.span_committee (currentTargetEpochStart cfg store)
      (currentTargetEpochEnd cfg store)) = E.total_active cfg := by
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon := by
    rw [h.anchor_epoch_eq_initial cfg ext E]
    exact (h.completed_calls.static_validators.genesis_within_horizon).2.2
  rw [current_epoch_span_eq_anchorActive cfg ext E
    h.trajectory.externals_coherence h.completed_calls.static_validators
    hcurrentH hendH hanchorH]
  exact E.total_active_eq_anchorActive_weight cfg
    h.completed_calls.balance_floor |>.symm

/-- Estimation soundness on complementary same-epoch ranges is exact once
their disjoint union is the full active committee. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.complementary_partial_window_exact
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (a b c : Slot) (hab : a ≤ b) (hbc : b + 1 ≤ c)
    (hepoch : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg c)
    (hwhole : E.weight (E.span_committee a c) = E.total_active cfg)
    (haH : E.SlotWithinHorizon cfg a)
    (hbH : E.SlotWithinHorizon cfg b)
    (hb1H : E.SlotWithinHorizon cfg (b + 1))
    (hcH : E.SlotWithinHorizon cfg c)
    (hcovLeft : is_full_validator_set_covered cfg a b = false)
    (hcovRight : is_full_validator_set_covered cfg (b + 1) c = false)
    (hepochLeft : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b)
    (hepochRight : compute_epoch_at_slot cfg (b + 1) = compute_epoch_at_slot cfg c)
    (hlength : b - a + 1 + (c - (b + 1) + 1) = cfg.slots_per_epoch) :
    E.weight (E.span_committee a b) =
        estimate_committee_weight_between_slots cfg (E.total_active cfg) a b ∧
      E.weight (E.span_committee (b + 1) c) =
        estimate_committee_weight_between_slots cfg (E.total_active cfg)
          (b + 1) c := by
  have hpart := h.same_epoch_span_weight_partition cfg ext E
    hab (Nat.lt_of_succ_le hbc) hepoch
  rw [hwhole] at hpart
  have hest := complementary_partial_estimates_le_total cfg
    (E.total_active cfg) a b c hab hbc hcovLeft hcovRight
    hepochLeft hepochRight hlength
  have hleft := h.completed_calls.byzantine_bound.estimate_sound a b haH hbH
  have hright := h.completed_calls.byzantine_bound.estimate_sound
    (b + 1) c hb1H hcH
  exact complementary_epoch_window_exact_of_le hpart hest hleft hright

/-- The accepted full-epoch committee identity supplies the whole-weight
premise of complementary partial-window exactness. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.current_epoch_partial_window_exact
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (store : Store Root) (b : Slot)
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hstartH : E.SlotWithinHorizon cfg (currentTargetEpochStart cfg store))
    (hendH : E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store))
    (hbH : E.SlotWithinHorizon cfg b)
    (hb1H : E.SlotWithinHorizon cfg (b + 1))
    (hab : currentTargetEpochStart cfg store ≤ b)
    (hbc : b + 1 ≤ currentTargetEpochEnd cfg store)
    (hepoch : compute_epoch_at_slot cfg (currentTargetEpochStart cfg store) =
      compute_epoch_at_slot cfg (currentTargetEpochEnd cfg store))
    (hcovLeft : is_full_validator_set_covered cfg
      (currentTargetEpochStart cfg store) b = false)
    (hcovRight : is_full_validator_set_covered cfg
      (b + 1) (currentTargetEpochEnd cfg store) = false)
    (hepochLeft : compute_epoch_at_slot cfg (currentTargetEpochStart cfg store) =
      compute_epoch_at_slot cfg b)
    (hepochRight : compute_epoch_at_slot cfg (b + 1) =
      compute_epoch_at_slot cfg (currentTargetEpochEnd cfg store)) :
    E.weight (E.span_committee (currentTargetEpochStart cfg store) b) =
        estimate_committee_weight_between_slots cfg (E.total_active cfg)
          (currentTargetEpochStart cfg store) b ∧
      E.weight (E.span_committee (b + 1) (currentTargetEpochEnd cfg store)) =
        estimate_committee_weight_between_slots cfg (E.total_active cfg)
          (b + 1) (currentTargetEpochEnd cfg store) := by
  have hlen : b - currentTargetEpochStart cfg store + 1 +
      (currentTargetEpochEnd cfg store - (b + 1) + 1) =
      cfg.slots_per_epoch := by
    exact partial_slot_count cfg.slots_per_epoch_pos hab hbc
  exact h.complementary_partial_window_exact cfg ext E
    (currentTargetEpochStart cfg store) b
    (currentTargetEpochEnd cfg store) hab hbc hepoch
    (h.full_epoch_span_weight_eq_total cfg ext E store hcurrentH hendH)
    hstartH hbH hb1H hendH hcovLeft hcovRight
    hepochLeft hepochRight hlen

/-- Every vote slot in a completed epoch has reached its next-slot delivery
deadline by the endpoint, including the last slot of that epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.completed_epoch_vote_delivery
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {e : Epoch} {m : ℕ}
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    {t : Slot} (htEpoch : compute_epoch_at_slot cfg t = e) :
    E.slot_start cfg (t + 1) ≤ m := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have htNext : t + 1 ≤ compute_start_slot_at_epoch cfg (e + 1) := by
    have hlt := Nat.lt_mul_div_succ t cfg.slots_per_epoch_pos
    simp only [compute_epoch_at_slot] at htEpoch
    rw [htEpoch] at hlt
    simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlt
  apply Nat.le_of_not_gt
  intro htooLate
  have hslotLt : E.slot_at cfg m < t + 1 :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2 htooLate
  exact (Nat.not_lt_of_ge (htNext.trans heDone)) hslotLt

/-- Any in-horizon balance source with the static registry has the anchor's
total balance and proposer boost. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_balance_source_accounting
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (bs : BeaconState Root)
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon) :
    get_total_active_balance cfg bs = E.total_active cfg ∧
      compute_proposer_score cfg bs =
        compute_proposer_score cfg E.anchor_state := by
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon := by
    rw [h.anchor_epoch_eq_initial cfg ext E]
    exact (h.completed_calls.static_validators.genesis_within_horizon).2.2
  have hact : ∀ i : ValidatorIndex,
      is_active_validator (bs.validators.getD i default)
        (get_current_epoch cfg bs) =
      is_active_validator (E.anchor_state.validators.getD i default)
        (get_current_epoch cfg E.anchor_state) := by
    intro i
    rw [hval]
    exact h.completed_calls.static_validators.activity_constant i
      (get_current_epoch cfg bs) (get_current_epoch cfg E.anchor_state)
      hbsH hanchorH
  have htotal := get_total_active_balance_congr cfg hval hact
  have hboost := compute_proposer_score_congr cfg hval hact
  exact ⟨htotal, hboost⟩

/-- Two in-horizon balance sources with the accepted static registry have
the same active, unslashed validator list, even when they are different
checkpoint states. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_supporter_base_eq
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon) :
    (get_active_validator_indices oldSource
        (get_current_epoch cfg oldSource)).filter
          (fun i => !(oldSource.validators.getD i default).slashed) =
    (get_active_validator_indices newSource
        (get_current_epoch cfg newSource)).filter
          (fun i => !(newSource.validators.getD i default).slashed) := by
  have hact : ∀ i : ValidatorIndex,
      is_active_validator (oldSource.validators.getD i default)
          (get_current_epoch cfg oldSource) =
        is_active_validator (newSource.validators.getD i default)
          (get_current_epoch cfg newSource) := by
    intro i
    rw [hvalOld, hvalNew]
    exact h.completed_calls.static_validators.activity_constant i
      (get_current_epoch cfg oldSource) (get_current_epoch cfg newSource)
      hOldH hNewH
  have hidx : get_active_validator_indices oldSource
      (get_current_epoch cfg oldSource) =
      get_active_validator_indices newSource
        (get_current_epoch cfg newSource) := by
    unfold get_active_validator_indices
    rw [hvalOld, hvalNew]
    apply List.filter_congr
    intro i _
    simpa only [hvalOld, hvalNew] using hact i
  rw [hidx, hvalOld, hvalNew]

/-- A supporter of an epoch-`e` block at an epoch-`e` call has a latest
message from that epoch. Provenance puts the vote after the block and before
the call. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_supporter_message_epoch
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {t : ℕ}
    (hHt : E.WithinHorizon cfg t)
    {e : Epoch} (hcurrent : get_current_store_epoch cfg
      (E.store cfg ext w t) = e)
    {b : Root} (hb : b ∈ (E.store cfg ext w t).block_roots)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w t) b = e)
    (source : BeaconState Root)
    {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg (E.store cfg ext w t)
      (get_node_for_root b) source)
    {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages i = some msg) :
    get_latest_message_epoch cfg msg = e := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hprov := E.latestMessageProvenance cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    hgen w t hw hHt
  obtain ⟨_, _, _, _, _, hbefore, _, hrootKnown, hrootSlot, hmsgSlot⟩ :=
    hprov i msg hmsg
  have hwalkK := E.store_walkKnownK cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure w t
  have hwalk := hwalkK b hb msg.root hrootKnown
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hi
  rw [hmsg] at hlm
  have hsame : lm = msg := (Option.some.inj hlm).symm
  subst lm
  have hancPending : is_ancestor (E.store cfg ext w t)
      (get_node_for_root msg.root) (get_node_for_root b) = true := by
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  have hslotLe := get_ancestor_slot_le
    (E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      h.trajectory.wellFormed.anchor_parent_unscheduled w t) hwalk
  simp only [get_node_for_root, is_ancestor_pending,
    decide_eq_true_eq] at hancPending
  rw [hancPending] at hslotLe
  have hlower : get_block_slot (E.store cfg ext w t) b ≤ msg.slot :=
    hslotLe.trans (hrootSlot.trans_eq hmsgSlot.symm)
  have hupper : msg.slot < get_current_slot cfg (E.store cfg ext w t) := by
    rw [E.store_current_slot cfg ext w t]
    rw [hmsgSlot]
    exact Nat.lt_of_succ_le hbefore
  have hepochLower : e ≤ get_latest_message_epoch cfg msg := by
    rw [← hbEpoch]
    exact Nat.div_le_div_right hlower
  have hepochUpper : get_latest_message_epoch cfg msg ≤ e := by
    rw [← hcurrent]
    exact Nat.div_le_div_right hupper.le
  exact Nat.le_antisymm hepochUpper hepochLower

/-- At the next epoch start, an old supporter with an old-epoch message still
supports the same known block unless that validator has been marked as an
equivocator. The result applies to Byzantine as well as honest validators. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_old_supporter_at_boundary
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hnm : n ≤ m)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    {e : Epoch} (hboundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg (e + 1))
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon)
    (hOldEpoch : ∀ i msg,
      i ∈ AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource →
      (E.store cfg ext w n).latest_messages i = some msg →
      get_latest_message_epoch cfg msg = e)
    {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource) :
    i ∈ AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root b) newSource ∨
      i ∈ (E.store cfg ext w m).equivocating_indices := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hbase := h.live_supporter_base_eq cfg ext E oldSource newSource
    hvalOld hvalNew hOldH hNewH
  have hprovOld := E.latestMessageProvenance cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    hgen w n hw hHn
  have hsub := (E.store_storeLE cfg ext w hnm).1
  have hwalk := E.store_walkKnownK cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure w n
  apply old_supporter_persists_or_equivocates cfg
    (E.store cfg ext w n) (E.store cfg ext w m)
    oldSource newSource (get_node_for_root b) hbase
  · intro j msg hj hmsg
    exact E.latest_message_stable_at_next_epoch_start cfg ext
      h.trajectory.wellFormed h.trajectory.externals_coherence
      hgen hw hnm hHn hHm hboundary hmsg (hOldEpoch j msg hj hmsg)
  · intro j msg hj hmsg hanc
    obtain ⟨_, _, _, _, _, _, _, hmsgKnown, _, _⟩ :=
      hprovOld j msg hmsg
    have hwalkMsg := hwalk b hb msg.root hmsgKnown
    have hancPending : is_ancestor (E.store cfg ext w n)
        (get_node_for_root msg.root) (get_node_for_root b) = true := by
      simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
    have htransport := is_ancestor_transport cfg ext
      h.trajectory.wellFormed hsub hmsgKnown hb hwalkMsg hancPending
    simpa only [get_node_for_root, is_ancestor_supported_pending] using htransport
  · exact hi

/-- For a known block from the just-completed epoch, the old-message epoch
condition follows from block and call geometry. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_old_supporter_at_boundary_of_block_epoch
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hnm : n ≤ m)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    {e : Epoch}
    (holdCurrent : get_current_store_epoch cfg (E.store cfg ext w n) = e)
    (hboundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg (e + 1))
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w n) b = e)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon)
    {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource) :
    i ∈ AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root b) newSource ∨
      i ∈ (E.store cfg ext w m).equivocating_indices := by
  exact h.live_old_supporter_at_boundary cfg ext E hw hnm hHn hHm
    hboundary hb oldSource newSource hvalOld hvalNew hOldH hNewH
    (fun j msg hj hmsg => h.live_supporter_message_epoch cfg ext E
      hw hHn holdCurrent hb hbEpoch oldSource hj hmsg) hi

/-- Every old supporter absent from the boundary score is a newly marked
equivocator. This is the set-level loss that the adversarial allowance must
refund. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_lost_supporters_newly_equivocating
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hnm : n ≤ m)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    {e : Epoch}
    (holdCurrent : get_current_store_epoch cfg (E.store cfg ext w n) = e)
    (hboundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg (e + 1))
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w n) b = e)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon) :
    (AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).toFinset \
      (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource).toFinset ⊆
      (E.store cfg ext w m).equivocating_indices \
        (E.store cfg ext w n).equivocating_indices := by
  intro i hi
  have hOld : i ∈ AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hi).1
  have hNotNew := (Finset.mem_sdiff.mp hi).2
  have hNewEquiv := (h.live_old_supporter_at_boundary_of_block_epoch
    cfg ext E hw hnm hHn hHm holdCurrent hboundary hb hbEpoch
    oldSource newSource hvalOld hvalNew hOldH hNewH hOld).resolve_left
      (fun hNew => hNotNew (List.mem_toFinset.mpr hNew))
  obtain ⟨_, _, hNotOldEquiv, _⟩ := mem_AttSupporters cfg hOld
  exact Finset.mem_sdiff.mpr ⟨hNewEquiv, hNotOldEquiv⟩

/-- A checkpoint state already cached at an accepted call has the same
committee total and proposer score as the anchor. Thus a historical current
source and the next boundary's previous source need not be identical states
for the numerical reconfirmation argument. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_cached_source_accounting
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {t : ℕ}
    (hHt : E.WithinHorizon cfg t) {cp : Checkpoint Root}
    (hkey : cp ∈ (E.store cfg ext w t).checkpoint_state_keys) :
    get_total_active_balance cfg
        ((E.store cfg ext w t).checkpoint_states cp) = E.total_active cfg ∧
      compute_proposer_score cfg
        ((E.store cfg ext w t).checkpoint_states cp) =
        compute_proposer_score cfg E.anchor_state := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have htotal := E.checkpoint_states_total_active_balance cfg ext
    h.completed_calls.static_validators
    h.trajectory.externals_coherence w hw t cp hkey hHt
    (hdiv := h.trajectory.whole_seconds) (hgen := hgen)
  refine ⟨htotal, ?_⟩
  simp only [compute_proposer_score]
  rw [htotal]

/-- With a nondegenerate active balance, the live margin's non-honest
weight is exactly the complement of the honest anchor active set. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.anchor_honest_weight_partition
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg)) :
    E.weight ((E.currentTargetAnchorActive cfg).filter fun i => i ∈ E.honest) +
      E.activeNonHonestWeight cfg = E.total_active cfg := by
  have hset : E.currentTargetAnchorActive cfg =
      (Finset.range E.registry.length).filter fun i =>
        is_active_validator (E.registry.getD i default)
          (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true := by
    ext i
    simp [Execution.currentTargetAnchorActive, get_active_validator_indices,
      Execution.registry, h.anchor_epoch_eq_initial cfg ext E]
  have hpart := E.initial_active_weight_partition cfg
  have htotal := E.total_active_eq_anchorActive_weight cfg hfloor
  rw [hset] at htotal
  simpa only [hset, Finset.filter_filter, and_comm] using
    hpart.trans htotal.symm

/-- Committee coverage places every honest anchor-active validator into
the completed epoch. Delivery of each such slot is stated separately so
this lemma can be used at the exact FCR call time. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.honest_full_epoch_assignments
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {e : Epoch} {m : ℕ}
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hdelivery : ∀ t : Slot, compute_epoch_at_slot cfg t = e →
      E.slot_start cfg (t + 1) ≤ m) :
    ∀ i ∈ (E.currentTargetAnchorActive cfg).filter (fun i => i ∈ E.honest),
      i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        compute_start_slot_at_epoch cfg e ≤ t ∧
        t < E.slot_at cfg m ∧ i ∈ E.committee t ∧
        E.slot_start cfg (t + 1) ≤ m := by
  intro i hiHS
  obtain ⟨hiActive, hiHonest⟩ := Finset.mem_filter.mp hiHS
  have hactiveAnchor : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    simp only [Execution.currentTargetAnchorActive,
      get_active_validator_indices, List.mem_toFinset, List.mem_filter,
      List.mem_range] at hiActive
    simpa only [Execution.registry] using hiActive.2
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon := by
    rw [h.anchor_epoch_eq_initial cfg ext E]
    exact (h.completed_calls.static_validators.genesis_within_horizon).2.2
  have heEpochLe : e + 1 ≤ compute_epoch_at_slot cfg (E.slot_at cfg m) := by
    simp only [compute_epoch_at_slot]
    exact (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mpr
      (by simpa only [compute_start_slot_at_epoch] using heDone)
  have heH : e < E.verification_horizon :=
    (Nat.lt_succ_self e).trans (heEpochLe.trans_lt hHm.2.2)
  have hactiveE : is_active_validator (E.registry.getD i default) e = true := by
    rw [← h.completed_calls.static_validators.activity_constant i
      (get_current_epoch cfg E.anchor_state) e hanchorH heH]
    exact hactiveAnchor
  obtain ⟨t, htH, htEpoch, hcommittee⟩ :=
    h.trajectory.externals_coherence.committee_coverage i e heH hactiveE
  have hstartT : compute_start_slot_at_epoch cfg e ≤ t := by
    simp only [compute_start_slot_at_epoch, compute_epoch_at_slot] at htEpoch ⊢
    rw [← htEpoch]
    exact Nat.div_mul_le_self t cfg.slots_per_epoch
  have hnextT : t < compute_start_slot_at_epoch cfg (e + 1) := by
    have hlt := Nat.lt_mul_div_succ t cfg.slots_per_epoch_pos
    simp only [compute_epoch_at_slot] at htEpoch
    rw [htEpoch] at hlt
    simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlt
  exact ⟨hiHonest, t, htH, hstartT, hnextT.trans_le heDone,
    hcommittee, hdelivery t htEpoch⟩

/-- One-confirmation of a live block from a full-epoch set of delivered
honest assignments. The explicit equalities are accounting results about the
actual call window, not additional live assumptions. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.one_confirmed_of_full_window
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hHm : E.WithinHorizon cfg m)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      s ≤ u → u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        s ≤ t ∧ t < E.slot_at cfg m ∧ i ∈ E.committee t ∧
        E.slot_start cfg (t + 1) ≤ m)
    (hpartition : E.weight HS + E.activeNonHonestWeight cfg =
      E.total_active cfg)
    (hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      (((E.store cfg ext w m).blocks
        ((E.store cfg ext w m).blocks r).parent_root).slot + 1)
      (get_current_slot cfg (E.store cfg ext w m) - 1) ≤ E.total_active cfg)
    (hboost : compute_proposer_score cfg balanceSource ≤
      compute_proposer_score cfg E.anchor_state)
    (hadversarial : get_adversarial_weight cfg ext
      (E.store cfg ext w m) balanceSource r ≤
      E.total_active cfg / 100 * cfg.confirmation_byzantine_threshold) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  have hscore := h.fixed_live_block_score_lower cfg ext E hs0 hHm
    hsupport hw balanceSource hval hbsH HS hHS
  exact one_confirmed_of_bounded_window cfg ext
    (E.store cfg ext w m) balanceSource r hpartition
    live.configured_threshold_margin hscore hwindow hboost hadversarial

/-- A live epoch-entry block is one-confirmed at the next epoch start when
the endpoint balance source is the anchored registry and the entire epoch's
honest assignments have arrived. The parent-window and balance-floor facts
are kept explicit for the actual-call application. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.first_epoch_live_block_one_confirmed
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (heStart : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hdelivery : ∀ t : Slot, compute_epoch_at_slot cfg t = e →
      E.slot_start cfg (t + 1) ≤ m)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      compute_start_slot_at_epoch cfg e ≤ u →
      u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (htab : get_total_active_balance cfg balanceSource = E.total_active cfg)
    (hboost : compute_proposer_score cfg balanceSource ≤
      compute_proposer_score cfg E.anchor_state)
    (hcurrentSlot : get_current_slot cfg (E.store cfg ext w m) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hparentWindow : ((E.store cfg ext w m).blocks
      ((E.store cfg ext w m).blocks r).parent_root).slot + 1 ≤
        compute_start_slot_at_epoch cfg e)
    (hblockEpoch : get_block_epoch cfg (E.store cfg ext w m) r = e)
    (hparentEpoch : get_block_epoch cfg (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks r).parent_root < e) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  let HS := (E.currentTargetAnchorActive cfg).filter fun i => i ∈ E.honest
  have hassign := h.honest_full_epoch_assignments cfg ext E
    heDone hHm hdelivery
  have hpartition := h.anchor_honest_weight_partition cfg ext E hfloor
  have hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      (((E.store cfg ext w m).blocks
        ((E.store cfg ext w m).blocks r).parent_root).slot + 1)
      (get_current_slot cfg (E.store cfg ext w m) - 1) ≤ E.total_active cfg := by
    rw [htab, hcurrentSlot]
    exact le_of_eq (estimate_eq_total_of_full_epoch_inside cfg e
      (E.total_active cfg) _ _ hparentWindow (Nat.le_refl _))
  have hadversarial := first_epoch_block_adversarial_bound cfg ext
    (E.store cfg ext w m) balanceSource r e
    hblockEpoch hparentEpoch hcurrentSlot
  rw [htab] at hadversarial
  exact h.one_confirmed_of_full_window cfg ext E live heStart hHm
    hsupport hw balanceSource hval hbsH HS hassign hpartition
    hwindow hboost hadversarial

/-- The accepted clock and static-balance laws discharge all accounting
inputs of the first-epoch-block confirmation lemma. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.first_epoch_live_block_one_confirmed_at_boundary
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (heStart : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      compute_start_slot_at_epoch cfg e ≤ u →
      u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (hcurrentSlot : get_current_slot cfg (E.store cfg ext w m) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hparentWindow : ((E.store cfg ext w m).blocks
      ((E.store cfg ext w m).blocks r).parent_root).slot + 1 ≤
        compute_start_slot_at_epoch cfg e)
    (hblockEpoch : get_block_epoch cfg (E.store cfg ext w m) r = e)
    (hparentEpoch : get_block_epoch cfg (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks r).parent_root < e) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  obtain ⟨htab, hboost⟩ := h.live_balance_source_accounting cfg ext E
    balanceSource hval hbsH
  exact h.first_epoch_live_block_one_confirmed cfg ext E live
    heStart heDone hHm
    (fun t ht => h.completed_epoch_vote_delivery cfg ext E heDone ht)
    h.completed_calls.balance_floor hsupport hw balanceSource
    hval hbsH htab hboost.le hcurrentSlot hparentWindow
    hblockEpoch hparentEpoch

end Execution

end FastConfirmation.Spec

end
