module
public import FastConfirmationProofs.Monotonicity.LiveVoteSupport
public import FastConfirmationProofs.Monotonicity.LatestMessagePersistence

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

/-- The guarded executable adversarial allowance is the truncated
subtraction of the equivocation score from the configured cap. -/
theorem compute_adversarial_weight_eq_sub
    (store : Store Root) (source : BeaconState Root) (sa es : Slot) :
    compute_adversarial_weight cfg ext store source sa es =
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg source) sa es / 100 *
          cfg.confirmation_byzantine_threshold -
        get_equivocation_score cfg ext store source sa es := by
  simp only [compute_adversarial_weight]
  split_ifs with h
  · rfl
  · exact (Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)).symm

/-- Concrete adversarial-growth bound for two same-start windows. The
committee-estimate identity and equivocation increase are separate inputs. -/
theorem get_adversarial_weight_quantized_growth_with_loss
    (oldStore newStore : Store Root)
    (oldSource newSource : BeaconState Root)
    (b : Root) (sa added lost : ℕ)
    (hstartOld :
      (if get_block_epoch cfg oldStore b >
          get_block_epoch cfg oldStore (oldStore.blocks b).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg oldStore b)
       else (oldStore.blocks b).slot) = sa)
    (hstartNew :
      (if get_block_epoch cfg newStore b >
          get_block_epoch cfg newStore (newStore.blocks b).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg newStore b)
       else (newStore.blocks b).slot) = sa)
    (hestimate : estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg newSource) sa
        (get_current_slot cfg newStore - 1) =
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg oldSource) sa
        (get_current_slot cfg oldStore - 1) + added)
    (hOldDiv : 100 ∣ estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg oldSource) sa
      (get_current_slot cfg oldStore - 1))
    (hAddedDiv : 100 ∣ added)
    (hOldEq : get_equivocation_score cfg ext oldStore oldSource sa
        (get_current_slot cfg oldStore - 1) ≤
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg oldSource) sa
        (get_current_slot cfg oldStore - 1) / 100 *
          cfg.confirmation_byzantine_threshold)
    (hlost : lost ≤ get_adversarial_weight cfg ext oldStore oldSource b)
    (hequiv : get_equivocation_score cfg ext oldStore oldSource sa
        (get_current_slot cfg oldStore - 1) + lost ≤
      get_equivocation_score cfg ext newStore newSource sa
        (get_current_slot cfg newStore - 1)) :
    4 * (get_adversarial_weight cfg ext newStore newSource b + lost) ≤
      4 * get_adversarial_weight cfg ext oldStore oldSource b + added := by
  simp only [get_adversarial_weight_eq, hstartOld, hstartNew,
    compute_adversarial_weight_eq_sub] at hlost ⊢
  rw [hestimate]
  exact quantized_adversarial_budget_growth_with_loss
    hOldDiv hAddedDiv cfg.confirmation_byzantine_threshold_le
    hOldEq hlost hequiv

/-- Exactness for one slot identifies the estimator's per-slot rate with a
ground-truth committee weight. Phase0 quantization then makes every partial
same-epoch estimate a multiple of one hundred. -/
theorem Execution.hundred_dvd_same_epoch_estimate_of_one_slot_exact
    (E : Execution Root) (hbb : ByzantineBound cfg E)
    (tab : Gwei) (a s t : Slot)
    (hfirstCov : is_full_validator_set_covered cfg a a = false)
    (hfirstExact : estimate_committee_weight_between_slots cfg tab a a =
      E.weight (E.committee a))
    (hst : s ≤ t)
    (hcov : is_full_validator_set_covered cfg s t = false)
    (hepoch : compute_epoch_at_slot cfg s = compute_epoch_at_slot cfg t) :
    100 ∣ estimate_committee_weight_between_slots cfg tab s t := by
  have hrate : tab / cfg.slots_per_epoch = E.weight (E.committee a) := by
    have h := estimate_same_epoch cfg tab a a (Nat.le_refl _)
      hfirstCov rfl
    simpa only [Nat.sub_self, Nat.zero_add, mul_one] using h.symm.trans hfirstExact
  rw [estimate_same_epoch cfg tab s t hst hcov hepoch, hrate]
  exact dvd_mul_of_dvd_left (E.hundred_dvd_weight cfg hbb (E.committee a)) _

/-- A range beginning strictly after an epoch's start and ending in that
epoch cannot contain every slot of a complete epoch. -/
theorem no_full_coverage_inside_epoch_after_start
    (e : Epoch) (a b : Slot)
    (ha : compute_start_slot_at_epoch cfg e < a)
    (hb : b < compute_start_slot_at_epoch cfg (e + 1)) :
    is_full_validator_set_covered cfg a b = false := by
  have hle : b + 1 ≤ a + (cfg.slots_per_epoch - 1) := by
    have hnext : compute_start_slot_at_epoch cfg (e + 1) =
        compute_start_slot_at_epoch cfg e + cfg.slots_per_epoch := by
      simp [compute_start_slot_at_epoch, Nat.add_mul]
    rw [hnext] at hb
    have hpos := cfg.slots_per_epoch_pos
    have hminus : cfg.slots_per_epoch - 1 + 1 = cfg.slots_per_epoch :=
      Nat.sub_add_cancel hpos
    have heq : compute_start_slot_at_epoch cfg e + cfg.slots_per_epoch =
        compute_start_slot_at_epoch cfg e + 1 + (cfg.slots_per_epoch - 1) := by
      calc
        compute_start_slot_at_epoch cfg e + cfg.slots_per_epoch =
            compute_start_slot_at_epoch cfg e +
              ((cfg.slots_per_epoch - 1) + 1) :=
          congrArg (fun x => compute_start_slot_at_epoch cfg e + x) hminus.symm
        _ = compute_start_slot_at_epoch cfg e + 1 +
              (cfg.slots_per_epoch - 1) := by ac_rfl
    calc
      b + 1 ≤ compute_start_slot_at_epoch cfg e + cfg.slots_per_epoch :=
        Nat.succ_le_of_lt hb
      _ = compute_start_slot_at_epoch cfg e + 1 + (cfg.slots_per_epoch - 1) := heq
      _ ≤ a + (cfg.slots_per_epoch - 1) :=
        Nat.add_le_add_right (Nat.succ_le_of_lt ha) _
  have hnot : ¬ ((a + (cfg.slots_per_epoch - 1)) / cfg.slots_per_epoch <
      (b + 1) / cfg.slots_per_epoch) :=
    Nat.not_lt_of_ge (Nat.div_le_div_right hle)
  simpa [is_full_validator_set_covered, compute_epoch_at_slot] using hnot

/-- The coverage test is false when the inclusive range ends before the
first possible end of a complete epoch beginning at its start. -/
theorem no_full_coverage_of_short_range (a b : Slot)
    (hshort : b + 1 ≤ a + (cfg.slots_per_epoch - 1)) :
    is_full_validator_set_covered cfg a b = false := by
  have hnot : ¬ ((a + (cfg.slots_per_epoch - 1)) / cfg.slots_per_epoch <
      (b + 1) / cfg.slots_per_epoch) :=
    Nat.not_lt_of_ge (Nat.div_le_div_right hshort)
  simpa [is_full_validator_set_covered, compute_epoch_at_slot] using hnot

/-- An old window and its added suffix split exactly when both lie after
the same epoch's first slot. -/
theorem estimate_growth_inside_epoch_after_start
    (tab : Gwei) (e : Epoch) (a u v : Slot)
    (ha : compute_start_slot_at_epoch cfg e < a)
    (hau : a ≤ u) (huv : u + 1 ≤ v)
    (hv : v < compute_start_slot_at_epoch cfg (e + 1)) :
    estimate_committee_weight_between_slots cfg tab a v =
      estimate_committee_weight_between_slots cfg tab a u +
        estimate_committee_weight_between_slots cfg tab (u + 1) v := by
  have hepoch : ∀ x : Slot,
      compute_start_slot_at_epoch cfg e ≤ x →
      x < compute_start_slot_at_epoch cfg (e + 1) →
      compute_epoch_at_slot cfg x = e := by
    intro x hlo hhi
    have hge : e ≤ compute_epoch_at_slot cfg x := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hlo
    have hlt : compute_epoch_at_slot cfg x < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hhi
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hge
  have haHi : a < compute_start_slot_at_epoch cfg (e + 1) :=
    (hau.trans (Nat.le_of_succ_le huv)).trans_lt hv
  have huHi : u < compute_start_slot_at_epoch cfg (e + 1) :=
    (Nat.lt_of_succ_le huv).trans_le hv.le
  have hu1Lo : compute_start_slot_at_epoch cfg e < u + 1 :=
    ha.trans_le (hau.trans (Nat.le_succ u))
  have hu1Hi : u + 1 < compute_start_slot_at_epoch cfg (e + 1) :=
    huv.trans_lt hv
  have hvLo : compute_start_slot_at_epoch cfg e ≤ v :=
    hu1Lo.le.trans huv
  exact estimate_additive cfg tab a u v hau huv
    (no_full_coverage_inside_epoch_after_start cfg e a v ha hv)
    (no_full_coverage_inside_epoch_after_start cfg e a u ha huHi)
    (no_full_coverage_inside_epoch_after_start cfg e (u + 1) v hu1Lo hv)
    (by rw [hepoch a ha.le haHi, hepoch v hvLo hv])
    (by rw [hepoch a ha.le haHi, hepoch u (ha.le.trans hau) huHi])
    (by rw [hepoch (u + 1) hu1Lo.le hu1Hi,
      hepoch v hvLo hv])

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


/-- A confirmed live block is the exact produced root supported by all
honest votes from its slot through the live endpoint. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_one_confirmed_supports_live_votes
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
    ∀ j ∈ E.honest, ∀ t kt a',
      get_block_slot (E.store cfg ext w (q + 1)) b ≤ t →
      t < E.slot_at cfg m → E.vote j t = some (kt, a') →
        b ∈ (E.store cfg ext j kt).block_roots ∧
        is_ancestor (E.store cfg ext j kt)
          (get_node_for_root a'.data.beacon_block_root)
          (get_node_for_root b) = true := by
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
  simpa only [s, get_block_slot, hEq] using hsupport

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

/-- On nested committee windows, the equivocation score grows by at least
the weight of old supporters lost to newly recorded equivocation. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_equivocation_score_growth_with_loss
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
    (sa oldEnd newEnd : Slot) (hEnd : oldEnd ≤ newEnd)
    (hOldEndH : E.SlotWithinHorizon cfg oldEnd)
    (hNewEndH : E.SlotWithinHorizon cfg newEnd)
    (hLostSpan :
      (AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).toFinset \
        (AttSupporters cfg (E.store cfg ext w m)
          (get_node_for_root b) newSource).toFinset ⊆
        E.span_committee sa newEnd) :
    get_equivocation_score cfg ext (E.store cfg ext w n)
        oldSource sa oldEnd +
      E.weight ((AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).toFinset \
        (AttSupporters cfg (E.store cfg ext w m)
          (get_node_for_root b) newSource).toFinset) ≤
      get_equivocation_score cfg ext (E.store cfg ext w m)
        newSource sa newEnd := by
  let lost := (AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource).toFinset \
      (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource).toFinset
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
  have hequivMono := (E.store_storeLE cfg ext w hnm).2.2.1
  have hOldSubset : EquivActive cfg E (E.store cfg ext w n)
      oldSource sa oldEnd ⊆ EquivActive cfg E (E.store cfg ext w m)
        newSource sa newEnd := by
    intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi ⊢
    exact ⟨⟨E.span_committee_mono sa hEnd hi.1.1,
      hequivMono hi.1.2⟩, by rw [← hact i]; exact hi.2⟩
  have hLostEq := h.live_lost_supporters_newly_equivocating cfg ext E
    hw hnm hHn hHm holdCurrent hboundary hb hbEpoch
    oldSource newSource hvalOld hvalNew hOldH hNewH
  have hLostSubset : lost ⊆
      EquivActive cfg E (E.store cfg ext w m) newSource sa newEnd \
        EquivActive cfg E (E.store cfg ext w n) oldSource sa oldEnd := by
    intro i hi
    have hOldSupport : i ∈ AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource :=
      List.mem_toFinset.mp (Finset.mem_sdiff.mp hi).1
    have hactiveOld : is_active_validator
        (oldSource.validators.getD i default)
        (get_current_epoch cfg oldSource) = true := by
      simp only [AttSupporters, List.mem_filter,
        get_active_validator_indices] at hOldSupport
      exact hOldSupport.1.1.2
    have hactiveNew : is_active_validator
        (newSource.validators.getD i default)
        (get_current_epoch cfg newSource) = true := by
      rw [← hact i]
      exact hactiveOld
    have hnewEquiv := (Finset.mem_sdiff.mp (hLostEq hi)).1
    have holdNotEquiv := (Finset.mem_sdiff.mp (hLostEq hi)).2
    apply Finset.mem_sdiff.mpr
    constructor
    · simp only [EquivActive, Finset.mem_filter, Finset.mem_inter]
      exact ⟨⟨hLostSpan hi, hnewEquiv⟩, hactiveNew⟩
    · simp only [EquivActive, Finset.mem_filter, Finset.mem_inter]
      intro hmem
      exact holdNotEquiv hmem.1.2
  have hweight := E.weight_growth_of_new_equivocators hOldSubset
    hLostSubset
  rw [get_equivocation_score_eq_weight cfg ext
    h.trajectory.externals_coherence hw n hHn hvalOld sa oldEnd hOldEndH,
    get_equivocation_score_eq_weight cfg ext
      h.trajectory.externals_coherence hw m hHm hvalNew sa newEnd hNewEndH]
  exact hweight

set_option maxRecDepth 4096 in
/-- Old supporters of a known block are in every later span that starts no
later than the block slot and ends after the old call's vote cutoff. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_old_supporters_in_later_span
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (source : BeaconState Root)
    {sa endSlot : Slot}
    (hsa : sa ≤ ((E.store cfg ext w n).blocks b).slot)
    (hend : get_current_slot cfg (E.store cfg ext w n) - 1 ≤ endSlot) :
    (AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) source).toFinset ⊆
      E.span_committee sa endSlot := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hprov := E.latestMessageProvenance cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    hgen w n hw hHn
  rw [← E.store_current_slot cfg ext w n] at hprov
  have hwf := E.store_parentSlotLt cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure
    h.trajectory.wellFormed.anchor_parent_unscheduled w n
  have hwalkK := E.store_walkKnownK cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure w n
  intro i hi
  have hi' := List.mem_toFinset.mp hi
  have hspan := supporter_mem_span_committee cfg
    (E := E) (bs := source) (b := b) (i := i) (sa := sa)
    hwf hprov hi'
    (fun msg hmsg => by
      obtain ⟨_, _, _, _, _, _, _, hknown, _, _⟩ := hprov i msg hmsg
      exact hwalkK b hb msg.root hknown) hsa
  exact E.span_committee_mono sa hend hspan

/-- The score lost at the boundary is part of the old Byzantine supporter
weight, so it is covered by the old executable adversarial allowance. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_lost_weight_le_old_adversarial
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
    (hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext w n).blocks b).slot)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (htabOld : get_total_active_balance cfg oldSource = E.total_active cfg)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon) :
    E.weight ((AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).toFinset \
      (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource).toFinset) ≤
      get_adversarial_weight cfg ext (E.store cfg ext w n) oldSource b := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  let lost := (AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource).toFinset \
      (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource).toFinset
  have hLostEq := h.live_lost_supporters_newly_equivocating cfg ext E
    hw hnm hHn hHm holdCurrent hboundary hb hbEpoch
    oldSource newSource hvalOld hvalNew hOldH hNewH
  have hsubsetByz : lost ⊆
      ((AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).filter
        (fun i => i ∉ E.honest)).toFinset := by
    intro i hi
    have hOld := (Finset.mem_sdiff.mp hi).1
    have hNewEquiv := (Finset.mem_sdiff.mp (hLostEq hi)).1
    have hNotHonest : i ∉ E.honest := by
      intro hiHonest
      exact E.honest_not_equivocating cfg ext
        h.trajectory.honest_behavior h.trajectory.externals_coherence
        hgen hiHonest w m hw hHm hNewEquiv
    exact List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨List.mem_toFinset.mp hOld,
        decide_eq_true hNotHonest⟩)
  have hprov := E.latestMessageProvenance cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    hgen w n hw hHn
  rw [← E.store_current_slot cfg ext w n] at hprov
  have hwf := E.store_parentSlotLt cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure
    h.trajectory.wellFormed.anchor_parent_unscheduled w n
  have hwalkK := E.store_walkKnownK cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    h.trajectory.genesis_structure w n
  have hbyz := byz_score_le_adversarial_weight cfg ext
    h.trajectory.honest_behavior h.trajectory.externals_coherence
    h.completed_calls.byzantine_bound hgen hw hHn hwf hbH
    hvalOld htabOld hprov
    (fun i hi msg hmsg => by
      obtain ⟨_, _, _, _, _, _, _, hknown, _, _⟩ := hprov i msg hmsg
      exact hwalkK b hb msg.root hknown)
  rw [byz_score_eq_weight cfg hvalOld] at hbyz
  exact (weight_mono (E := E) hsubsetByz).trans hbyz

/-- The equivocation score of a live block's committee window is within the
configured cap at an accepted old call. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_equivocation_le_budget
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (source : BeaconState Root)
    (hval : source.validators = E.registry)
    (htab : get_total_active_balance cfg source = E.total_active cfg)
    {sa : Slot} (hsa : sa ≤ ((E.store cfg ext w n).blocks b).slot)
    (hsaH : E.SlotWithinHorizon cfg sa)
    (hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext w n) - 1)) :
    get_equivocation_score cfg ext (E.store cfg ext w n) source sa
        (get_current_slot cfg (E.store cfg ext w n) - 1) ≤
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg source) sa
        (get_current_slot cfg (E.store cfg ext w n) - 1) / 100 *
          cfg.confirmation_byzantine_threshold := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hne : ∀ i ∈ (E.store cfg ext w n).equivocating_indices,
      i ∉ E.honest := by
    intro i hi hiHonest
    exact E.honest_not_equivocating cfg ext
      h.trajectory.honest_behavior h.trajectory.externals_coherence
      hgen hiHonest w n hw hHn hi
  have hspan := h.live_old_supporters_in_later_span cfg ext E
    hw hHn hb source hsa (Nat.le_refl _)
  have hbound := byz_plus_equiv_le cfg ext
    h.trajectory.externals_coherence h.completed_calls.byzantine_bound
    hw hHn hval htab hne hsaH hendH
    (fun i hi _ => hspan (List.mem_toFinset.mpr hi))
  exact (Nat.le_add_left _ _).trans hbound

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
    h.trajectory.externals_coherence w t cp hkey hHt
    (hdiv := h.trajectory.whole_seconds) (hgen := hgen)
  refine ⟨htotal, ?_⟩
  simp only [compute_proposer_score]
  rw [htotal]






/-- Every delivered honest assignment after a fixed live block is in the
endpoint supporter set. This set inclusion, rather than just its score lower
bound, identifies the new voters that can be added without double counting. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.fixed_live_block_new_supporters
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hHm : E.WithinHorizon cfg m)
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
        E.slot_start cfg (t + 1) ≤ m) :
    HS ⊆ (AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root r) balanceSource).toFinset := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  intro i hiHS
  obtain ⟨hi, t, htH, hst, htm, hcommittee, hdelivery⟩ := hHS i hiHS
  obtain ⟨msg, hmsg, hanc⟩ := h.fixed_live_block_support_of_assignment
    cfg ext E hs0 hHm hsupport hst htm hi hcommittee hw hdelivery
  apply List.mem_toFinset.mpr
  apply mem_AttSupporters_of_honest_committee cfg ext
    h.trajectory.honest_behavior h.trajectory.externals_coherence
    h.completed_calls.static_validators hgen hval hbsH
    hi htH hcommittee hmsg
  · simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  · exact hw
  · exact hHm

/-- Honest assignments after an old call in one epoch are disjoint from the
old supporter set of a block from that epoch. An old supporter already used
its unique committee slot before the call. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_new_assignments_disjoint_old_supporters
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    {e : Epoch}
    (holdCurrent : get_current_store_epoch cfg (E.store cfg ext w n) = e)
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w n) b = e)
    (oldSource : BeaconState Root)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, ∃ t : Slot,
      get_current_slot cfg (E.store cfg ext w n) ≤ t ∧
      t < compute_start_slot_at_epoch cfg (e + 1) ∧
      i ∈ E.committee t) :
    Disjoint HS (AttSupporters cfg (E.store cfg ext w n)
      (get_node_for_root b) oldSource).toFinset := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hprov := E.latestMessageProvenance cfg ext
    h.trajectory.wellFormed h.trajectory.externals_coherence
    hgen w n hw hHn
  apply Finset.disjoint_left.mpr
  intro i hiHS hiOld
  obtain ⟨t, htLower, htUpper, htCommittee⟩ := hHS i hiHS
  have hiOld' := List.mem_toFinset.mp hiOld
  obtain ⟨msg, hmsg, _, _⟩ := mem_AttSupporters cfg hiOld'
  obtain ⟨_, _, _, _, hmsgEpoch, hbefore, hmsgCommittee, _, _, hmsgSlot⟩ :=
    hprov i msg hmsg
  have hOldEpoch := h.live_supporter_message_epoch cfg ext E
    hw hHn holdCurrent hb hbEpoch oldSource hiOld' hmsg
  have htEpochLower : e ≤ compute_epoch_at_slot cfg t := by
    rw [← holdCurrent]
    exact Nat.div_le_div_right htLower
  have htEpochUpper : compute_epoch_at_slot cfg t ≤ e := by
    have hlt : compute_epoch_at_slot cfg t < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch] using htUpper
    exact Nat.lt_succ_iff.mp hlt
  have htEpoch : compute_epoch_at_slot cfg t = e :=
    Nat.le_antisymm htEpochUpper htEpochLower
  have hassignedSame := h.trajectory.externals_coherence.committee_assignment_unique
    i msg.slot t (by rw [hmsgSlot]; exact hmsgCommittee) htCommittee
    (by rw [hmsgSlot, hmsgEpoch, hOldEpoch, htEpoch])
  have hmsgBefore : msg.slot < get_current_slot cfg (E.store cfg ext w n) := by
    rw [E.store_current_slot cfg ext w n, hmsgSlot]
    exact Nat.lt_of_succ_le hbefore
  exact (Nat.ne_of_lt (hmsgBefore.trans_le htLower)) hassignedSame

/-- Added honest assignments after an old call raise the boundary support
score, with old supporters subsequently marked equivocating counted as the
only possible loss. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_score_growth
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hHn : E.WithinHorizon cfg n)
    (hHm : E.WithinHorizon cfg m)
    {e : Epoch}
    (holdCurrent : get_current_store_epoch cfg (E.store cfg ext w n) = e)
    {b : Root} (hb : b ∈ (E.store cfg ext w n).block_roots)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w n) b = e)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      s ≤ u → u < E.slot_at cfg m → E.vote j u = some (k, a) →
        b ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root b) = true)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        s ≤ t ∧ get_current_slot cfg (E.store cfg ext w n) ≤ t ∧
        t < E.slot_at cfg m ∧
        t < compute_start_slot_at_epoch cfg (e + 1) ∧
        i ∈ E.committee t ∧ E.slot_start cfg (t + 1) ≤ m) :
    get_attestation_score cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource + E.weight HS ≤
      get_attestation_score cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource +
        E.weight ((AttSupporters cfg (E.store cfg ext w n)
          (get_node_for_root b) oldSource).toFinset \
          (AttSupporters cfg (E.store cfg ext w m)
            (get_node_for_root b) newSource).toFinset) := by
  have hnew := h.fixed_live_block_new_supporters cfg ext E hs0 hHm
    hsupport hw newSource hvalNew hNewH HS
    (fun i hi => by
      obtain ⟨hiHonest, t, htH, hst, _, htm, _, hcommittee, hdelivery⟩ :=
        hHS i hi
      exact ⟨hiHonest, t, htH, hst, htm, hcommittee, hdelivery⟩)
  have hdisj := h.live_new_assignments_disjoint_old_supporters cfg ext E
    hw hHn holdCurrent hb hbEpoch oldSource HS
    (fun i hi => by
      obtain ⟨_, t, _, _, htLower, _, htUpper, hcommittee, _⟩ := hHS i hi
      exact ⟨t, htLower, htUpper, hcommittee⟩)
  have hadded : HS ⊆
      (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root b) newSource).toFinset \
        (AttSupporters cfg (E.store cfg ext w n)
          (get_node_for_root b) oldSource).toFinset := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hnew hi,
      fun hOld => (Finset.disjoint_left.mp hdisj) hi hOld⟩
  exact E.attestation_score_growth_with_loss cfg
    (E.store cfg ext w n) (E.store cfg ext w m)
    oldSource newSource (get_node_for_root b) hvalOld hvalNew HS hadded

/-- The arithmetic and vote-persistence core of per-block boundary
reconfirmation. Remaining inputs are the historical old confirmation and
exact same-epoch window geometry. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_reconfirm_of_window
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
    (hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext w n).blocks b).slot)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      s ≤ u → u < E.slot_at cfg m → E.vote j u = some (k, a) →
        b ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root b) = true)
    (oldSource newSource : BeaconState Root)
    (hvalOld : oldSource.validators = E.registry)
    (hvalNew : newSource.validators = E.registry)
    (hOldH : get_current_epoch cfg oldSource < E.verification_horizon)
    (hNewH : get_current_epoch cfg newSource < E.verification_horizon)
    (htabOld : get_total_active_balance cfg oldSource = E.total_active cfg)
    (htabNew : get_total_active_balance cfg newSource = E.total_active cfg)
    (hconfirmed : is_one_confirmed cfg ext
      (E.store cfg ext w n) oldSource b = true)
    (hOldDiscount : get_support_discount cfg ext
      (E.store cfg ext w n) oldSource b = 0)
    (hNewDiscount : get_support_discount cfg ext
      (E.store cfg ext w m) newSource b = 0)
    (sa added : ℕ)
    (hsa : sa ≤ ((E.store cfg ext w n).blocks b).slot)
    (hsaH : E.SlotWithinHorizon cfg sa)
    (hOldEndH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext w n) - 1))
    (hNewEndH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext w m) - 1))
    (hEnd : get_current_slot cfg (E.store cfg ext w n) - 1 ≤
      get_current_slot cfg (E.store cfg ext w m) - 1)
    (hstartOld :
      (if get_block_epoch cfg (E.store cfg ext w n) b >
          get_block_epoch cfg (E.store cfg ext w n)
            ((E.store cfg ext w n).blocks b).parent_root then
        compute_start_slot_at_epoch cfg
          (get_block_epoch cfg (E.store cfg ext w n) b)
       else ((E.store cfg ext w n).blocks b).slot) = sa)
    (hstartNew :
      (if get_block_epoch cfg (E.store cfg ext w m) b >
          get_block_epoch cfg (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks b).parent_root then
        compute_start_slot_at_epoch cfg
          (get_block_epoch cfg (E.store cfg ext w m) b)
       else ((E.store cfg ext w m).blocks b).slot) = sa)
    (hestimate : estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg newSource) sa
        (get_current_slot cfg (E.store cfg ext w m) - 1) =
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg oldSource) sa
        (get_current_slot cfg (E.store cfg ext w n) - 1) + added)
    (hOldDiv : 100 ∣ estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg oldSource) sa
      (get_current_slot cfg (E.store cfg ext w n) - 1))
    (hAddedDiv : 100 ∣ added)
    (hwindow : estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg newSource)
        (((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks b).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext w m) - 1) ≤
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg oldSource)
        (((E.store cfg ext w n).blocks
          ((E.store cfg ext w n).blocks b).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext w n) - 1) + added)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        s ≤ t ∧ get_current_slot cfg (E.store cfg ext w n) ≤ t ∧
        t < E.slot_at cfg m ∧
        t < compute_start_slot_at_epoch cfg (e + 1) ∧
        i ∈ E.committee t ∧ E.slot_start cfg (t + 1) ≤ m)
    (hhonest : 3 * added ≤ 4 * E.weight HS) :
    is_one_confirmed cfg ext (E.store cfg ext w m) newSource b = true := by
  let lost := E.weight ((AttSupporters cfg (E.store cfg ext w n)
    (get_node_for_root b) oldSource).toFinset \
    (AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root b) newSource).toFinset)
  have hscore := h.live_boundary_score_growth cfg ext E hw hHn hHm
    holdCurrent hb hbEpoch hs0 hsupport oldSource newSource
    hvalOld hvalNew hNewH HS hHS
  have hspan := h.live_old_supporters_in_later_span cfg ext E
    hw hHn hb oldSource hsa hEnd
  have hLostSpan :
      (AttSupporters cfg (E.store cfg ext w n)
        (get_node_for_root b) oldSource).toFinset \
        (AttSupporters cfg (E.store cfg ext w m)
          (get_node_for_root b) newSource).toFinset ⊆
        E.span_committee sa
          (get_current_slot cfg (E.store cfg ext w m) - 1) := by
    intro i hi
    exact hspan (Finset.mem_sdiff.mp hi).1
  have hequiv := h.live_equivocation_score_growth_with_loss cfg ext E
    hw hnm hHn hHm holdCurrent hboundary hb hbEpoch
    oldSource newSource hvalOld hvalNew hOldH hNewH
    sa _ _ hEnd hOldEndH hNewEndH hLostSpan
  have hlost := h.live_lost_weight_le_old_adversarial cfg ext E
    hw hnm hHn hHm holdCurrent hboundary hb hbEpoch hbH
    oldSource newSource hvalOld hvalNew htabOld hOldH hNewH
  have hOldEq := h.live_equivocation_le_budget cfg ext E
    hw hHn hb oldSource hvalOld htabOld hsa hsaH hOldEndH
  have hadversarial := get_adversarial_weight_quantized_growth_with_loss
    cfg ext (E.store cfg ext w n) (E.store cfg ext w m)
    oldSource newSource b sa added lost hstartOld hstartNew
    hestimate hOldDiv hAddedDiv hOldEq hlost hequiv
  have hboost : compute_proposer_score cfg newSource ≤
      compute_proposer_score cfg oldSource := by
    simp only [compute_proposer_score, htabOld, htabNew]
    exact le_rfl
  have hscorePositive := one_confirmed_requires_nonadversarial_support
    cfg ext (E.store cfg ext w n) oldSource b
    (by rw [hOldDiscount]; exact Nat.zero_le _) hconfirmed
  exact is_one_confirmed_reconfirm_of_growth_with_equivocation_loss
    cfg ext (E.store cfg ext w n) (E.store cfg ext w m)
    oldSource newSource b added (E.weight HS) lost
    hconfirmed hOldDiscount hNewDiscount hscore
    (hlost.trans_lt hscorePositive) hwindow hboost
    hadversarial hhonest

/-- The honest assignments from an old call slot through the previous
epoch's last slot supply the new-support set and its three-quarter weight
bound at the next boundary. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_added_honest_span
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {e : Epoch} {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : E.slot_at cfg m = compute_start_slot_at_epoch cfg (e + 1))
    (u s : Slot)
    (hstart : compute_start_slot_at_epoch cfg e ≤ u)
    (hu : u ≤ compute_start_slot_at_epoch cfg (e + 1) - 1)
    (hs : s ≤ u) :
    let z := compute_start_slot_at_epoch cfg (e + 1) - 1
    let HS := (E.span_committee u z).filter fun i => i ∈ E.honest
    (∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        s ≤ t ∧ u ≤ t ∧ t < E.slot_at cfg m ∧
        t < compute_start_slot_at_epoch cfg (e + 1) ∧
        i ∈ E.committee t ∧ E.slot_start cfg (t + 1) ≤ m) ∧
    3 * E.weight (E.span_committee u z) ≤ 4 * E.weight HS := by
  let z := compute_start_slot_at_epoch cfg (e + 1) - 1
  let HS := (E.span_committee u z).filter fun i => i ∈ E.honest
  dsimp only
  have hnextPos : 0 < compute_start_slot_at_epoch cfg (e + 1) := by
    simp only [compute_start_slot_at_epoch]
    exact Nat.mul_pos (Nat.succ_pos e) cfg.slots_per_epoch_pos
  have hzLt : z < compute_start_slot_at_epoch cfg (e + 1) :=
    Nat.sub_lt hnextPos (by omega)
  have hzH : E.SlotWithinHorizon cfg z :=
    E.slotWithinHorizon_of_le cfg (by rw [hboundary]; exact hzLt.le) hHm
  have huH : E.SlotWithinHorizon cfg u :=
    E.slotWithinHorizon_mono cfg hu hzH
  refine ⟨?_, h.honest_span_three_quarters cfg ext E u z huH hzH⟩
  intro i hi
  obtain ⟨hiSpan, hiHonest⟩ := Finset.mem_filter.mp hi
  simp only [Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc] at hiSpan
  obtain ⟨t, ⟨hut, htz⟩, hit⟩ := hiSpan
  have htLt : t < compute_start_slot_at_epoch cfg (e + 1) := htz.trans_lt hzLt
  have htH : E.SlotWithinHorizon cfg t :=
    E.slotWithinHorizon_mono cfg htz hzH
  have htEpoch : compute_epoch_at_slot cfg t = e := by
    have hlo : compute_start_slot_at_epoch cfg e ≤ t := hstart.trans hut
    have hge : e ≤ compute_epoch_at_slot cfg t := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hlo
    have hlt : compute_epoch_at_slot cfg t < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using htLt
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hge
  refine ⟨hiHonest, t, htH, hs.trans hut, hut, ?_, htLt, hit, ?_⟩
  · rw [hboundary]
    exact htLt
  · exact h.completed_epoch_vote_delivery cfg ext E (by rw [hboundary]) htEpoch

/-- The accepted full-epoch committee partition makes every suffix after the
epoch's first slot exact at the configured estimator. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_epoch_suffix_estimate_exact
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (store : Store Root) (e : Epoch)
    (hcurrent : get_current_store_epoch cfg store = e)
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hstartH : E.SlotWithinHorizon cfg (compute_start_slot_at_epoch cfg e))
    (hendH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg (e + 1) - 1))
    (u : Slot) (huLo : compute_start_slot_at_epoch cfg e < u)
    (huHi : u ≤ compute_start_slot_at_epoch cfg (e + 1) - 1) :
    E.weight (E.span_committee u
        (compute_start_slot_at_epoch cfg (e + 1) - 1)) =
      estimate_committee_weight_between_slots cfg (E.total_active cfg) u
        (compute_start_slot_at_epoch cfg (e + 1) - 1) := by
  let A := compute_start_slot_at_epoch cfg e
  let Z := compute_start_slot_at_epoch cfg (e + 1) - 1
  have hnext : compute_start_slot_at_epoch cfg (e + 1) =
      A + cfg.slots_per_epoch := by
    simp [A, compute_start_slot_at_epoch, Nat.add_mul]
  have hZeq : Z = A + (cfg.slots_per_epoch - 1) := by
    dsimp only [Z]
    rw [hnext]
    exact Nat.add_sub_assoc (Nat.succ_le_of_lt cfg.slots_per_epoch_pos) A
  have hZlt : Z < compute_start_slot_at_epoch cfg (e + 1) := by
    rw [hZeq, hnext]
    exact Nat.add_lt_add_left (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
  have hUprev : u - 1 + 1 = u :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) huLo))
  have hAprev : A ≤ u - 1 := Nat.le_sub_one_of_lt huLo
  have hprevH : E.SlotWithinHorizon cfg (u - 1) :=
    E.slotWithinHorizon_mono cfg ((Nat.sub_le u 1).trans huHi) hendH
  have huH : E.SlotWithinHorizon cfg u :=
    E.slotWithinHorizon_mono cfg huHi hendH
  have hsuccH : E.SlotWithinHorizon cfg (u - 1 + 1) := by
    rw [hUprev]
    exact huH
  have hepoch : ∀ x : Slot, A ≤ x → x < compute_start_slot_at_epoch cfg (e + 1) →
      compute_epoch_at_slot cfg x = e := by
    intro x hlo hhi
    have hge : e ≤ compute_epoch_at_slot cfg x := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [A, compute_start_slot_at_epoch, compute_epoch_at_slot] using hlo
    have hlt : compute_epoch_at_slot cfg x < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hhi
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hge
  have hAeq : currentTargetEpochStart cfg store = A := by
    simp [currentTargetEpochStart, A, hcurrent]
  have hEndEq : currentTargetEpochEnd cfg store = Z := by
    simp [currentTargetEpochEnd, hAeq, hZeq]
  have hAhi : A < compute_start_slot_at_epoch cfg (e + 1) :=
    (hAprev.trans ((Nat.sub_le u 1).trans huHi)).trans_lt hZlt
  have hPrevHi : u - 1 < compute_start_slot_at_epoch cfg (e + 1) :=
    ((Nat.sub_le u 1).trans huHi).trans_lt hZlt
  have hUhi : u < compute_start_slot_at_epoch cfg (e + 1) :=
    huHi.trans_lt hZlt
  have hZlo : A ≤ Z := hAprev.trans ((Nat.sub_le u 1).trans huHi)
  have hEpochAZ : compute_epoch_at_slot cfg A = compute_epoch_at_slot cfg Z := by
    rw [hepoch A (Nat.le_refl _) hAhi, hepoch Z hZlo hZlt]
  have hEpochAPrev : compute_epoch_at_slot cfg A =
      compute_epoch_at_slot cfg (u - 1) := by
    rw [hepoch A (Nat.le_refl _) hAhi, hepoch (u - 1) hAprev hPrevHi]
  have hEpochUZ : compute_epoch_at_slot cfg u = compute_epoch_at_slot cfg Z := by
    rw [hepoch u huLo.le hUhi, hepoch Z hZlo hZlt]
  have hCovLeft : is_full_validator_set_covered cfg A (u - 1) = false := by
    apply no_full_coverage_of_short_range cfg A (u - 1)
    rw [hUprev, ← hZeq]
    exact huHi
  have hCovRight : is_full_validator_set_covered cfg u Z = false :=
    no_full_coverage_inside_epoch_after_start cfg e u Z huLo hZlt
  have hfull := h.current_epoch_partial_window_exact cfg ext E store (u - 1)
    hcurrentH (by rw [hAeq]; exact hstartH)
    (by rw [hEndEq]; exact hendH) hprevH hsuccH
    (by rw [hAeq]; exact hAprev)
    (by rw [hEndEq, hUprev]; exact huHi)
    (by rw [hAeq, hEndEq]; exact hEpochAZ)
    (by rw [hAeq]; exact hCovLeft)
    (by rw [hEndEq, hUprev]; exact hCovRight)
    (by rw [hAeq]; exact hEpochAPrev)
    (by rw [hEndEq, hUprev]; exact hEpochUZ)
  simpa only [hEndEq, hUprev] using hfull.2

/-- Every keyed checkpoint balance source at an honest in-horizon store has
the static registry, an in-horizon epoch, and the anchored active total. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_cached_source_geometry
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {t : ℕ}
    (hHt : E.WithinHorizon cfg t) {cp : Checkpoint Root}
    (hkey : cp ∈ (E.store cfg ext w t).checkpoint_state_keys) :
    ((E.store cfg ext w t).checkpoint_states cp).validators = E.registry ∧
      get_current_epoch cfg ((E.store cfg ext w t).checkpoint_states cp) <
        E.verification_horizon ∧
      get_total_active_balance cfg
        ((E.store cfg ext w t).checkpoint_states cp) = E.total_active cfg := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hregistry := E.registryConstant cfg ext
    h.trajectory.externals_coherence hgen w t
  have hslot := (E.stateSlotsLE cfg ext h.trajectory.whole_seconds
    h.trajectory.externals_coherence hgen w t).2 cp hkey
  have hsourceH : get_current_epoch cfg
      ((E.store cfg ext w t).checkpoint_states cp) <
        E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hslot) hHt.2.2
  exact ⟨hregistry.2 cp hkey, hsourceH,
    (h.live_cached_source_accounting cfg ext E hw hHt hkey).1⟩

/-- A successful old one-block confirmation pins its source checkpoint key.
That key persists, so both the old and boundary sources have the static
registry, in-horizon epochs, and the same anchored total. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_confirmed_source_geometry_later
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n m : ℕ}
    (hnm : n ≤ m) (hHn : E.WithinHorizon cfg n)
    (hHm : E.WithinHorizon cfg m)
    (cp : Checkpoint Root) (b : Root)
    (hconfirmed : is_one_confirmed cfg ext (E.store cfg ext w n)
      ((E.store cfg ext w n).checkpoint_states cp) b = true) :
    let oldSource := (E.store cfg ext w n).checkpoint_states cp
    let newSource := (E.store cfg ext w m).checkpoint_states cp
    oldSource.validators = E.registry ∧
      newSource.validators = E.registry ∧
      get_current_epoch cfg oldSource < E.verification_horizon ∧
      get_current_epoch cfg newSource < E.verification_horizon ∧
      get_total_active_balance cfg oldSource = E.total_active cfg ∧
      get_total_active_balance cfg newSource = E.total_active cfg := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hkeyOld : cp ∈ (E.store cfg ext w n).checkpoint_state_keys :=
    E.checkpoint_state_key_of_one_confirmed cfg ext hgen w n cp b hconfirmed
  have hkeyNew : cp ∈ (E.store cfg ext w m).checkpoint_state_keys :=
    E.store_checkpointKeysLE cfg ext w hnm hkeyOld
  obtain ⟨hvalOld, hOldH, htabOld⟩ :=
    h.live_cached_source_geometry cfg ext E hw hHn hkeyOld
  obtain ⟨hvalNew, hNewH, htabNew⟩ :=
    h.live_cached_source_geometry cfg ext E hw hHm hkeyNew
  exact ⟨hvalOld, hvalNew, hOldH, hNewH, htabOld, htabNew⟩

/-- A one-confirmed known block at an actual call has an honest recorded
supporter from an earlier slot, so its slot precedes the call slot. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_one_confirmed_slot_before_call
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    get_block_slot (E.store cfg ext w (q + 1)) b < E.slot_at cfg (q + 1) := by
  let st := E.store cfg ext w (q + 1)
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
  have hancB' : (get_ancestor st (get_node_for_root lm.root)
      (st.blocks b).slot).root = b := by
    have hanc : is_ancestor st (get_node_for_root lm.root)
        (get_node_for_root b) = true := by
      simpa only [st, get_node_for_root, is_ancestor_supported_pending]
        using hancB
    simpa only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] using hanc
  have hslot := get_ancestor_slot_le hwf hwalk
  change (st.blocks (get_ancestor st (get_node_for_root lm.root)
    (st.blocks b).slot).root).slot ≤ (st.blocks lm.root).slot at hslot
  rw [hancB'] at hslot
  have huEq : lm.slot = u := by simpa only [hlmSlot]
  calc
    get_block_slot st b ≤ (st.blocks lm.root).slot := hslot
    _ ≤ aProv.data.slot := hlmRootSlot
    _ = lm.slot := hmsgSlot.symm
    _ = u := huEq
    _ < E.slot_at cfg (q + 1) := huEnd

end Execution

end FastConfirmation.Spec

end
