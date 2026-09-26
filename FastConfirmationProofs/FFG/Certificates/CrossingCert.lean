module
public import FastConfirmationProofs.FFG.Certificates.CertExtract
public import FastConfirmationProofs.Monotonicity.Growth
public import FastConfirmationProofs.Checkpoints.EdgeWeightAlgebra

@[expose] public section

/-!
# Spec / Proof / CrossingCert: the full-span crossing certificate

The crossing arm is re-anchored at the confirmed block's slot.  Its confirmation
charge still uses the rule's full parent-to-current window and the crossing
`get_adversarial_weight` span.  This module packages those quantities without
assuming that raw slot spans on opposite sides of an epoch boundary have
disjoint validator sets.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

private theorem crossing_hbase_arith {H B d rhs S : ℕ}
    (h : 2 * (H + B) + d ≥ rhs) (hHS : H ≤ S) :
    2 * S + 2 * B + d ≥ rhs := by
  omega

private theorem slot_succ_le_epoch_start {spe parentSlot blockSlot : ℕ}
    (hspe : 0 < spe) (hcross : parentSlot / spe < blockSlot / spe) :
    parentSlot + 1 ≤ blockSlot / spe * spe := by
  have hq : parentSlot / spe + 1 ≤ blockSlot / spe := Nat.succ_le_of_lt hcross
  have hp : parentSlot < spe * (parentSlot / spe + 1) := by
    have he := Nat.div_add_mod parentSlot spe
    have hr := Nat.mod_lt parentSlot hspe
    rw [Nat.mul_add]
    omega
  calc
    parentSlot + 1 ≤ spe * (parentSlot / spe + 1) := hp
    _ ≤ spe * (blockSlot / spe) := Nat.mul_le_mul_left spe hq
    _ = blockSlot / spe * spe := Nat.mul_comm _ _

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- On the crossing branch, the slot after the parent is no later than the
first slot of the child's epoch. -/
theorem parent_slot_succ_le_crossing_start {store : Store Root} {b : Root}
    (hcross : get_block_epoch cfg store b >
      get_block_epoch cfg store (store.blocks b).parent_root) :
    (store.blocks (store.blocks b).parent_root).slot + 1
      ≤ compute_start_slot_at_epoch cfg (get_block_epoch cfg store b) := by
  simpa only [get_block_epoch, compute_epoch_at_slot, compute_start_slot_at_epoch] using
    slot_succ_le_epoch_start cfg.slots_per_epoch_pos hcross

/-! ## 1. The confirmation charge at the re-anchored window -/

/-- An honest recorded supporter belongs to the re-anchored support class
`Sclass (blocks b').slot es`.  The slot lower bound is exactly
`supporter_mem_span_committee` with the start slot specialized to the block
slot; reverse provenance supplies the ground newest vote used by `Sclass`. -/
private theorem recorded_supporter_mem_crossing_Sclass
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈
          (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀)) (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀)
          ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀
      ((E.store cfg ext v₀ n₀).blocks b').slot es)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
      (get_node_for_root b') bs)
    (hih : i ∈ E.honest) :
    i ∈ E.Sclass cfg ext v₀ n₀ b'
      ((E.store cfg ext v₀ n₀).blocks b').slot es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hi_supp
  have hspan : i ∈ E.span_committee
      ((E.store cfg ext v₀ n₀).blocks b').slot
      (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1) :=
    supporter_mem_span_committee (E := E) (store := E.store cfg ext v₀ n₀)
      (bs := bs) (b := b') (i := i)
      (sa := ((E.store cfg ext v₀ n₀).blocks b').slot)
      cfg hwf hprov hi_supp (hwalk i hi_supp) (le_refl _)
  have hspanEs : i ∈ E.span_committee
      ((E.store cfg ext v₀ n₀).blocks b').slot es := by
    simpa only [hes] using hspan
  obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
    E.recorded_lm_is_newest cfg ext hhb hec hgen hprov hes hih hlm
      (hdom i hih hspanEs lm hlm)
  simp only [Execution.Sclass, Finset.mem_filter]
  refine ⟨⟨?_, hih⟩, ?_⟩
  · exact hspanEs
  · refine ⟨t, k, a, htle, hvote, hnew, ?_⟩
    rw [hbbreq]
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc

/-- **Crossing `hbase` from a confirmed instance.**  The raw
`is_one_confirmed_ineq` score is split into honest and non-honest recorded
supporters.  Reverse provenance puts every honest supporter into the
re-anchored `Sval` window whose lower slot is `(blocks b').slot`; enlarging the
honest summand gives the certificate's base inequality. -/
theorem crossing_hbase_of_confirmed_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈
          (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    {bs : BeaconState Root} {b' : Root}
    (hval : bs.validators = E.registry)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀)) (E.store cfg ext v₀ n₀))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v₀ n₀) bs b' = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀)
          ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (es : Slot) (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀
      ((E.store cfg ext v₀ n₀).blocks b').slot es) :
    2 * E.Sval cfg ext v₀ n₀ b' ((E.store cfg ext v₀ n₀).blocks b').slot es
        + 2 * (((AttSupporters cfg (E.store cfg ext v₀ n₀)
            (get_node_for_root b') bs).filter (fun i => i ∉ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum
        + get_support_discount cfg ext (E.store cfg ext v₀ n₀) bs b'
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
        + compute_proposer_score cfg bs
        + 2 * get_adversarial_weight cfg ext (E.store cfg ext v₀ n₀) bs b' + 1 := by
  have hineq := is_one_confirmed_ineq cfg ext hconf
  rw [attestation_score_honest_split cfg E (E.store cfg ext v₀ n₀)
    (get_node_for_root b') bs] at hineq
  have hhonest :
      (((AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
        ≤ E.Sval cfg ext v₀ n₀ b' ((E.store cfg ext v₀ n₀).blocks b').slot es := by
    rw [honest_score_eq_weight cfg E hval, Execution.Sval]
    apply E.weight_mono
    intro i hi
    rw [List.mem_toFinset, List.mem_filter] at hi
    exact E.recorded_supporter_mem_crossing_Sclass cfg ext hhb hec hgen hwf hprov hes
      hwalk hdom hi.1 (of_decide_eq_true hi.2)
  exact crossing_hbase_arith hineq hhonest


/-! ## 2. Overlap-safe pre/sub accounting -/

/-- The pre-region of a crossing certificate is the part of the full committee
union not already present in the re-anchored sub-window.  This is deliberately
not `span_committee lo (mid - 1)`: validators may be assigned on both sides of
an epoch boundary. -/
def crossingPreRegion (lo mid es : Slot) : Finset ValidatorIndex :=
  E.span_committee lo es \ E.span_committee mid es

omit [LinearOrder Root] [Inhabited Root] in
/-- **Overlap-safe `hMU`.**  When `lo ≤ mid`, the sub-window and
`crossingPreRegion lo mid es` partition the full validator union exactly.
Consequently the rule's full-window estimate dominates the sub-window honest
and enemy mass plus the set-difference pre mass. -/
theorem crossing_hMU_of_preRegion (hbb : ByzantineWeightPremises cfg E)
    {bs : BeaconState Root}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    {lo mid es : Slot} (hlo : lo ≤ mid)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hesH : E.SlotWithinHorizon cfg es) :
    (E.Jspec mid es + E.Bval mid es) + E.weight (E.crossingPreRegion lo mid es)
      ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
  have hsub : E.span_committee mid es ⊆ E.span_committee lo es :=
    span_committee_mono_lo hlo
  calc
    (E.Jspec mid es + E.Bval mid es) + E.weight (E.crossingPreRegion lo mid es)
        = E.weight (E.span_committee mid es)
            + E.weight (E.span_committee lo es \ E.span_committee mid es) := by
              rw [E.Jspec_add_Bval_eq_weight_span]
              rfl
    _ = E.weight (E.span_committee lo es) := E.weight_add_sdiff hsub
    _ ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
            rw [htab]
            exact hbb.estimate_sound lo es hloH hesH

/-- Parent-stuck honest validators not already counted in the sub-window. -/
def crossingParentPre (store : Store Root) (bs : BeaconState Root) (b : Root)
    (mid es : Slot) : Finset ValidatorIndex :=
  ParentStuck cfg E store bs b \ E.span_committee mid es

/-- Parent-stuck honest validators that recur in, and are therefore already
counted by, the sub-window. -/
def crossingParentSub (store : Store Root) (bs : BeaconState Root) (b : Root)
    (mid es : Slot) : Finset ValidatorIndex :=
  ParentStuck cfg E store bs b ∩ E.span_committee mid es

/-- Honest validators in the overlap-safe pre-region. -/
def crossingHonestPre (lo mid es : Slot) : Finset ValidatorIndex :=
  (E.crossingPreRegion lo mid es).filter (fun i => i ∈ E.honest)

/-- Non-honest validators in the overlap-safe pre-region. -/
def crossingByzPre (lo mid es : Slot) : Finset ValidatorIndex :=
  (E.crossingPreRegion lo mid es).filter (fun i => i ∉ E.honest)

/-- Active equivocators present in a wide span but not already present in the
re-anchored sub-window. -/
def crossingEquivPre (store : Store Root) (bs : BeaconState Root)
    (lo mid es : Slot) : Finset ValidatorIndex :=
  EquivActive cfg E store bs lo es \ EquivActive cfg E store bs mid es

omit [LinearOrder Root] [Inhabited Root] in
/-- Wide-span-only active equivocators are non-honest members of the
overlap-safe pre-region. -/
theorem crossing_equivPre_subset_byzPre {store : Store Root} {bs : BeaconState Root}
    {lo mid es : Slot}
    (hne : ∀ i ∈ store.equivocating_indices, i ∉ E.honest) :
    E.crossingEquivPre cfg store bs lo mid es ⊆ E.crossingByzPre lo mid es := by
  intro i hi
  simp only [crossingEquivPre, Finset.mem_sdiff, EquivActive, Finset.mem_filter,
    Finset.mem_inter] at hi
  simp only [crossingByzPre, crossingPreRegion, Finset.mem_filter, Finset.mem_sdiff]
  refine ⟨⟨hi.1.1.1, ?_⟩, hne i hi.1.1.2⟩
  intro hiSub
  exact hi.2 ⟨⟨hiSub, hi.1.1.2⟩, hi.1.2⟩

/-- The full-span equivocation score is the sub-window score plus exactly the
wide-span-only active-equivocator mass. -/
theorem crossing_equivocation_score_split
    (hec : BeaconExternalsPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {sa mid es : Slot} (hsa : sa ≤ mid)
    (hsaA : E.anchorEpochStart cfg ≤ sa) (hesN : es ≤ E.slot_at cfg n) :
    get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
        + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es)
      = get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es := by
  rw [get_equivocation_score_eq_weight cfg ext hec hv n hnH hval mid es
      (hsaA.trans hsa) hesN,
    get_equivocation_score_eq_weight cfg ext hec hv n hnH hval sa es hsaA hesN]
  have hsub : EquivActive cfg E (E.store cfg ext v n) bs mid es ⊆
      EquivActive cfg E (E.store cfg ext v n) bs sa es := by
    intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi ⊢
    exact ⟨⟨span_committee_mono_lo hsa hi.1.1, hi.1.2⟩, hi.2⟩
  simpa only [crossingEquivPre] using E.weight_add_sdiff hsub

omit [LinearOrder Root] [Inhabited Root] in
/-- A sub-window plus the honest/non-honest parts of its overlap-safe wide
prefix is exactly the full-span committee mass. -/
theorem crossing_fullSpan_mass_split {sa mid es : Slot} (hsa : sa ≤ mid) :
    (E.Jspec mid es + E.Bval mid es)
        + (E.weight (E.crossingHonestPre sa mid es)
          + E.weight (E.crossingByzPre sa mid es))
      = E.Jspec sa es + E.Bval sa es := by
  have hsub : E.span_committee mid es ⊆ E.span_committee sa es :=
    span_committee_mono_lo hsa
  calc
    (E.Jspec mid es + E.Bval mid es)
          + (E.weight (E.crossingHonestPre sa mid es)
            + E.weight (E.crossingByzPre sa mid es))
        = E.weight (E.span_committee mid es)
            + E.weight (E.crossingPreRegion sa mid es) := by
              rw [E.Jspec_add_Bval_eq_weight_span,
                E.weight_split_honest (E.crossingPreRegion sa mid es)]
              rfl
    _ = E.weight (E.span_committee sa es) := E.weight_add_sdiff hsub
    _ = E.Jspec sa es + E.Bval sa es := (E.Jspec_add_Bval_eq_weight_span sa es).symm

omit [LinearOrder Root] [Inhabited Root] in
/-- The enemy mass has the matching exact split: sub-window enemy mass plus
wide-only non-honest pre mass equals full-span enemy mass. -/
theorem crossing_fullSpan_Bval_split {sa mid es : Slot} (hsa : sa ≤ mid) :
    E.Bval mid es + E.weight (E.crossingByzPre sa mid es) = E.Bval sa es := by
  have hsub : E.Bwin mid es ⊆ E.Bwin sa es := by
    exact Finset.filter_subset_filter _ (span_committee_mono_lo hsa)
  have hdiff : E.Bwin sa es \ E.Bwin mid es = E.crossingByzPre sa mid es := by
    ext i
    simp only [Execution.Bwin, crossingByzPre, crossingPreRegion, Finset.mem_filter,
      Finset.mem_sdiff]
    aesop
  rw [Execution.Bval, Execution.Bval, ← hdiff]
  exact E.weight_add_sdiff hsub

omit [LinearOrder Root] [Inhabited Root] in
/-- Widening only the lower endpoint enlarges the overlap-safe pre-region. -/
theorem crossingPreRegion_mono_lo {lo sa mid es : Slot} (hlo : lo ≤ sa) :
    E.crossingPreRegion sa mid es ⊆ E.crossingPreRegion lo mid es := by
  intro i hi
  simp only [crossingPreRegion, Finset.mem_sdiff] at hi ⊢
  exact ⟨span_committee_mono_lo hlo hi.1, hi.2⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- The non-honest part of the full adversarial prefix is included in the
parent-to-current pre-region whenever `lo ≤ sa`. -/
theorem crossingByzPre_mono_lo {lo sa mid es : Slot} (hlo : lo ≤ sa) :
    E.crossingByzPre sa mid es ⊆ E.crossingByzPre lo mid es := by
  exact Finset.filter_subset_filter _ (E.crossingPreRegion_mono_lo hlo)

/-- The canonical old-sibling honest pre mass: every honest pre-region member
not used as the outside-subwindow parent-stuck discount source. -/
def crossingXPre (store : Store Root) (bs : BeaconState Root) (b : Root)
    (lo mid es : Slot) : Finset ValidatorIndex :=
  E.crossingHonestPre lo mid es \ E.crossingParentPre cfg store bs b mid es

/-- Outside-subwindow parent-stuck validators are honest members of the
set-difference pre-region.  The upper-slot inclusion uses only
`b.slot ≤ current`; the sub-window exclusion is definitional. -/
theorem crossing_parentPre_subset_honestPre
    {v : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root} {es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hbcur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n)) :
    E.crossingParentPre cfg (E.store cfg ext v n) bs b
        ((E.store cfg ext v n).blocks b).slot es
      ⊆ E.crossingHonestPre
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        ((E.store cfg ext v n).blocks b).slot es := by
  intro i hi
  have hi' : i ∈ ParentStuck cfg E (E.store cfg ext v n) bs b \
      E.span_committee ((E.store cfg ext v n).blocks b).slot es := by
    simpa only [crossingParentPre] using hi
  obtain ⟨hiP, hiNotSub⟩ := Finset.mem_sdiff.mp hi'
  have hiRaw := (mem_ParentSupport cfg (Finset.mem_filter.mp hiP).1).1
  have hhigh : ((E.store cfg ext v n).blocks b).slot - 1 ≤ es := by
    rw [hes]
    exact Nat.sub_le_sub_right hbcur 1
  have hiFull := E.span_committee_mono
    (((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1) hhigh hiRaw
  simp only [crossingHonestPre, crossingPreRegion, Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨hiFull, hiNotSub⟩, (Finset.mem_filter.mp hiP).2⟩

/-- **Canonical overlap-safe `hMU`.**  The sub-window ledger partition plus
`ParentPre`, `XPre`, and `ByzPre` is exactly the full-window committee union;
the rule's full-window estimate therefore dominates this concrete coordinate
sum. -/
theorem crossing_hMU_of_canonicalPre (hbb : ByzantineWeightPremises cfg E)
    {v : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hbcur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n))
    (hloH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hesH : E.SlotWithinHorizon cfg es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    (E.Sval cfg ext v n b mid es + E.Aval cfg ext v n b mid es
        + E.Xval cfg ext v n b mid es + E.Bval mid es)
      + (E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
        + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.weight (E.crossingByzPre lo mid es))
      ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
  dsimp only
  have hparent := E.crossing_parentPre_subset_honestPre (bs := bs) cfg ext hes hbcur
  have hhonest := E.weight_add_sdiff hparent
  have hpre := E.weight_split_honest (E.crossingPreRegion
    (((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    ((E.store cfg ext v n).blocks b).slot es)
  have hlo : ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
      ≤ ((E.store cfg ext v n).blocks b).slot := hslotlt
  rw [← E.weight_partition cfg ext v n b
    ((E.store cfg ext v n).blocks b).slot es]
  rw [show E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b
          ((E.store cfg ext v n).blocks b).slot es)
        + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext v n).blocks b).slot es)
      = E.weight (E.crossingHonestPre
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext v n).blocks b).slot es) by
        simpa only [crossingXPre] using hhonest]
  rw [show E.weight (E.crossingHonestPre
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext v n).blocks b).slot es)
        + E.weight (E.crossingByzPre
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext v n).blocks b).slot es)
      = E.weight (E.crossingPreRegion
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext v n).blocks b).slot es) by
        simpa only [crossingHonestPre, crossingByzPre] using hpre.symm]
  exact E.crossing_hMU_of_preRegion cfg hbb htab hlo hloH hesH

/-- **Overlap-safe `hd`.**  The ordinary discount bound is split exactly into
the parent-stuck validators outside the sub-window and those already present
inside it.  No cross-epoch disjointness premise is used. -/
theorem crossing_hd_of_preRegion
    (hec : BeaconExternalsPremises cfg ext E) (hbb : ByzantineWeightPremises cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hpA : E.anchor_state.slot ≤
      ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks b).parent_root).slot)
    (hbN : ((E.store cfg ext v n).blocks b).slot ≤ E.slot_at cfg n)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    (mid es : Slot) :
    get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
        + E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b mid es) := by
  have hd := support_discount_le_parent_stuck (b := b) cfg ext hec hbb hv hnH hval
    hstartH hbH hpA hbN htab hne
  have hdiff :
      ParentStuck cfg E (E.store cfg ext v n) bs b \
          (ParentStuck cfg E (E.store cfg ext v n) bs b ∩ E.span_committee mid es)
        = ParentStuck cfg E (E.store cfg ext v n) bs b \ E.span_committee mid es := by
    ext i
    simp
  have hsplit := E.weight_add_sdiff
    (Finset.inter_subset_left :
      ParentStuck cfg E (E.store cfg ext v n) bs b ∩ E.span_committee mid es
        ⊆ ParentStuck cfg E (E.store cfg ext v n) bs b)
  rw [hdiff] at hsplit
  calc
    get_support_discount cfg ext (E.store cfg ext v n) bs b
        ≤ E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) := hd
    _ = E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b mid es) := by
            simpa only [crossingParentPre, crossingParentSub, add_comm] using hsplit.symm


/-! ## 3. The full-span crossing adversarial guard -/

/-- **Crossing full-span guard.**  On the crossing branch,
`get_adversarial_weight` starts at the first slot of `b`'s epoch.  The same
full span supplies both facts used by the k-independent endpoint arithmetic:
its actual honest-plus-enemy union is dominated by `100 * (estimate / 100)`,
and its floored adversarial budget is at most the net adversarial weight plus
the full-span equivocation score. -/
theorem crossing_fullSpan_adversarial_guard (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hcross : get_block_epoch cfg store b >
      get_block_epoch cfg store (store.blocks b).parent_root)
    (hes : es = get_current_slot cfg store - 1)
    (hsaH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)))
    (hesH : E.SlotWithinHorizon cfg es) :
    let sa := compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
    E.Jspec sa es + E.Bval sa es ≤
        100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100) ∧
      estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) sa es / 100
          * cfg.confirmation_byzantine_threshold
        ≤ get_adversarial_weight cfg ext store bs b
          + get_equivocation_score cfg ext store bs sa es := by
  subst es
  dsimp only
  constructor
  · rw [E.Jspec_add_Bval_eq_weight_span]
    exact E.weight_span_le_estimate cfg hbb htab _ _ hsaH hesH
  · have hguard := qV_le_get_adversarial_add_eqV (cfg := cfg) (ext := ext)
      (store := store) (bs := bs) (b := b)
    simpa only [if_pos hcross] using hguard

/-! ## 4. Assemble the full-span endpoint certificate -/


/-! ## 5. Wire the endpoint certificate into one crossing descent step -/


end Execution

end FastConfirmation.Spec

end
