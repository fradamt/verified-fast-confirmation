module
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.Discount.HonestWeight

@[expose] public section

/-!
# Spec / Proof / EconomicCore

Tracks honest descendant support and voteless validators across slots.

This module contains `SupportsDesc_succ_of_novote`, `AncestorOrVoteless_succ_of_novote`, `novote_succ_of_span` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)




/-! ## Section 2 — the migration Finset algebra (`hSmono`/`hXmono`)

The pre-`T1` per-slot deltas of `IHMechanize.hdeltas_of_monotone` reduce, in the
same-epoch regime, to two Finset facts about the honest class sets as the window end
grows `σ' → σ' + 1`: `Sclass` grows by (at least) the fresh honest committee, and
`Xclass` never grows. This section **mechanizes that set algebra** down to the single
genuine store-dynamics crux — that every *fresh* honest window member of slot `σ' + 1`
supports `desc(b′)` (`hfresh`, from `votes_head` + the head-safety IH + the closed
vote-landing bundle). The same-epoch bookkeeping (`votes_assigned` +
`committee_assignment_unique`: a non-fresh window member casts no vote at `σ' + 1`, so its
class membership is preserved) is discharged here in full. -/

/-- **`SupportsDesc` is preserved by a no-vote step.** If `i` casts no vote at `σ' + 1`,
its newest-by-`σ'` supporting vote is still newest by `σ' + 1`, so `SupportsDesc σ'` lifts
to `SupportsDesc (σ' + 1)`. -/
theorem SupportsDesc_succ_of_novote (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ' : Slot)
    {i : ValidatorIndex} (hnovote : E.vote i (σ' + 1) = none)
    (h : E.SupportsDesc cfg ext v₀ n₀ b' σ' i) :
    E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i := by
  obtain ⟨t, k, a, htle, hvote, hnew, hanc⟩ := h
  refine ⟨t, k, a, le_trans htle (Nat.le_succ _), hvote, ?_, hanc⟩
  intro t' ht' ht'le
  rcases eq_or_lt_of_le ht'le with heq | hlt
  · rw [heq]; exact hnovote
  · exact hnew t' ht' (Nat.lt_succ_iff.mp hlt)

/-- **`AncestorOrVoteless` is preserved by a no-vote step.** As `SupportsDesc_succ_of_novote`
for the voteless / ancestor-voting predicate. -/
theorem AncestorOrVoteless_succ_of_novote (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ' : Slot)
    {i : ValidatorIndex} (hnovote : E.vote i (σ' + 1) = none)
    (h : E.AncestorOrVoteless cfg ext v₀ n₀ b' σ' i) :
    E.AncestorOrVoteless cfg ext v₀ n₀ b' (σ' + 1) i := by
  rcases h with hvoteless | ⟨t, k, a, htle, hvote, hnew, hanc⟩
  · refine Or.inl (fun t' ht'le => ?_)
    rcases eq_or_lt_of_le ht'le with heq | hlt
    · rw [heq]; exact hnovote
    · exact hvoteless t' (Nat.lt_succ_iff.mp hlt)
  · refine Or.inr ⟨t, k, a, le_trans htle (Nat.le_succ _), hvote, ?_, hanc⟩
    intro t' ht' ht'le
    rcases eq_or_lt_of_le ht'le with heq | hlt
    · rw [heq]; exact hnovote
    · exact hnew t' ht' (Nat.lt_succ_iff.mp hlt)

/-- **A non-fresh honest window member casts no vote at `σ' + 1`** (same-epoch). `i ∈
span lo σ'` is assigned at some slot `s ∈ [lo, σ']`; `committee_assignment_unique` (same
epoch) forbids a second assignment at `σ' + 1`, so `votes_assigned` (honest) forces
`vote i (σ' + 1) = none`. -/
theorem novote_succ_of_span (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    {i : ValidatorIndex} (hih : i ∈ E.honest) {lo σ' : Slot}
    (hmem : i ∈ E.span_committee lo σ')
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1)) :
    E.vote i (σ' + 1) = none := by
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hmem
  obtain ⟨s, ⟨hslo, hshi⟩, hcomm⟩ := hmem
  by_contra hne
  have hcomm' : i ∈ E.committee (σ' + 1) := hhb.votes_assigned i hih (σ' + 1) hne
  have hseq : s = σ' + 1 :=
    hec.committee_assignment_unique i s (σ' + 1) hcomm hcomm' (hsame s hslo hshi)
  subst hseq
  exact absurd hshi (Nat.not_succ_le_self σ')

omit [LinearOrder Root] [Inhabited Root] in
/-- **Disjoint-union weight.** `weight (A ∪ B) = weight A + weight B` for disjoint `A`, `B`. -/
theorem weight_union_disjoint {A B : Finset ValidatorIndex} (h : Disjoint A B) :
    E.weight (A ∪ B) = E.weight A + E.weight B := by
  simp only [Execution.weight]; exact Finset.sum_union h

/-- **`hSmono` from the fresh-support crux** (`EconomicCore`, item 1). In the same-epoch regime the
honest support grows by (at least) the fresh honest committee: `Sclass σ'` lifts into
`Sclass (σ' + 1)` (non-fresh members cast no vote, `SupportsDesc` preserved) and the fresh
honest window growth `G := (span lo (σ'+1) \ span lo σ').filter honest` lands in
`Sclass (σ' + 1)` by `hfresh`, disjointly. Hence
`Sval σ' + weight G ≤ Sval (σ' + 1)` — exactly `hdeltas_of_monotone`'s `hSmono`. -/
theorem hSmono_of_fresh (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hfresh : ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
        (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i) :
    E.Sval cfg ext v₀ n₀ b' lo σ' +
        E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1) := by
  classical
  set G := (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter (fun i => i ∈ E.honest)
    with hGdef
  have hSsub : E.Sclass cfg ext v₀ n₀ b' lo σ' ⊆ E.Sclass cfg ext v₀ n₀ b' lo (σ' + 1) := by
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan, hih⟩, hsupp⟩ := hi
    refine ⟨⟨E.span_committee_mono lo (Nat.le_succ _) hspan, hih⟩, ?_⟩
    exact E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b' σ'
      (E.novote_succ_of_span cfg ext hhb hec hih hspan hsame) hsupp
  have hGsub : G ⊆ E.Sclass cfg ext v₀ n₀ b' lo (σ' + 1) := by
    intro i hi
    have hi' := hi
    rw [hGdef, Finset.mem_filter, Finset.mem_sdiff] at hi'
    simp only [Execution.Sclass, Finset.mem_filter]
    exact ⟨⟨hi'.1.1, hi'.2⟩, hfresh i hi⟩
  have hdisj : Disjoint (E.Sclass cfg ext v₀ n₀ b' lo σ') G := by
    rw [Finset.disjoint_left]
    intro i hiS hiG
    simp only [Execution.Sclass, Finset.mem_filter] at hiS
    rw [hGdef, Finset.mem_filter, Finset.mem_sdiff] at hiG
    exact hiG.1.2 hiS.1.1
  simp only [Execution.Sval]
  rw [← E.weight_union_disjoint hdisj]
  exact E.weight_mono (Finset.union_subset hSsub hGsub)

/-- **`hXmono` from the fresh-support crux** (`EconomicCore`, item 1). In the same-epoch regime the
sibling-stuck honest class never grows: `Xclass (σ'+1) ⊆ Xclass σ'`. A member of
`Xclass (σ'+1)` cannot be fresh (`hfresh` would make it `SupportsDesc`, hence not `Xclass`),
so it is a non-fresh window member; as such it casts no vote at `σ' + 1`, so both class
predicates are preserved backwards. Hence `Xval (σ' + 1) ≤ Xval σ'` — `hdeltas_of_monotone`'s
`hXmono`. -/
theorem hXmono_of_fresh (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hfresh : ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
        (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i) :
    E.Xval cfg ext v₀ n₀ b' lo (σ' + 1) ≤ E.Xval cfg ext v₀ n₀ b' lo σ' := by
  classical
  have hsub : E.Xclass cfg ext v₀ n₀ b' lo (σ' + 1) ⊆ E.Xclass cfg ext v₀ n₀ b' lo σ' := by
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan1, hih⟩, hnS, hnA⟩ := hi
    -- i is not fresh: freshness would give `SupportsDesc (σ'+1)`, contradicting `hnS`.
    have hspan0 : i ∈ E.span_committee lo σ' := by
      by_contra hnot
      exact hnS (hfresh i (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hspan1, hnot⟩, hih⟩))
    have hnovote := E.novote_succ_of_span cfg ext hhb hec hih hspan0 hsame
    refine ⟨⟨hspan0, hih⟩, ?_, ?_⟩
    · exact fun hS => hnS (E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b' σ' hnovote hS)
    · exact fun hA => hnA (E.AncestorOrVoteless_succ_of_novote cfg ext v₀ n₀ b' σ' hnovote hA)
  simp only [Execution.Xval]
  exact E.weight_mono hsub

end Execution

end FastConfirmation.Spec

end
