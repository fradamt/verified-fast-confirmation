module
public import FastConfirmation.Spec.Proof.Remainder
public import FastConfirmation.Spec.Proof.Growth

@[expose] public section

/-!
# Cross-epoch honest-class dynamics

The same-epoch growth lemmas use committee-assignment uniqueness to show that
an already-seen validator casts no vote at the next slot.  That argument is not
available across an epoch boundary, where the same validator can be assigned
again.  It is also unnecessary once the protocol proof knows the stronger,
semantic fact that every honest member of the next slot's committee supports
the selected block.

This module proves the corresponding endpoint-anchored dynamics.  Recurring
validators are handled directly: if they vote, the new vote supports the
selected block; if they do not, their previous class membership persists.
Consequently support grows by every genuinely new honest window member, the
sibling-stuck class shrinks, and the combined `A + X` non-supporter mass
shrinks, with no same-epoch hypothesis.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
private theorem combined_nonSupport_arith
    {J0 J1 S0 S1 A0 A1 X0 X1 : ℕ}
    (hJ : J0 ≤ J1) (hS : S0 + (J1 - J0) ≤ S1)
    (hpart0 : J0 = S0 + A0 + X0)
    (hpart1 : J1 = S1 + A1 + X1) :
    A1 + X1 ≤ A0 + X0 := by
  have hdiff : J0 + (J1 - J0) = J1 := Nat.add_sub_of_le hJ
  omega

/-- Every honest member assigned at slot `t` supports `b` when votes are
interpreted in the fixed endpoint store `(v₀,n₀)`.  The eventual safety proof
derives this from the slot-start safety induction hypothesis, honest
vote-your-head behavior, and forward block/ancestry transport into that
endpoint. -/
def CommitteeSupportsAt (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root)
    (t : Slot) : Prop :=
  ∀ i ∈ E.honest, i ∈ E.committee t →
    E.SupportsDesc cfg ext v₀ n₀ b t i

/-- Support-class growth for one arbitrary slot transition.  Unlike
`hSmono_of_fresh`, this theorem has no same-epoch premise: an old window member
who votes again is covered by `CommitteeSupportsAt`; one who does not vote
keeps its previous supporting latest message. -/
theorem hSmono_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo σ : Slot)
    (hsupport : E.CommitteeSupportsAt cfg ext v₀ n₀ b (σ + 1)) :
    E.Sval cfg ext v₀ n₀ b lo σ +
        E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b lo (σ + 1) := by
  classical
  set G := (E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
    (fun i => i ∈ E.honest) with hG
  have hSsub : E.Sclass cfg ext v₀ n₀ b lo σ ⊆
      E.Sclass cfg ext v₀ n₀ b lo (σ + 1) := by
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan, hhon⟩, hdesc⟩ := hi
    refine ⟨⟨E.span_committee_mono lo (Nat.le_succ σ) hspan, hhon⟩, ?_⟩
    by_cases hnone : E.vote i (σ + 1) = none
    · exact E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b σ hnone hdesc
    · exact hsupport i hhon
        (hhb.votes_assigned i hhon (σ + 1) hnone)
  have hGsub : G ⊆ E.Sclass cfg ext v₀ n₀ b lo (σ + 1) := by
    intro i hi
    have hi' := hi
    rw [hG, Finset.mem_filter, Finset.mem_sdiff] at hi'
    simp only [Execution.Sclass, Finset.mem_filter]
    exact ⟨⟨hi'.1.1, hi'.2⟩,
      hsupport i hi'.2 (E.mem_committee_of_fresh hi'.1.1 hi'.1.2)⟩
  have hdisj : Disjoint (E.Sclass cfg ext v₀ n₀ b lo σ) G := by
    rw [Finset.disjoint_left]
    intro i hiS hiG
    simp only [Execution.Sclass, Finset.mem_filter] at hiS
    rw [hG, Finset.mem_filter, Finset.mem_sdiff] at hiG
    exact hiG.1.2 hiS.1.1
  simp only [Execution.Sval]
  rw [← E.weight_union_disjoint hdisj]
  exact E.weight_mono (Finset.union_subset hSsub hGsub)

/-- Pointwise form of sibling-stuck antitonicity for one arbitrary slot
transition.  This is the set inclusion underlying
`hXmono_of_committee_support`; exporting it lets endpoint accounting split an
old window into a pre-region and a re-anchored sub-window without trying to
recover membership from a weight inequality. -/
theorem Xclass_succ_subset_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo σ : Slot)
    (hsupport : E.CommitteeSupportsAt cfg ext v₀ n₀ b (σ + 1)) :
    E.Xclass cfg ext v₀ n₀ b lo (σ + 1) ⊆
      E.Xclass cfg ext v₀ n₀ b lo σ := by
  classical
  intro i hi
  simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
  obtain ⟨⟨hspan1, hhon⟩, hnS, hnA⟩ := hi
  have hspan0 : i ∈ E.span_committee lo σ := by
    by_contra hnot
    exact hnS (hsupport i hhon (E.mem_committee_of_fresh hspan1 hnot))
  have hnone : E.vote i (σ + 1) = none := by
    by_contra hvote
    exact hnS (hsupport i hhon
      (hhb.votes_assigned i hhon (σ + 1) hvote))
  refine ⟨⟨hspan0, hhon⟩, ?_, ?_⟩
  · exact fun hS => hnS
      (E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b σ hnone hS)
  · exact fun hA => hnA
      (E.AncestorOrVoteless_succ_of_novote cfg ext v₀ n₀ b σ hnone hA)

/-- Sibling-stuck mass cannot grow over an arbitrary epoch boundary once the
whole next-slot honest committee supports the selected block. -/
theorem hXmono_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo σ : Slot)
    (hsupport : E.CommitteeSupportsAt cfg ext v₀ n₀ b (σ + 1)) :
    E.Xval cfg ext v₀ n₀ b lo (σ + 1) ≤
      E.Xval cfg ext v₀ n₀ b lo σ := by
  simp only [Execution.Xval]
  exact E.weight_mono
    (E.Xclass_succ_subset_of_committee_support cfg ext hhb v₀ n₀ b lo σ
      hsupport)

/-- Pointwise sibling-stuck antitonicity over an arbitrary multi-slot,
possibly multi-epoch window.  Every intervening honest committee supports the
selected block, so a validator still sibling-stuck at the endpoint was already
sibling-stuck at the base cutoff. -/
theorem Xclass_subset_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo : Slot)
    {es σ : Slot} (hes : es ≤ σ)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext v₀ n₀ b t) :
    E.Xclass cfg ext v₀ n₀ b lo σ ⊆
      E.Xclass cfg ext v₀ n₀ b lo es := by
  revert hsupport
  induction σ, hes using Nat.le_induction with
  | base =>
      intro _
      exact Finset.Subset.rfl
  | succ σ hes ih =>
      intro hsupport
      have hstep := E.Xclass_succ_subset_of_committee_support cfg ext hhb
        v₀ n₀ b lo σ
        (hsupport (σ + 1) (Nat.lt_succ_of_le hes) (le_refl _))
      have hprev := ih (fun t ht hle =>
        hsupport t ht (hle.trans (Nat.le_succ σ)))
      exact hstep.trans hprev

/-- Support grows by the honest union growth over an arbitrary multi-epoch
window when each intervening honest committee supports the block. -/
theorem hgrowS_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo : Slot)
    {es σ : Slot} (hes : es ≤ σ)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext v₀ n₀ b t) :
    E.Sval cfg ext v₀ n₀ b lo es +
        (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext v₀ n₀ b lo σ := by
  apply E.hgrowS_of_steps cfg ext v₀ n₀ b lo hes
  intro σ' hlo hhi
  have hstep := E.hSmono_of_committee_support cfg ext hhb v₀ n₀ b lo σ'
    (hsupport (σ' + 1) (Nat.lt_succ_of_le hlo) (Nat.succ_le_of_lt hhi))
  rw [E.Jspec_eq_add_growth lo (Nat.le_succ σ'), Nat.add_sub_cancel_left]
  exact hstep

/-- Sibling-stuck mass is antitone over the same arbitrary multi-epoch
window. -/
theorem hgrowX_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo : Slot)
    {es σ : Slot} (hes : es ≤ σ)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext v₀ n₀ b t) :
    E.Xval cfg ext v₀ n₀ b lo σ ≤ E.Xval cfg ext v₀ n₀ b lo es := by
  apply E.hgrowX_of_steps cfg ext v₀ n₀ b lo hes
  intro σ' hlo hhi
  exact E.hXmono_of_committee_support cfg ext hhb v₀ n₀ b lo σ'
    (hsupport (σ' + 1) (Nat.lt_succ_of_le hlo) (Nat.succ_le_of_lt hhi))

/-- The combined non-supporter mass `A + X` is antitone across arbitrary
epoch boundaries.  This is the exact `hAX` input of the full-span re-anchored
crossing endpoint; it follows algebraically from support growth and the
`S/A/X` partition, without a recurrence or committee-seat disjointness claim. -/
theorem hgrowAX_of_committee_support
    (hhb : HonestBehavior cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b : Root) (lo : Slot)
    {es σ : Slot} (hes : es ≤ σ)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext v₀ n₀ b t) :
    E.Aval cfg ext v₀ n₀ b lo σ + E.Xval cfg ext v₀ n₀ b lo σ ≤
      E.Aval cfg ext v₀ n₀ b lo es + E.Xval cfg ext v₀ n₀ b lo es := by
  have hJ := E.Jspec_mono lo hes
  have hS := E.hgrowS_of_committee_support cfg ext hhb v₀ n₀ b lo hes hsupport
  have hpart0 := E.weight_partition cfg ext v₀ n₀ b lo es
  have hpart1 := E.weight_partition cfg ext v₀ n₀ b lo σ
  exact combined_nonSupport_arith hJ hS hpart0 hpart1

end Execution

end FastConfirmation.Spec

end
