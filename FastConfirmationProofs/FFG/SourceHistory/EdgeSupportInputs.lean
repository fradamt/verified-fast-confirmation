module
public import FastConfirmationProofs.Discount.Confinement
public import FastConfirmationProofs.Discount.ByzantineSiblingWeight
public import FastConfirmationProofs.Checkpoints.EdgeWeightAlgebra
public import FastConfirmationProofs.Execution.Delivery.VoteDeliveryMargin
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / EdgeResiduals

Bounds the Byzantine and honest vote support used by an FFG source edge.

This module contains `bwin_of_bbad_or_spent`, `byz_confinement_bwin` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hByz`: byz sibling supporters land in `Bwin lo σ` -/

/-- **`BbadSet lo es ∪ SpentSet es σ ⊆ Bwin lo σ`.** The two byz destinations of
`ByzVpre.byz_sibling_confinement` both weigh into the window byz set `Bwin lo σ`: the base
enemy `BbadSet lo es` sits in `Bwin lo es ⊆ Bwin lo σ` (`span_committee_mono`, `es ≤ σ`);
the tail `SpentSet es σ = span (es+1) σ .filter (∉honest)` sits in `Bwin lo σ`
(`span_committee_mono_lo`, `lo ≤ es+1`). -/
theorem bwin_of_bbad_or_spent {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    (hlo : lo ≤ es + 1) (hes : es ≤ σ) {i : ValidatorIndex}
    (hi : i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    i ∈ E.Bwin lo σ := by
  simp only [Execution.Bwin, Finset.mem_filter]
  rcases hi with hb | hs
  · simp only [Execution.BbadSet, Finset.mem_filter] at hb
    exact ⟨E.span_committee_mono lo hes hb.1.1, hb.1.2⟩
  · simp only [Execution.SpentSet, Finset.mem_filter] at hs
    exact ⟨span_committee_mono_lo hlo hs.1, hs.2⟩

/-- **`hByz` core (confirm-margin `Bwin` shape).** A byz supporter of a filtered sibling
`c'` of the `b`-side child `c` at `(w, m)` lands in the window byz set `Bwin lo σ`. Composes
`ByzVpre.byz_sibling_confinement` (byz sibling supporter `∈ BbadSet lo es ∪ SpentSet es σ`)
with `bwin_of_bbad_or_spent`. The `hByz` field of `AnchorClose.ForkEdgeConfirmMarginSupply`
in `Bwin` shape (vs. the v2 `BbadSet ∪ SpentSet`). -/
theorem byz_confinement_bwin
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es σ : Slot}
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hloes : lo ≤ es + 1) (hes : es ≤ σ)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hib : i ∉ E.honest) :
    i ∈ E.Bwin lo σ :=
  E.bwin_of_bbad_or_spent cfg ext hloes hes
    (E.byz_sibling_confinement cfg ext hprov hwf hwalkK hb hc hc' hh hpc hpc' hne hbc hlo hσcur
      hlmknown hi_supp hib)

/-! ## Section 2 — `hHon`: honest sibling supporters land in `Xclass w m b lo σ` -/


/-! ## Section 3 — `hSmem`: `Sclass` members support the `b`-side child `c` -/



end Execution

end FastConfirmation.Spec

end
