module
public import Mathlib.Tactic
public import FastConfirmationPaper.LMDGhost.Proof.RuleSafety

@[expose] public section

/-!
# HFC / Proof / CanonicalReuse

The `flt`-generalized §3.1 canonical lemmas. Each is the corresponding
`FastConfirmation/Paper/LMDGhost/Proof/Rule.lean` lemma with the
hard-wired `trivialFilter` replaced by an arbitrary `(flt : BlockFilter n P)`
**parameter**. The filter never enters the weight machinery (`Q/S/H/J`) nor the
GHOST-head well-formedness argument, so the bodies transcribe verbatim — no
`NeverFiltered` hypothesis is needed for any of these three (it enters only the
engine/canonical *bridge*, already discharged at `ffgFilter` by
`hfc_canonical_from_engine`, Compose.lean).

These let the §3.1 monotonicity assembly (`proof_Theorem1_Monotonicity`, which is
`trivialFilter`-hardwired) be re-run at `flt := ffgFilter bal₀ τ` in
`Monotonicity.lean`, rather than cited (whose `trivialFilter`-bound proof does not
apply at the FFG filter).

Lemmas:

* `honest_member_supports_flt` (III.2) — generalizes `honest_member_supports`.
* `canonical_epoch_imp_safe_flt` (III.3) — generalizes `canonical_epoch_imp_safe`.
* `canonical_ancestor_of_slot_le_flt` (III.4) — generalizes
  `canonical_ancestor_of_slot_le`.

(III.1 `safe_canonical_from_engine_flt` already exists at `ffgFilter` as
`hfc_canonical_from_engine` in `Compose.lean`; `highestConfirmed_mem`,
`highestConfirmed_slot_ge_of_mem`, `safe_block_wf_slot` are already filter-free.)
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

section CanonicalReuse

variable {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight}
  {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
  {𝒱 : ViewFamily n P} {flt : BlockFilter n P}

/-- **III.2 — `honest_member_supports` at an arbitrary filter `flt`.** Verbatim port of
    `honest_member_supports` (Rule.lean:309) with `trivialFilter → flt`: the filter never
    enters the support/weight argument, so the body is unchanged. -/
theorem honest_member_supports_flt
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {s σ : Slot}
    (hgst : τ.AfterGST (τ.st s))
    (hHead : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      b ≼ forkChoiceHead τ (gj 𝒱 w t'') boost pb flt (𝒱 w t'') t'')
    {v : Validator n} {t' : Time} {i : Validator n} {k : Slot}
    (hv : v ∈ fm.honest) (hi : i ∈ fm.honest)
    (hik : i ∈ cm.member k) (hsk : s ≤ k) (hkσ : k ≤ σ) (hdeliv : τ.st (σ + 1) ≤ t') :
    (𝒱 v t').supportsLMD b' i σ = true := by
  -- `i` casts a vote at slot `k` for its own head at `st k`.
  obtain ⟨gv0, hgv0mem, hgv0slot, _⟩ := hHB.votesHead hi hik
  have hgst_low : τ.AfterGST (τ.st s) := hgst
  have hgst_k1 : τ.AfterGST (τ.st k) := by
    refine le_trans hgst_low ?_
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur hsk
  have hgst_gv0 : τ.AfterGST (τ.st gv0.slot) := by rw [hgv0slot]; exact hgst_k1
  -- deliver `gv0` into `𝒱 v t'`.
  have hge_gv0 : τ.st (gv0.slot + 1) ≤ t' := by
    rw [hgv0slot]
    refine le_trans ?_ hdeliv
    have : k + 1 ≤ σ + 1 := Nat.add_le_add_right hkσ 1
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur this
  have hgv0v : gv0 ∈ (𝒱 v t').votesOf i :=
    honest_vote_ubiquitous hSync hNF hi hi hgv0mem hv (le_refl gv0.slot) hge_gv0 hgst_gv0
  -- the latest vote of `i` at cutoff `σ` exists (≥ k ≥ s) and supports `b'`.
  have hgv0σ : gv0.slot ≤ σ := by rw [hgv0slot]; exact hkσ
  have hsome : ((𝒱 v t').latestVote i σ).isSome := latestVote_isSome hgv0v hgv0σ
  obtain ⟨gv1, hgv1⟩ := Option.isSome_iff_exists.mp hsome
  have hne := hHB.noEquivocation hi (w := v) (t := t')
  have hev : (𝒱 v t').effectiveVote i σ = some gv1 := by
    rw [effectiveVote_eq_latest hne, hgv1]
  have hgv1ge : gv0.slot ≤ gv1.slot := latestVote_is_max hgv1 hgv0v hgv0σ
  have hgv1_s : s ≤ gv1.slot := le_trans hsk (le_trans (le_of_eq hgv0slot.symm) hgv1ge)
  exact effHigh_supports hSync hNF hHB hb'b hgst_low
    (st0 := s) (σ := σ)
    (fun {kk} hkk1 hkk2 {j} hj => hHead hj (by
      exact_mod_cast Nat.mul_le_mul_right τ.slotDur hkk1))
    hv hi hev hgv1_s

/-- **III.3 — `canonical_epoch_imp_safe` at an arbitrary filter `flt`.** Verbatim port of
    `canonical_epoch_imp_safe` (Rule.lean:360) with `trivialFilter → flt`: the filter enters
    only `hHB`, `hHead`, and `forkChoiceHead_WellFormed` (already filter-generic). The weight
    machinery (Assumption 4 + `CommitteeCoversEpoch`) is filter-free. -/
theorem canonical_epoch_imp_safe_flt
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t))
    {b : Block n} {e : Epoch} {s : Slot}
    (hcover : CommitteeCoversEpoch τ cm e)
    (_hpb : 0 ≤ pb) (hβ4 : fm.β < (1 - pb) / 4)
    (_hbne : b ≠ Block.genesis) (hbepoch : b.slot < τ.fslot e) (hsfe : s ≤ τ.fslot e)
    (hgst : τ.AfterGST (τ.st s))
    (hHead : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      b ≼ forkChoiceHead τ (gj 𝒱 w t'') boost pb flt (𝒱 w t'') t'') :
    ∀ ⦃v : Validator n⦄ ⦃t' : Time⦄, v ∈ fm.honest → τ.st (τ.fslot (e + 1)) ≤ t' →
      isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v t') (𝒱 v t') b t' := by
  classical
  intro v t' hv ht'
  set A := gj 𝒱 v t' with hA
  have hEpos : 1 ≤ τ.slotsPerEpoch := τ.hSlotsPerEpoch
  -- Keep `slotOf t'` opaque so `omega` cannot unfold `/`,`*` into a false counterexample.
  set St' := τ.slotOf t' with hSt'
  set σ := St' - 1 with hσ
  -- `lslot e + 1 = fslot (e+1)` and `fslot e ≤ lslot e` (concrete `Nat` facts).
  have hfe1 : τ.fslot (e + 1) = τ.lslot e + 1 := by
    change (e + 1) * τ.slotsPerEpoch = e * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) + 1
    have hexp : (e + 1) * τ.slotsPerEpoch = e * τ.slotsPerEpoch + τ.slotsPerEpoch := by ring
    rw [hexp, Nat.add_assoc, Nat.sub_add_cancel hEpos]
  have hfe_le_le : τ.fslot e ≤ τ.lslot e := Nat.le_add_right _ _
  -- from `t' ≥ st(fslot(e+1))`, `slotOf t' ≥ fslot(e+1) = lslot e + 1`.
  have hslot_t' : τ.fslot (e + 1) ≤ St' := by
    rw [hSt', ← Timing.slotOf_st τ (τ.fslot (e + 1))]
    exact Nat.div_le_div_right ht'
  have hlslot1_le : τ.lslot e + 1 ≤ St' := by rw [← hfe1]; exact hslot_t'
  have hlslot_le_σ : τ.lslot e ≤ σ := by
    rw [hσ]; exact Nat.le_pred_of_lt (Nat.lt_of_succ_le hlslot1_le)
  -- `1 ≤ slotOf t'`: `slotOf t' ≥ lslot e + 1 ≥ 1`.
  have h1_st' : 1 ≤ St' := le_trans (Nat.le_add_left 1 _) hlslot1_le
  -- delivery deadline `st(σ+1) ≤ t'`: `σ + 1 = slotOf t'`, and `st(slotOf t') ≤ t'`.
  have hσ1 : σ + 1 = St' := by rw [hσ]; exact Nat.sub_add_cancel h1_st'
  have hdeliv : τ.st (σ + 1) ≤ t' := by rw [hσ1, hSt']; exact Timing.st_slotOf_le τ t'
  -- GST at `st(σ+1)`: `s ≤ fslot e ≤ lslot e ≤ σ < σ + 1`.
  have hs_le_σ1 : s ≤ σ + 1 :=
    le_trans hsfe (le_trans hfe_le_le (le_trans hlslot_le_σ (Nat.le_succ σ)))
  have hgst_σ1 : τ.AfterGST (τ.st (σ + 1)) := by
    refine le_trans hgst ?_
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur hs_le_σ1
  -- The per-ancestor `isOneConfirmed` goal.
  intro b' hb'b
  by_cases hb'g : b' = Block.genesis
  · exact Or.inl hb'g
  right
  -- `st s ≤ t'`: `s ≤ σ + 1 = slotOf t'`, and `st(slotOf t') ≤ t'`.
  have hst_s_t' : τ.st s ≤ t' := by
    refine le_trans ?_ hdeliv
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur hs_le_σ1
  -- `b'.slot < fslot e`: `b' ≼ b`, `b` well-formed (it is on a head), `b.slot < fslot e`.
  have hbwf : b.WellFormed :=
    WellFormed_of_ancestor (hHead (w := v) (t'' := t') hv hst_s_t')
      (forkChoiceHead_WellFormed (τ := τ) A flt (𝒱 v t') t')
  have hb'wf : b'.WellFormed := WellFormed_of_ancestor hb'b hbwf
  have hb'slot : b'.slot < τ.fslot e :=
    lt_of_le_of_lt (slot_le_of_ancestor hb'b hbwf) hbepoch
  -- `psPlus1 b' ≤ b'.slot` (well-formed, non-genesis): parent slot `<` own slot.
  have hpsp_le : b'.psPlus1 ≤ b'.slot := by
    cases hb'c : b' with
    | genesis => exact absurd hb'c hb'g
    | mk bid p ss =>
      have hlt : p.slot < ss := by rw [hb'c] at hb'wf; exact hb'wf.1
      simp only [Block.psPlus1, Block.parentSlot, Block.slot]
      exact hlt
    | mkWithVotes bid p ss votes =>
      have hlt : p.slot < ss := by rw [hb'c] at hb'wf; exact hb'wf.1
      simp only [Block.psPlus1, Block.parentSlot, Block.slot]
      exact hlt
  -- the epoch-`e` committee slots `[fslot e, lslot e]` sit inside `[psPlus1 b', σ]`.
  have hpsp_fe : b'.psPlus1 ≤ τ.fslot e := le_trans hpsp_le (le_of_lt hb'slot)
  have hsub : (Finset.Icc (τ.fslot e) (τ.lslot e)).biUnion cm.member
      ⊆ committeeUnion cm b'.psPlus1 σ := by
    unfold committeeUnion
    apply Finset.biUnion_subset_biUnion_of_subset_left
    apply Finset.Icc_subset_Icc hpsp_fe hlslot_le_σ
  -- **Coverage**: `committeeUnion cm b'.psPlus1 σ = univ` (epoch union ⊆ it, and = univ).
  have hcovE : (Finset.Icc (τ.fslot e) (τ.lslot e)).biUnion cm.member = Finset.univ := hcover
  have hcovU : committeeUnion cm b'.psPlus1 σ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    apply hsub
    rw [hcovE]; exact Finset.mem_univ x
  -- `W = totalWeight univ`, `Wp = pb · totalWeight univ`, so `Wp/W = pb`.
  have hWeq : W A cm b' σ = totalWeight A Finset.univ := by
    unfold W; rw [hcovU]
  have hWpos : 0 < W A cm b' σ := by
    rw [hWeq]
    exact totalWeight_pos A ⟨v, Finset.mem_univ v⟩
  have hWne : W A cm b' σ ≠ 0 := ne_of_gt hWpos
  -- **`H = J`**: every honest committee member supports `b'`.
  have hHJ : H A cm fm (𝒱 v t') b' σ = J A cm fm b' σ := by
    unfold H J totalWeight
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro i hi
    rcases Classical.em (i ∈ fm.honest) with hih | hih
    · -- honest `i ∈ univ`: by epoch coverage it is in some committee of epoch `e`.
      have hiU_ep : i ∈ (Finset.Icc (τ.fslot e) (τ.lslot e)).biUnion cm.member := by
        rw [hcovE]; exact Finset.mem_univ i
      rw [Finset.mem_biUnion] at hiU_ep
      obtain ⟨k, hk, hik⟩ := hiU_ep
      rw [Finset.mem_Icc] at hk
      have hsk : s ≤ k := le_trans hsfe hk.1
      have hkσ : k ≤ σ := le_trans hk.2 hlslot_le_σ
      have hsupp := honest_member_supports_flt hSync hNF hHB hb'b hgst hHead hv hih hik
        hsk hkσ hdeliv
      simp only [hih, true_and, iff_true]
      exact hsupp
    · simp only [hih, false_and]
  -- **`Q ≥ 1 - β`**: `S ≥ H = J`, and `J ≥ (1-β)W`.
  have hSH : H A cm fm (𝒱 v t') b' σ ≤ S A cm (𝒱 v t') b' σ := H_le_S A cm fm (𝒱 v t') b' σ
  have hJW : (1 - fm.β) * W A cm b' σ ≤ J A cm fm b' σ := by
    have := hcm (w := v) (t := t') b'.psPlus1 σ
    simpa [W, J] using this
  -- assemble `Q > ½(1 + Wp/W) + β`.
  unfold isOneConfirmed safetyThreshold
  rw [← hSt', ← hσ]
  have hWpeq : Wp A pb / W A cm b' σ = pb := by
    unfold Wp; rw [hWeq, mul_div_assoc, div_self (by
      have : (0 : Weight) < totalWeight A Finset.univ := totalWeight_pos A ⟨v, Finset.mem_univ v⟩
      exact ne_of_gt this), mul_one]
  rw [hWpeq]
  -- `Q = S/W ≥ J/W = (since J ≥ (1-β)W) ≥ 1-β > ½(1+pb)+β`.
  change S A cm (𝒱 v t') b' σ / W A cm b' σ > (1 / 2) * (1 + pb) + fm.β
  rw [gt_iff_lt, lt_div_iff₀ hWpos]
  have hSge : (1 - fm.β) * W A cm b' σ ≤ S A cm (𝒱 v t') b' σ := by
    calc (1 - fm.β) * W A cm b' σ ≤ J A cm fm b' σ := hJW
      _ = H A cm fm (𝒱 v t') b' σ := hHJ.symm
      _ ≤ S A cm (𝒱 v t') b' σ := hSH
  -- Assumption-4 close: `(½(1+pb)+β)·W < (1-β)·W ≤ S` since `½(1+pb)+β < 1-β ⟺ β<(1-pb)/4`.
  have hthr : (1 / 2) * (1 + pb) + fm.β < 1 - fm.β := by linarith [hβ4]
  calc ((1 / 2) * (1 + pb) + fm.β) * W A cm b' σ
      < (1 - fm.β) * W A cm b' σ := by
        apply mul_lt_mul_of_pos_right hthr hWpos
    _ ≤ S A cm (𝒱 v t') b' σ := hSge

/-- **III.4 — `canonical_ancestor_of_slot_le` at an arbitrary filter `flt`.** Verbatim port
    of `canonical_ancestor_of_slot_le` (Rule.lean:255) with `trivialFilter → flt`: comparability
    of two head-ancestors and the slot-ordered selection are filter-free; only the three head
    references carry the filter. -/
theorem canonical_ancestor_of_slot_le_flt {w : Validator n} {t' : Time} {B B' : Block n}
    (hB : B ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb flt (𝒱 w t') t')
    (hB' : B' ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb flt (𝒱 w t') t')
    (hHeadWf : (forkChoiceHead τ (gj 𝒱 w t') boost pb flt (𝒱 w t') t').WellFormed)
    (hslot : B.slot ≤ B'.slot) : B ≼ B' := by
  -- `B`, `B'` are comparable (both ancestors of the head); the slot bound picks the order.
  rcases ancestor_comparable hB hB' with h | h
  · exact h
  · -- `B' ≼ B`, and `B'.slot ≥ B.slot`, while ancestry forces `B'.slot ≤ B.slot` (head WF
    -- ⇒ `B` WF ⇒ `B'` WF and slot-monotone), so `B = B'`.
    have hBwf : B.WellFormed := WellFormed_of_ancestor hB hHeadWf
    have hB'le : B'.slot ≤ B.slot := slot_le_of_ancestor h hBwf
    have heq : B' = B := eq_of_ancestor_slot h hBwf (le_antisymm hB'le hslot)
    rw [heq]; exact Block.Ancestor.refl B

end CanonicalReuse

end FastConfirmation.LMDGhost

end
