module
public import FastConfirmationPaper.HFC.Model.AnchorRule
public import FastConfirmationPaper.HFC.Proof.Justification

@[expose] public section

/-!
# HFC / Proof / FFGRule — the anchor bridge (Algorithm 1 ⇒ the GU-anchor precondition)

Part of making the §4 theorems about the paper's **Algorithm 1** (`isConfirmedNoCaching`) rather
than the semantic abstraction. Here we derive, from Algorithm 1's *local* current-epoch checks, the
GU-anchor precondition the never-filter consumes:

* `isConfirmedNoCaching`'s GU-anchor check `epoch(ruleGJBlock(b)) = epoch(t)−1` +
  `ruleGJBlock(b)` being AU-justified on `chain(b)` and visible through `OnChainAnchorInterface`
  gives
  `GreatestJustifiedAnchorPrecondition` directly
  (`greatestJustifiedAnchorPrecondition_of_confirmedNoCaching`).

The *semantic* gate `WillNoConflictingChkpBeJustified` is **not** derived here — the gate-free
Algorithm-1 never-filter (`FastConfirmationPaper/HFC/Proof/Algorithm1FilterSafety.lean` / `FastConfirmationPaper/HFC/Proof/CheckpointCertificate.lean`) bypasses it entirely,
driving comparability from `willChkpBeJustified` via the §4.1 certificate.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **Phase 2a — the anchor bridge.** Algorithm 1's current-epoch branch supplies the paper's
    `GreatestJustifiedAnchorInputs` precondition: an honest validator's `isConfirmedNoCaching(b,t)`
    in the current epoch (`epoch(b) = epoch(t)`) carries `epoch(ruleGJBlock(b)) = epoch(t)−1`.
    The selector is AU-justified on `chain(b)` by construction and becomes view-level `Justified`
    through `OnChainAnchorInterface`. Taking `GUc := ruleGJBlock(b)` discharges
    `GreatestJustifiedAnchorPrecondition` — the rule's own GU-anchor check, not an extra
    assumption. -/
theorem greatestJustifiedAnchorPrecondition_of_confirmedNoCaching (bal₀ : Stakes n)
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} {v : Validator n} {b : Block n} {t : Time}
    (hv : v ∈ fm.honest)
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b t)
    (hdel : OnChainAnchorInterface bal₀ fm τ 𝒱 b t)
    (hcur : τ.epochOf b.slot = τ.epochOf (τ.slotOf t)) :
    GreatestJustifiedAnchorPrecondition bal₀ fm τ 𝒱 b t := by
  unfold isConfirmedNoCaching at hconf
  rw [if_pos hcur] at hconf
  obtain ⟨_hwill, hgjep, _hsafe⟩ := hconf
  refine ⟨ruleGJBlock bal₀ τ b, ?_, ruleGJBlock_block_le bal₀ τ b, v, hv, ?_⟩
  · rw [hgjep, hcur]
  · exact hdel.ruleGJBlock_justified hv (Timing.st_slotOf_le τ t)

/-- Algorithm 1's per-block predicate always carries the LMD-GHOST safety check, in either the
    current-epoch or previous-epoch branch. -/
theorem isLMDGHOSTSafe_of_isConfirmedNoCaching (bal₀ : Stakes n)
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} {v : Validator n} {b : Block n} {t : Time}
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b t) :
    isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v t) b t := by
  unfold isConfirmedNoCaching at hconf
  by_cases hcur : τ.epochOf b.slot = τ.epochOf (τ.slotOf t)
  · rw [if_pos hcur] at hconf
    exact hconf.2.2
  · rw [if_neg hcur] at hconf
    rcases hconf with ⟨_hfirst, _hwill, b', _hb'mem, _hbb', _hb'epoch, _hrec, hsafe⟩
    exact hsafe

/-- The Algorithm-1 highest-confirmed block is genesis or an actual `isConfirmedNoCaching`
    candidate from one of the validator's slot-boundary views. -/
theorem highestConfirmedAlg1_mem {τ : Timing} {fm : FaultModel n} {cm : Committees n}
    {pb we : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    (bal₀ : Stakes n) (v : Validator n) (e : Epoch) (t : Time) :
    highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v e t = Block.genesis ∨
    ∃ s', s' ∈ Finset.Icc (τ.fslot e + 1) (τ.slotOf t) ∧
      (highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v e t) ∈ (𝒱 v (τ.st s')).blocks ∧
      isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v
        (highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v e t) (τ.st s') := by
  unfold highestConfirmedSinceEpochAlg1 Alg1.highestConfirmedSinceEpoch
  extract_lets cand
  split
  · rename_i B harg
    right
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList] at hmem
    simp only [cand, Finset.mem_biUnion, Finset.mem_filter] at hmem
    obtain ⟨s', hs', hBblk, hBconf⟩ := hmem
    exact ⟨s', hs', hBblk, hBconf⟩
  · left; rfl

/-- The Algorithm-1 highest-confirmed block dominates every `isConfirmedNoCaching` candidate by
    slot. -/
theorem highestConfirmedAlg1_slot_ge_of_mem {τ : Timing} {fm : FaultModel n} {cm : Committees n}
    {pb we : Weight} {𝒱 : ViewFamily n (FFGVote n)} {v : Validator n} {e' : Epoch}
    {t' : Time} {B' : Block n} {s' : Slot} (bal₀ : Stakes n)
    (hs' : s' ∈ Finset.Icc (τ.fslot e' + 1) (τ.slotOf t'))
    (hmem : B' ∈ (𝒱 v (τ.st s')).blocks)
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v B' (τ.st s')) :
    B'.slot ≤ (highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v e' t').slot := by
  classical
  set cand : Finset (Block n) :=
    (Finset.Icc (τ.fslot e' + 1) (τ.slotOf t')).biUnion (fun s'' =>
      (𝒱 v (τ.st s'')).blocks.filter (fun b' =>
        isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b' (τ.st s''))) with hcand
  have hmemcand : B' ∈ cand := by
    rw [hcand, Finset.mem_biUnion]
    exact ⟨s', hs', Finset.mem_filter.mpr ⟨hmem, hconf⟩⟩
  unfold highestConfirmedSinceEpochAlg1 Alg1.highestConfirmedSinceEpoch
  simp only [← hcand]
  cases harg : cand.toList.argmax (·.slot) with
  | none =>
    rw [List.argmax_eq_none, Finset.toList_eq_nil] at harg
    rw [harg] at hmemcand
    simp at hmemcand
  | some B =>
    exact List.le_of_mem_argmax (Finset.mem_toList.mpr hmemcand) harg

end FastConfirmation.HFC

end
