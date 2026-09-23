module
public import FastConfirmationPaper.HFC.Proof.Justification
public import FastConfirmationPaper.HFC.Model.HonestFFG
public import FastConfirmationPaper.LMDGhost.Proof.RuleSafety

@[expose] public section

/-!
# HFC / Proof / Recency — shared helpers for the §4 recency descendant argument

Proves source-epoch recency bounds for votes that justify an HFC checkpoint.

This module contains `ancestor_boundaryBlock`, `le_lslot_epochOf`, `honest_voter_of_link` and related declarations.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-! ### Step 5 helper — `boundaryBlock` monotonicity -/

/-- **`boundaryBlock` monotonicity.** If `b` is an ancestor of a well-formed `x` and
    `b.slot ≤ bound`, then `b` is an ancestor of `x`'s `bound`-boundary block (the
    highest ancestor of `x` of slot `≤ bound`). Structural recursion on `x`: at each
    `mk` node, either the node's slot is `≤ bound` (the boundary is the node itself,
    and `b ≼ x` directly) or we descend to the parent — where `b` still sits, because
    `b.slot ≤ bound < x.slot` forces `b ≠ x`, so `b` is an ancestor of the parent. -/
theorem ancestor_boundaryBlock {b x : Block n} (bound : Slot)
    (hbx : b ≼ x) (hwf : x.WellFormed) (hslot : b.slot ≤ bound) :
    b ≼ boundaryBlock bound x := by
  induction x with
  | genesis =>
    -- x = genesis ⇒ b = genesis ⇒ b ≼ genesis = boundaryBlock bound genesis.
    cases hbx
    exact Block.Ancestor.refl _
  | mk bid p s ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact hbx
    · rw [if_neg hsb]
      -- s > bound ≥ b.slot, so b ≠ mk bid p s; hence b ≼ p.
      have hbp : b ≼ p := by
        rcases ancestor_mk_cases hbx with heq | hap
        · -- b = mk bid p s would give b.slot = s > bound ≥ b.slot, contradiction.
          exfalso
          rw [heq] at hslot
          simp only [Block.slot] at hslot
          exact hsb (le_trans (le_refl s) hslot)
        · exact hap
      exact ih hbp hwf.2
  | mkWithVotes bid p s votes ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact hbx
    · rw [if_neg hsb]
      -- s > bound ≥ b.slot, so b ≠ mkWithVotes bid p s votes; hence b ≼ p.
      have hbp : b ≼ p := by
        rcases ancestor_mkWithVotes_cases hbx with heq | hap
        · -- b = mkWithVotes bid p s votes would give b.slot = s > bound ≥ b.slot.
          exfalso
          rw [heq] at hslot
          simp only [Block.slot] at hslot
          exact hsb (le_trans (le_refl s) hslot)
        · exact hap
      exact ih hbp hwf.2

/-! ### Step 5 helper — epoch-boundary slot arithmetic (pure `Nat` division) -/


/-- A slot sits at or below the last slot of its own epoch: `s ≤ lslot (epochOf s)`.
    `s = (s / E)·E + s % E` and `s % E ≤ E − 1`. -/
theorem le_lslot_epochOf (τ : Timing) (s : Slot) : s ≤ τ.lslot (τ.epochOf s) := by
  unfold Timing.lslot Timing.epochOf
  -- `s = (s / E) * E + s % E`, and `s % E ≤ E - 1`.
  have hdm : s / τ.slotsPerEpoch * τ.slotsPerEpoch + s % τ.slotsPerEpoch = s :=
    Nat.div_add_mod' s τ.slotsPerEpoch
  have hmod : s % τ.slotsPerEpoch ≤ τ.slotsPerEpoch - 1 :=
    Nat.le_sub_one_of_lt (Nat.mod_lt s τ.hSlotsPerEpoch)
  calc s = s / τ.slotsPerEpoch * τ.slotsPerEpoch + s % τ.slotsPerEpoch := hdm.symm
    _ ≤ s / τ.slotsPerEpoch * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) := Nat.add_le_add_left hmod _

/-! ### Step 2 helper — an honest voter behind every `≥ 2/3` supermajority link -/

open Classical in
/-- **An honest voter behind every supermajority link.** From a `≥ 2/3` weighted
    supermajority link `Cs → Ct` (`3·linkWeight ≥ 2·totalWeight univ`) and the global
    Byzantine-weight bound (`totalWeight (non-honest over univ) ≤ β·totalWeight univ`,
    the `univ`-instance of Assumption 2), with `β < 1/3` and a nonempty validator set,
    the link's signer set contains an **honest** validator: the honest part of the
    signer weight is `≥ (2/3 − β)·W > (1/3)·W > 0`, hence nonempty.

    This is the FFG mirror of the §3.1 honest-supporter extraction
    (`Quorum.Q_imp_H_majority`): a `≥ 2/3` link cannot be entirely Byzantine when
    `β < 1/3`. Concretely it returns an honest `i` together with an FFG message in `V`
    cast by `i` whose link is exactly `Cs → Ct`. -/
theorem honest_voter_of_link {bal₀ : Stakes n} {fm : FaultModel n} {V : View n (FFGVote n)}
    {Cs Ct : Checkpoint n}
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hsup : 3 * linkWeight bal₀ V Cs Ct ≥ 2 * totalWeight bal₀ Finset.univ) :
    ∃ i ∈ fm.honest, ∃ m ∈ V.msgs,
      m.ghost.validator = i ∧ m.extra.source = Cs ∧ m.extra.target = Ct := by
  classical
  set Sgn : Finset (Validator n) := Finset.univ.filter (fun i =>
    ∃ m ∈ V.msgs, m.ghost.validator = i ∧ m.extra.source = Cs ∧ m.extra.target = Ct) with hSgn
  -- `linkWeight = totalWeight Sgn` (definitional).
  have hlink : linkWeight bal₀ V Cs Ct = totalWeight bal₀ Sgn := rfl
  set Wtot : Weight := totalWeight bal₀ (Finset.univ : Finset (Validator n)) with hWtot
  have hWpos : 0 < Wtot := totalWeight_pos bal₀ hwit
  -- Split the signer weight into honest + non-honest.
  have hsplit : totalWeight bal₀ Sgn
      = totalWeight bal₀ (Sgn.filter (fun i => i ∈ fm.honest))
        + totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest)) := by
    simp only [totalWeight]
    exact (Finset.sum_filter_add_sum_filter_not Sgn (fun i => i ∈ fm.honest) bal₀.bal).symm
  -- Non-honest signer weight ≤ non-honest weight over univ ≤ β·Wtot.
  have hadv : totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest)) ≤ fm.β * Wtot := by
    refine le_trans (totalWeight_mono bal₀ ?_) hByz
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2
  -- β·Wtot < (1/3)·Wtot since β < 1/3 and Wtot > 0.
  have hβbound : fm.β * Wtot < (1 / 3) * Wtot := by
    apply mul_lt_mul_of_pos_right fm.hβ hWpos
  -- Honest signer weight ≥ (2/3 − β)·Wtot > 0.
  have hhon_pos : 0 < totalWeight bal₀ (Sgn.filter (fun i => i ∈ fm.honest)) := by
    have hl : totalWeight bal₀ Sgn = linkWeight bal₀ V Cs Ct := hlink.symm
    -- 3·link ≥ 2·Wtot ⇒ link ≥ (2/3)·Wtot.
    have hlinkge : (2 / 3) * Wtot ≤ linkWeight bal₀ V Cs Ct := by linarith
    have hadv' : totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest)) < (1 / 3) * Wtot :=
      lt_of_le_of_lt hadv hβbound
    -- honest = link − non-honest ≥ (2/3 − 1/3)·Wtot > 0.
    have : totalWeight bal₀ (Sgn.filter (fun i => i ∈ fm.honest))
        = linkWeight bal₀ V Cs Ct - totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest)) := by
      rw [hl] at hsplit; linarith
    rw [this]; linarith
  -- Positive weight ⇒ the honest signer set is nonempty ⇒ extract the honest voter.
  have hne : (Sgn.filter (fun i => i ∈ fm.honest)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hhon_pos
    simp [totalWeight] at hhon_pos
  obtain ⟨i, hi⟩ := hne
  simp only [Finset.mem_filter, hSgn] at hi
  obtain ⟨⟨_, hsig⟩, hhon⟩ := hi
  obtain ⟨m, hm, hmv, hms, hmt⟩ := hsig
  exact ⟨i, hhon, m, hm, hmv, hms, hmt⟩

end FastConfirmation.HFC

end
