module
public import FastConfirmation.Paper.HFC.Proof.Recency
public import FastConfirmation.Paper.HFC.Proof.Justification

@[expose] public section

/-!
# HFC / Proof / CrossEpoch — the cross-epoch joint induction (§4)

This module makes the paper's **cross-epoch induction** (arXiv:2405.00549 §4) explicit as a
§4-layer ladder *on top of* the §3.1 head-safety engine
(`FastConfirmation/Paper/LMDGhost/`, reused per epoch,
without changing the §3.1 argument). For a block `B` confirmed (safe) in epoch `E`:

  (1) `B` is never FFG-filtered throughout `E+1` — the FFG never-filter for the whole next epoch;
  (2) not-filtered throughout `E+1` ⇒ `B` canonical throughout `E+1` — the §3.1 LMD-GHOST-HFC
      engine at the filtered fork choice;
  (3) `B canonical throughout E+1` is the **base case** of an induction on epochs `e ≥ E+1`:
      IH `CanonicalThroughoutEpoch B e` (B on the filtered head for EVERY honest view at EVERY
      slot boundary of epoch `e`). STEP `e → e+1`: every honest epoch-`e` FFG voter has `B` on
      its head ⇒ (by `HonestFFGNoEquivocation`) its target is `checkpointOf(head, ·)`, which is
      on `chain(B)` (`boundaryBlock` monotonicity) ⇒ the realized GJ at any time in `e+1`
      (epoch `≤ e`, when justified by epoch-`e` voters) is on `chain(B)` ⇒ `B` not filtered
      throughout `e+1` ⇒ (engine, step 2) `B` canonical throughout `e+1`.

The IH `CanonicalThroughoutEpoch B e` is what covers the **early-epoch voters** the engine's
from-safe-time (`st(slotOf t)`) window `[s, k)` misses for the realized GJ of epoch exactly `e`:
it is DERIVED inductively (not assumed), so non-circular. This is the §4-layer per-step hook;
the engine's `NeverFilteredFromHead` / `hNFilOfHead` functional form is the per-epoch rung.

## Results in this module

* `CanonicalThroughoutEpoch` — the §4-layer predicate (B on the filtered head at every honest
  slot-boundary view of epoch `e`).
* `realizedGJ_descends_of_canonicalEpoch` — the STEP's analytic core: a realized GJ of epoch
  exactly `e`, justified by an honest epoch-`e` voter, descends from `B` given
  `CanonicalThroughoutEpoch B e`. It realizes the §4 RECENCY descendant argument with the window
  taken to be the *whole epoch* `e` (`[fslot e, lslot e]`), supplied by the IH — **no slot
  bound, no gate**. It is the per-rung descendant placement the ladder consumes.

`confirmedNotFFGFiltered_proved` in `NeverFiltered.lean` composes these rungs and eliminates the
slot-bound premise.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-! ### `boundaryBlock` structural facts (ancestor + slot bound + ancestor placement) -/

/-- The boundary block is an ancestor of `x` (it walks up `chain(x)` to slot `≤ bound`). -/
theorem boundaryBlock_ancestor (bound : Slot) (x : Block n) : boundaryBlock bound x ≼ x := by
  induction x with
  | genesis => exact Block.Ancestor.refl _
  | mk bid p s ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact Block.Ancestor.refl _
    · rw [if_neg hsb]; exact Block.Ancestor.step ih
  | mkWithVotes bid p s votes ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact Block.Ancestor.refl _
    · rw [if_neg hsb]; exact Block.Ancestor.stepWithVotes ih

/-- The boundary block's slot is `≤ bound` (for a well-formed `x`). Genesis has slot `0 ≤ bound`;
    at a `mk` node either the node's slot is `≤ bound` (taken as the boundary) or we recurse into
    the well-formed parent. -/
theorem boundaryBlock_slot_le (bound : Slot) {x : Block n} (hwf : x.WellFormed) :
    (boundaryBlock bound x).slot ≤ bound ∨ boundaryBlock bound x = Block.genesis := by
  induction x with
  | genesis => exact Or.inr rfl
  | mk bid p s ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact Or.inl hsb
    · rw [if_neg hsb]; exact ih hwf.2
  | mkWithVotes bid p s votes ih =>
    unfold boundaryBlock
    by_cases hsb : s ≤ bound
    · rw [if_pos hsb]; exact Or.inl hsb
    · rw [if_neg hsb]; exact ih hwf.2

/-- **Ancestor placement of the boundary block.** If `B ≼ x` (well-formed `x`) and
    `bound < B.slot`, then `boundaryBlock bound x ≼ B`. Both `boundaryBlock bound x` and `B` are
    ancestors of `x`, hence comparable (`ancestor_comparable`); the boundary's slot is
    `≤ bound < B.slot`, so the boundary is the (strictly-)lower one, i.e. an ancestor of `B`.
    This is the **ancestor** counterpart of `ancestor_boundaryBlock`: it places a *low* boundary
    (epoch strictly below `B`'s epoch) *below* `B` on the same chain — exactly what pins a realized
    GJ of epoch `< epochOf B.slot`, justified by epoch-`e'` voters with `B` on their head, as an
    ancestor of `B` (`block(GJ) ≼ B`). -/
theorem boundaryBlock_le_of_lt_slot {B x : Block n} (bound : Slot)
    (hBx : B ≼ x) (hwf : x.WellFormed) (hlt : bound < B.slot) :
    boundaryBlock bound x ≼ B := by
  have hbx : boundaryBlock bound x ≼ x := boundaryBlock_ancestor bound x
  have hBwf : B.WellFormed := WellFormed_of_ancestor hBx hwf
  rcases ancestor_comparable hbx hBx with hle | hge
  · exact hle
  · -- `B ≼ boundaryBlock bound x` would give `B.slot ≤ (boundary).slot ≤ bound < B.slot`.
    exfalso
    have hslot_le : (boundaryBlock bound x).slot ≤ bound := by
      rcases boundaryBlock_slot_le bound hwf with h | h
      · exact h
      · rw [h]; exact Nat.zero_le _
    have hBle : B.slot ≤ (boundaryBlock bound x).slot :=
      slot_le_of_ancestor hge (WellFormed_of_ancestor hbx hwf)
    exact absurd (le_trans hBle hslot_le) (not_le.mpr hlt)

/-- **Prefix agreement on the epoch-onset checkpoint** (the payoff of the `fslot e` checkpoint
    convention). If `b ≼ h`, both well-formed, and the boundary `bound ≤ b.slot`, then `b` and its
    descendant `h` have the **same** boundary block:
    `boundaryBlock bound h = boundaryBlock bound b`.
    With `bound := τ.fslot e` and `τ.fslot e ≤ b.slot` (i.e. `epoch(b) ≥ e`), this says every honest
    head `h ⪰ b` computes the SAME `checkpointOf b e` — the §4.1 certificate target — from prefix
    agreement `b ⪯ h` alone, **no head convergence**. This is exactly the common-target invariant
    the
    certificate-formation keystone (`checkpoint_justified_of_canonical`'s `htgt`) consumes. -/
theorem boundaryBlock_eq_of_ancestor {b h : Block n} (bound : Slot)
    (hbh : b ≼ h) (hbwf : b.WellFormed) (hhwf : h.WellFormed) (hle : bound ≤ b.slot) :
    boundaryBlock bound h = boundaryBlock bound b := by
  have hHanc : boundaryBlock bound h ≼ h := boundaryBlock_ancestor bound h
  have hBanc : boundaryBlock bound b ≼ b := boundaryBlock_ancestor bound b
  have hHwf : (boundaryBlock bound h).WellFormed := WellFormed_of_ancestor hHanc hhwf
  have hBwf : (boundaryBlock bound b).WellFormed := WellFormed_of_ancestor hBanc hbwf
  have hHslot : (boundaryBlock bound h).slot ≤ bound := by
    rcases boundaryBlock_slot_le bound hhwf with hs | hgen
    · exact hs
    · rw [hgen]; exact Nat.zero_le _
  have hBslot : (boundaryBlock bound b).slot ≤ bound := by
    rcases boundaryBlock_slot_le bound hbwf with hs | hgen
    · exact hs
    · rw [hgen]; exact Nat.zero_le _
  -- `boundaryBlock bound h ≼ b` (it is an ancestor of `h` of slot `≤ bound ≤ b.slot`).
  have hHb : boundaryBlock bound h ≼ b := by
    rcases ancestor_comparable hHanc hbh with h1 | h2
    · exact h1
    · have hble : b.slot ≤ (boundaryBlock bound h).slot := slot_le_of_ancestor h2 hHwf
      have heqs : b.slot = (boundaryBlock bound h).slot :=
        le_antisymm hble (le_trans hHslot hle)
      have heq : b = boundaryBlock bound h := eq_of_ancestor_slot h2 hHwf heqs
      rw [heq]
      exact Block.Ancestor.refl _
  -- each boundary block is an ancestor of the other ⇒ equal (well-formed antisymmetry).
  have hHbb : boundaryBlock bound h ≼ boundaryBlock bound b :=
    ancestor_boundaryBlock bound hHb hbwf hHslot
  have hBbh : boundaryBlock bound b ≼ boundaryBlock bound h :=
    ancestor_boundaryBlock bound (Block.Ancestor.trans hBanc hbh) hhwf hBslot
  exact eq_of_ancestor_slot hHbb hBwf
    (le_antisymm (slot_le_of_ancestor hHbb hBwf) (slot_le_of_ancestor hBbh hHwf))

/-- **§4-layer canonicity-throughout-an-epoch predicate.** `B` is on every honest validator's
    filtered (`ffgFilter`) LMD-GHOST-HFC fork-choice head, computed at *every* slot boundary
    `st j` whose slot `j` lies in epoch `e` (`epochOf j = e`). This is the rung of the
    cross-epoch ladder: the base rung (`e = E+1`) comes from the confirmation via the engine,
    each subsequent rung from the STEP. Crucially it covers the **whole** epoch `e` — including
    early-epoch slots `j < s` the engine's from-safe-time window cannot reach — and is DERIVED
    inductively, never assumed. -/
def CanonicalThroughoutEpoch (τ : Timing) (fm : FaultModel n)
    (boost : ProposerBoost n (FFGVote n)) (pb : Weight) (bal₀ : Stakes n)
    (𝒱 : ViewFamily n (FFGVote n)) (B : Block n) (e : Epoch) : Prop :=
  ∀ ⦃j : Slot⦄, τ.epochOf j = e → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
    B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
      (τ.st j)

/-- **STEP analytic core — the realized GJ of epoch `e` is the epoch-`e` boundary of an honest
    head `⪰ B`.** If `B` is canonical throughout epoch `e` (`hcanon`), then any checkpoint `Cpt`
    that is `Justified` in an honest view at `t'` and whose epoch is exactly `e` is the epoch-`e`
    boundary block of some honest fork-choice head `head` with `B ≼ head` (well-formed):
    `Cpt.block = boundaryBlock (lslot e) head` and `B ≼ head`. This is the shared kernel of the
    descendant (`epoch e ≥ epochOf B.slot`) and ancestor (`epoch e < epochOf B.slot`) placements —
    the head-safety window is the *whole epoch* `e`, supplied by `CanonicalThroughoutEpoch B e`,
    NOT by the engine's `[s, k)` window, so it needs **no GU-root slot bound and no gate**.

    **Proof.** `Cpt` is `Justified` ⇒ a `≥ 2/3` link; `β < 1/3` extracts an honest signer `i` with
    an FFG message `m ∈ (𝒱 w t').msgs` of that link (`honest_voter_of_link`). `HonestNoForgery` +
    `HonestFFGNoEquivocation` pin `Cpt = checkpointOf headᵢ (epochOf m.ghost.slot)` and
    `Cpt.epoch = epochOf m.ghost.slot = e`, so `m.ghost.slot` lies in epoch `e` and
    `CanonicalThroughoutEpoch B e` gives `B ≼ headᵢ` directly — even for the early-epoch voters
    (`m.ghost.slot < s`) the engine misses. ∎ -/
theorem realizedGJ_boundary_of_canonicalEpoch
    {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n} {cm : Committees n}
    {boost : ProposerBoost n (FFGVote n)} {pb : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    {w : Validator n} {t' : Time} {B : Block n} {Cpt : Checkpoint n} {e : Epoch}
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hnoforge : HonestNoForgery fm τ 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hw : w ∈ fm.honest)
    (hcanon : CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B e)
    (hCptpos : 1 ≤ e)
    (hCptep : Cpt.epoch = e)
    (hJust : Justified bal₀ (𝒱 w t') Cpt) :
    ∃ head : Block n, head.WellFormed ∧ B ≼ head ∧ Cpt.block = boundaryBlock (τ.fslot e) head := by
  classical
  cases hJust with
  | base =>
    -- `Cpt = genesisCheckpoint`, epoch `0`. `hCptep` forces `e = 0`, contradicting `1 ≤ e`.
    have he0 : (0 : ℕ) = e := by
      have := hCptep; simp only [genesisCheckpoint] at this; exact this
    rw [← he0] at hCptpos
    exact absurd hCptpos (Nat.not_succ_le_zero 0)
  | link hsCs hsup =>
    obtain ⟨i, hhon, m, hm, hmv, _hms, hmt⟩ :=
      honest_voter_of_link (bal₀ := bal₀) (fm := fm) (V := 𝒱 w t') hwit hByz hsup
    have hival : m.ghost.validator ∈ fm.honest := by rw [hmv]; exact hhon
    have hcast : HonestCast fm 𝒱 τ m := hnoforge hw hm hival
    obtain ⟨htgt, _hsrc⟩ := hnoequiv hcast
    have hCpt : Cpt = checkpointOf τ
        (forkChoiceHead τ (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot)) boost pb
          (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot))
        (τ.epochOf m.ghost.slot) := by rw [← hmt, htgt]
    have hCptepoch : Cpt.epoch = τ.epochOf m.ghost.slot := by rw [hCpt]; rfl
    have hvslot_ep : τ.epochOf m.ghost.slot = e := by rw [← hCptepoch, hCptep]
    refine ⟨forkChoiceHead τ (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot)) boost pb
      (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot), ?_, ?_, ?_⟩
    · exact forkChoiceHead_WellFormed (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot))
        (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot)
    · exact hcanon hvslot_ep hival
    · rw [hCpt]; simp only [checkpointOf, hvslot_ep]

/-- **STEP placement (descendant) — `epoch e ≥ epochOf B.slot`.** The realized GJ of epoch `e`,
    justified in an honest view with `B` canonical throughout epoch `e`, *descends from* `B`
    (`B ≼ Cpt.block`) when `epochOf B.slot ≤ e`. `B ≼ head` and `B.slot ≤ lslot e` give
    `B ≼ boundaryBlock (lslot e) head = Cpt.block` (`ancestor_boundaryBlock`). No slot bound. -/
theorem realizedGJ_descends_of_canonicalEpoch
    {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n} {cm : Committees n}
    {boost : ProposerBoost n (FFGVote n)} {pb : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    {w : Validator n} {t' : Time} {B : Block n} {Cpt : Checkpoint n} {e : Epoch}
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hnoforge : HonestNoForgery fm τ 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hw : w ∈ fm.honest)
    (hcanon : CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B e)
    (hCptpos : 1 ≤ e)
    (hCptep : Cpt.epoch = e)
    (hep : τ.epochOf B.slot < e)
    (hJust : Justified bal₀ (𝒱 w t') Cpt) :
    B ≼ Cpt.block := by
  obtain ⟨head, hwfhead, hBhead, hCptblock⟩ :=
    realizedGJ_boundary_of_canonicalEpoch hwit hByz hnoforge hnoequiv hw hcanon hCptpos hCptep
      hJust
  -- `epoch(B) < e ⇒ B.slot < e·E = fslot e`, so `B` lies at/before the epoch-`e` onset boundary.
  have hbslot : B.slot ≤ τ.fslot e :=
    Nat.le_of_lt ((Nat.div_lt_iff_lt_mul τ.hSlotsPerEpoch).mp hep)
  rw [hCptblock]
  exact ancestor_boundaryBlock _ hBhead hwfhead hbslot

/-- **STEP placement (ancestor) — `epoch e < epochOf B.slot`.** The realized GJ of epoch `e`,
    justified in an honest view with `B` canonical throughout epoch `e`, is an *ancestor of* `B`
    (`Cpt.block ≼ B`) when `e < epochOf B.slot`. Then `lslot e < fslot(epochOf B.slot) ≤ B.slot`,
    so the epoch-`e` boundary of the honest head (`B ≼ head`) sits *below* `B` on `chain(head)`,
    i.e. `boundaryBlock (lslot e) head ≼ B` (`boundaryBlock_le_of_lt_slot`). This is the ancestor
    counterpart that lets the cross-epoch ladder pin a realized GJ of epoch strictly below `B`'s
    epoch as an ancestor — replacing the GU-root slot bound for that sub-band. No slot bound. -/
theorem realizedGJ_ancestor_of_canonicalEpoch
    {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n} {cm : Committees n}
    {boost : ProposerBoost n (FFGVote n)} {pb : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    {w : Validator n} {t' : Time} {B : Block n} {Cpt : Checkpoint n} {e : Epoch}
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hnoforge : HonestNoForgery fm τ 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hw : w ∈ fm.honest)
    (hcanon : CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B e)
    (hCptpos : 1 ≤ e)
    (hCptep : Cpt.epoch = e)
    (hep : e < τ.epochOf B.slot)
    (hJust : Justified bal₀ (𝒱 w t') Cpt) :
    Cpt.block ≼ B := by
  obtain ⟨head, hwfhead, hBhead, hCptblock⟩ :=
    realizedGJ_boundary_of_canonicalEpoch hwit hByz hnoforge hnoequiv hw hcanon hCptpos hCptep
      hJust
  -- `lslot e < B.slot`: `lslot e < fslot (e+1) = (e+1)·E ≤ (epochOf B.slot)·E = fslot(epochOf
  -- B.slot) ≤ B.slot`.  Use `lslot e < fslot (epochOf B.slot)` and
  -- `fslot (epochOf B.slot) ≤ B.slot`.
  have hlt : τ.fslot e < B.slot := by
    have hstep : τ.fslot e < τ.fslot (e + 1) := by
      unfold Timing.fslot
      calc e * τ.slotsPerEpoch
          < e * τ.slotsPerEpoch + τ.slotsPerEpoch := lt_add_of_pos_right _ τ.hSlotsPerEpoch
        _ = (e + 1) * τ.slotsPerEpoch := by ring
    have hfle : τ.fslot (e + 1) ≤ τ.fslot (τ.epochOf B.slot) := by
      unfold Timing.fslot
      exact Nat.mul_le_mul_right τ.slotsPerEpoch hep
    have hfB : τ.fslot (τ.epochOf B.slot) ≤ B.slot := by
      unfold Timing.fslot Timing.epochOf
      exact Nat.div_mul_le_self B.slot τ.slotsPerEpoch
    exact lt_of_lt_of_le (lt_of_lt_of_le hstep hfle) hfB
  rw [hCptblock]
  exact boundaryBlock_le_of_lt_slot _ hBhead hwfhead hlt

/-! ### The ladder rung: head-safety-from-`st s` ⇒ `CanonicalThroughoutEpoch` for later epochs -/

/-- **Ladder rung (engine output ⇒ canonical throughout a later epoch).** Given head safety for
    `B` from the safe time `st s` (the §3.1 engine's output, after the never-filter is discharged)
    and an epoch `e` strictly above `B`'s safe-time epoch `epochOf s` (`epochOf s < e`), `B` is
    canonical throughout the *whole* epoch `e` — every slot `j` of epoch `e` has `fslot e ≤ j`, and
    `fslot e = e·E > (epochOf s)·E + (E−1) = lslot(epochOf s) ≥ s` (since `e ≥ epochOf s + 1`), so
    `st j ≥ st s`, where the engine gives `B ≼ head`. This makes steps (2) and (3) of the
    paper's induction explicit: *not-filtered-from-`st s` ⇒ B canonical throughout every epoch
    `> epochOf s`* — the engine's strong slot-induction IS the cross-epoch ladder, with each epoch
    `> epochOf s` a rung reached from the single never-filter at `st s`. (Epochs `≤ epochOf s` are
    NOT reachable: the engine bottoms out at the safe time `st s`, so early-epoch / pre-`s` slots
    have no head-safety. The realized GJ of an epoch `≤ epochOf s` is the ANCESTOR case of the
    never-filter, closed *not* by this ladder but by the both-directions case-split on the gate's
    compatibility `block(GJ_real) ~ B` — see `confirmedNotFFGFiltered_proved`; no slot bound.) -/
theorem canonicalEpoch_of_headSafety
    {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n}
    {boost : ProposerBoost n (FFGVote n)} {pb : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    {B : Block n} {s : Slot} {e : Epoch}
    (hsafe : ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t')
    (he : τ.epochOf s < e) :
    CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B e := by
  intro j hj i hi
  -- `s ≤ fslot e ≤ j`, hence `st s ≤ st j`; apply `hsafe` at `t' = st j`.
  have hsj : s ≤ j := by
    -- `s ≤ lslot(epochOf s) < fslot(epochOf s + 1) ≤ fslot e ≤ j`.
    have h1 : s ≤ τ.lslot (τ.epochOf s) := le_lslot_epochOf τ s
    have h2 : τ.lslot (τ.epochOf s) < τ.fslot (τ.epochOf s + 1) := by
      unfold Timing.lslot Timing.fslot
      have hE1 : τ.slotsPerEpoch - 1 < τ.slotsPerEpoch := Nat.sub_lt τ.hSlotsPerEpoch Nat.one_pos
      calc τ.epochOf s * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1)
              < τ.epochOf s * τ.slotsPerEpoch + τ.slotsPerEpoch :=
            Nat.add_lt_add_left hE1 _
        _ = (τ.epochOf s + 1) * τ.slotsPerEpoch := by ring
    have h3 : τ.fslot (τ.epochOf s + 1) ≤ τ.fslot e := by
      unfold Timing.fslot; exact Nat.mul_le_mul_right τ.slotsPerEpoch he
    have h4 : τ.fslot e ≤ j := by
      -- `fslot e = e·E ≤ j` since `epochOf j = e ⇒ e·E ≤ j` (`e·E ≤ (j/E)·E ≤ j`).
      unfold Timing.fslot
      rw [← hj]; unfold Timing.epochOf; exact Nat.div_mul_le_self j τ.slotsPerEpoch
    exact le_trans (le_trans h1 (le_of_lt (lt_of_lt_of_le h2 h3))) h4
  have hstle : τ.st s ≤ τ.st j := by
    unfold Timing.st; exact Nat.mul_le_mul_right τ.slotDur hsj
  exact hsafe hi hstle

/-- **Windowed ladder rung (the never-filter's internal hook).** The same conclusion as
    `canonicalEpoch_of_headSafety`, but fed by the engine's *windowed* head-safety
    `hHead : ∀ j ∈ [s, k), B ≼ head`, exactly as `NeverFilteredFromHead`'s functional antecedent
    supplies it. It yields `CanonicalThroughoutEpoch B e` whenever the *whole* epoch `e` sits
    inside the window: `s ≤ fslot e` (`he_lo`) and `lslot e < k` (`he_hi`). This is the rung the
    cross-epoch ladder uses *inside* `confirmedNotFFGFiltered_proved` (non-circular: it consumes
    only head-safety at the *earlier* slots `j < k` the engine's strong induction already grants).

    It reaches epochs `e ≥ epochOf s + 1` (`s ≤ fslot e ⟺ epochOf s < e`, since `fslot e ≥ s`
    needs `e·E ≥ s` and `s ≤ lslot(epochOf s) < fslot(epochOf s + 1)`); epochs `≤ epochOf s` are
    NOT reachable (their early slots fall below the window's lower bound `s`). That ancestor band is
    closed by the never-filter's both-directions case-split on the gate's compatibility, not by this
    ladder — no slot bound. -/
theorem canonicalEpoch_of_headWindow
    {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n}
    {boost : ProposerBoost n (FFGVote n)} {pb : Weight} {𝒱 : ViewFamily n (FFGVote n)}
    {B : Block n} {s k : Slot} {e : Epoch}
    (hHead : ∀ ⦃j : Slot⦄, s ≤ j → j < k → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
        (τ.st j))
    (he_lo : s ≤ τ.fslot e) (he_hi : τ.lslot e < k) :
    CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B e := by
  intro j hj i hi
  -- `fslot e ≤ j ≤ lslot e`, so `s ≤ fslot e ≤ j` and `j ≤ lslot e < k`.
  have hjlo : τ.fslot e ≤ j := by
    unfold Timing.fslot; rw [← hj]; unfold Timing.epochOf
    exact Nat.div_mul_le_self j τ.slotsPerEpoch
  have hjhi : j ≤ τ.lslot e := by rw [← hj]; exact le_lslot_epochOf τ j
  exact hHead (le_trans he_lo hjlo) (lt_of_le_of_lt hjhi he_hi) hi

end FastConfirmation.HFC

end
