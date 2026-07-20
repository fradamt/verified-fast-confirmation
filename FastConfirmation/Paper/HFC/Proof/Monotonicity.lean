import FastConfirmation.Paper.HFC.Proof.CanonicalReuse
import FastConfirmation.Paper.HFC.Proof.NeverFiltered
import FastConfirmation.Paper.HFC.Proof.Compose

/-!
# HFC / Proof / Monotonicity

`HFC_Monotonicity` — once HFC-confirmed, always HFC-confirmed. The HFC predicate is
`isConfirmed ∧ WillNoConflictingChkpBeJustified`, so monotonicity splits into:

* the **`isConfirmed`-half** — `b ≼ highestConfirmedSinceEpoch … t → b ≼ … t'` — a
  re-run of `proof_Theorem1_Monotonicity` (Rule.lean) at `flt := ffgFilter bal₀ τ`,
  `gj := gjFFG bal₀`, `C := bal₀`, using the `flt`-generic canonical lemmas
  (`CanonicalReuse.lean`) and feeding `NeverFiltered` from `confirmedNotFFGFiltered_proved`;
* the **gate-half** — `WillNoConflictingChkpBeJustified … t → … t'` — free, by
  quantifier-domain weakening (`willNoConflicting_persists`, III.5), since the semantic
  gate is already `∀ t'' ≥ st(slotOf t)`-quantified.

Lemmas:

* `willNoConflicting_persists` — gate persistence.
* `hfc_monotonicity_proved` — the assembly.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **III.5 — gate persistence (the gate-half of monotonicity).** The semantic gate
    `WillNoConflictingChkpBeJustified … b t` is already `∀ w∈honest, ∀ t'' ≥ st(slotOf t)`.
    For `t ≤ t'`: `slotOf t ≤ slotOf t'` (`Nat.div_le_div_right`), so
    `st(slotOf t) ≤ st(slotOf t')` (`Nat.mul_le_mul_right`); any `t'' ≥ st(slotOf t')` is
    then `≥ st(slotOf t)`, so the gate at `t` applies at `t'`. Assumption 3 is not needed
    for the semantic form. -/
theorem willNoConflicting_persists {τ : Timing} {fm : FaultModel n} {bal₀ : Stakes n}
    {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t t' : Time} (hle : t ≤ t')
    (hgate : WillNoConflictingChkpBeJustified bal₀ fm τ 𝒱 b t) :
    WillNoConflictingChkpBeJustified bal₀ fm τ 𝒱 b t' := by
  intro w hw t'' ht'' Cc hJ hep
  -- `st(slotOf t) ≤ st(slotOf t') ≤ t''`, so the gate at `t` fires.
  have hslot : τ.slotOf t ≤ τ.slotOf t' := Nat.div_le_div_right hle
  have hst : τ.st (τ.slotOf t) ≤ τ.st (τ.slotOf t') :=
    by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hslot
  exact hgate hw (le_trans hst ht'') hJ hep

/-- **III.6 — `HFC_Monotonicity` proved.** Re-run of `proof_Theorem1_Monotonicity` (Rule.lean)
    at `gj := gjFFG bal₀`, `flt := ffgFilter bal₀ τ`, `C := bal₀`. The `isConfirmed`-half is
    structurally identical to §3.1, with `safe_canonical_from_engine`→`hfc_canonical_from_engine`,
    `canonical_epoch_imp_safe`→`canonical_epoch_imp_safe_flt`,
    `canonical_ancestor_of_slot_le`→`canonical_ancestor_of_slot_le_flt`, and the `NeverFiltered`
    obligation at each engine/canonical step discharged by `confirmedNotFFGFiltered_proved`
    instantiated at the safe block itself (fed its gate/anchor soundness inputs from
    `SafeNeverFilteredInputs`). The gate-half is `willNoConflicting_persists` (III.5). -/
theorem hfc_monotonicity_proved {τ : Timing} (bal₀ : Stakes n) : HFC_Monotonicity τ bal₀ := by
  intro fm cm pb boost 𝒱 gj C hSync hNF hHB hVV hcm hWFB hpb hsb hβ4 hAS hnoequiv hByz hSGJ
    v b t t' hv hsg hle hcover hHFCconf
  classical
  obtain ⟨hconf, hgate⟩ := hHFCconf
  -- The gate-half persists immediately (III.5).
  refine ⟨?_, willNoConflicting_persists hle hgate⟩
  -- The `isConfirmed`-half: transcribe `proof_Theorem1_Monotonicity` at `ffgFilter`.
  change isConfirmed τ fm cm pb (gjFFG bal₀) 𝒱 v b t'
  set et := τ.epochOf (τ.slotOf t) - 1 with het
  set et' := τ.epochOf (τ.slotOf t') - 1 with het'
  set B := highestConfirmedSinceEpoch τ fm cm pb (gjFFG bal₀) 𝒱 v et t with hBdef
  have hbB : b ≼ B := hconf
  set B'' := highestConfirmedSinceEpoch τ fm cm pb (gjFFG bal₀) 𝒱 v et' t' with hB''def
  change b ≼ B''
  -- `slot t ≤ slot t'` and `et ≤ et'`.
  have hslotle : τ.slotOf t ≤ τ.slotOf t' := Nat.div_le_div_right hle
  have hetle : et ≤ et' := by
    rw [het, het']
    exact Nat.sub_le_sub_right (Nat.div_le_div_right hslotle) 1
  -- unpack `B`: genesis, or safe at `st s`, `s ∈ [fslot et + 1, slot t]`.
  rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gjFFG bal₀)
      (𝒱 := 𝒱) v et t with hgen | ⟨s, hs, hBblk, hBsafe⟩
  · rw [← hBdef] at hgen
    have : b = Block.genesis := by
      have := hbB; rw [hgen] at this; cases this with | refl => rfl
    rw [this]; exact genesis_ancestor _
  rw [← hBdef] at hBblk hBsafe
  rw [Finset.mem_Icc] at hs
  by_cases hBne : B = Block.genesis
  · have : b = Block.genesis := by
      have := hbB; rw [hBne] at this; cases this with | refl => rfl
    rw [this]; exact genesis_ancestor _
  -- `1 ≤ s`, `AfterGST (st s)`, `B` WF of slot `≤ s - 1`.
  have hs1 : 1 ≤ s := le_trans (Nat.le_add_left 1 _) hs.1
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  -- Base `AfterGST(st(s-1))` (engine + never-filter safe-block GST) and weaker `AfterGST(st s)`
  -- (cross-epoch `canonical_epoch_imp_safe_flt`). `fslot et + 1 ≤ s` gives `fslot et ≤ s-1`.
  have hgstSb : τ.AfterGST (τ.st (s - 1)) := by
    have hsg2 : τ.AfterGST (τ.st (τ.fslot et)) := hsg.2
    have hfle : τ.fslot et ≤ s - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs.1)
    exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle)
  have hgstS : τ.AfterGST (τ.st s) :=
    le_trans hgstSb (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le s 1))
  have hcmC : CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 v (τ.st s)) := hcm (w := v) (t := τ.st s)
  obtain ⟨hBwf, hBslot0⟩ := safe_block_wf_slot (C := gjFFG bal₀ 𝒱 v (τ.st s)) (hVV _ _) hcmC hpb
    hBsafe hBne
  rw [hslots] at hBslot0
  have hBslot : B.slot ≤ s := le_trans hBslot0 (Nat.sub_le _ 1)
  -- `B` is `isLMDGHOSTSafe` at `bal₀` (the `gjFFG` anchor is definitionally `bal₀`).
  have hBsafeC : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) B (τ.st s) := hBsafe
  -- never-filter `B` from `confirmedNotFFGFiltered_proved` at `b := B`, `B ≼ B` (refl).
  -- gate / epoch-cover / GU-anchor inputs for `B` come from `SafeGreatestJustifiedAnchorInputs`;
  -- the §4 RECENCY disjunct is now *proven* structurally inside the never-filter
  -- (no recency premise).
  obtain ⟨hgateB, _hAUB, hAnchorB⟩ := hSGJ (w := v) hv (t' := τ.st s) (X := B) hBsafeC
  have hNFB : NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 B (τ.st s) :=
    confirmedNotFFGFiltered_proved bal₀ hSync hNF hHB hVV hcm hpb hv (b := B)
      hAS hnoequiv hByz hs1 hgstSb (Block.Ancestor.refl B) hBsafeC hgateB hAnchorB
  -- M1: `B` is on every honest ffgFilter head from `st s` on.
  have hBcanon : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t'') boost pb (ffgFilter bal₀ τ) (𝒱 w t'') t'' :=
    hfc_canonical_from_engine bal₀ hSync hNF hHB hVV hcm hpb hv hBwf hBslot hs1 hgstSb hBsafeC hNFB
  -- `st s ≤ t'`.
  have hsslott' : s ≤ τ.slotOf t' := le_trans hs.2 hslotle
  have hst_s_t' : τ.st s ≤ t' :=
    le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hsslott') (Timing.st_slotOf_le τ t')
  -- the common ffgFilter head at `(v, t')`, and its well-formedness.
  set head := forkChoiceHead τ (gjFFG bal₀ 𝒱 v t') boost pb (ffgFilter bal₀ τ) (𝒱 v t') t'
    with hhead
  have hheadWf : head.WellFormed :=
    forkChoiceHead_WellFormed (τ := τ) _ (ffgFilter bal₀ τ) (𝒱 v t') t'
  have hBhead : B ≼ head := hBcanon hv hst_s_t'
  -- `B''` is on the head at `(v, t')` (genesis trivially, else never-filter at `b := B''`).
  have hB''head : B'' ≼ head := by
    rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gjFFG bal₀)
        (𝒱 := 𝒱) v et' t' with hg | ⟨s2, hs2, _hB2blk, hB2safe⟩
    · rw [← hB''def] at hg; rw [hg]; exact genesis_ancestor _
    · rw [← hB''def] at hB2safe
      rw [Finset.mem_Icc] at hs2
      by_cases hB2ne : B'' = Block.genesis
      · rw [hB2ne]; exact genesis_ancestor _
      · have hs21 : 1 ≤ s2 := le_trans (Nat.le_add_left 1 _) hs2.1
        have hgstS2 : τ.AfterGST (τ.st (s2 - 1)) := by
          have hsg2 : τ.AfterGST (τ.st (τ.fslot et')) :=
            le_trans hsg.2 (by
              exact_mod_cast Nat.mul_le_mul_right τ.slotDur
                (Nat.mul_le_mul_right τ.slotsPerEpoch hetle))
          have hfle2 : τ.fslot et' ≤ s2 - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs2.1)
          exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle2)
        have hcmC2 : CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 v (τ.st s2)) :=
          hcm (w := v) (t := τ.st s2)
        obtain ⟨hB2wf, hB2slot0⟩ :=
          safe_block_wf_slot (C := gjFFG bal₀ 𝒱 v (τ.st s2)) (hVV _ _) hcmC2 hpb hB2safe hB2ne
        rw [Timing.slotOf_st] at hB2slot0
        have hB2slot : B''.slot ≤ s2 := le_trans hB2slot0 (Nat.sub_le _ 1)
        have hB2safeC : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s2)) B'' (τ.st s2) := hB2safe
        -- never-filter `B''` at `b := B''`, `B'' ≼ B''` (refl), via the safe-block anchor inputs;
        -- the §4 RECENCY disjunct is now *proven* structurally inside the never-filter
        -- (no premise).
        obtain ⟨hgateB2, _hAUB2, hAnchorB2⟩ :=
          hSGJ (w := v) hv (t' := τ.st s2) (X := B'') hB2safeC
        have hNFB2 : NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 B''
            (τ.st s2) :=
          confirmedNotFFGFiltered_proved bal₀ hSync hNF hHB hVV hcm hpb hv (b := B'')
            hAS hnoequiv hByz hs21 hgstS2 (Block.Ancestor.refl B'') hB2safeC
            hgateB2 hAnchorB2
        have hB2canon := hfc_canonical_from_engine bal₀ hSync hNF hHB hVV hcm hpb hv hB2wf
          hB2slot hs21 hgstS2 hB2safeC hNFB2
        have hs2slott' : s2 ≤ τ.slotOf t' := hs2.2
        have hst_s2_t' : τ.st s2 ≤ t' :=
          le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hs2slott')
            (Timing.st_slotOf_le τ t')
        exact hB2canon hv hst_s2_t'
  -- It remains to show `slot B ≤ slot B''`, then `B ≼ B''` (`canonical_ancestor_of_slot_le_flt`).
  suffices hslot : B.slot ≤ B''.slot from
    Block.Ancestor.trans hbB (canonical_ancestor_of_slot_le_flt hBhead hB''head hheadWf hslot)
  by_cases hcase : s ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t')
  · -- Case 1 (same epoch): `B` is a candidate at `t'` at its own slot `s`.
    exact highestConfirmed_slot_ge_of_mem (e' := et') hcase hBblk hBsafe
  · -- Case 2 (cross epoch): `s ≤ fslot et'`; `canonical_epoch_imp_safe_flt` makes `B` safe
    -- at `st(slot t')`.
    rw [Finset.mem_Icc] at hcase
    push Not at hcase
    have hslefe : s ≤ τ.fslot et' := by
      by_contra hlt
      push Not at hlt
      have := hcase (Nat.succ_le_of_lt hlt)
      exact absurd hsslott' (not_le.mpr this)
    have h1slott' : 1 ≤ τ.slotOf t' := le_trans hs1 hsslott'
    have hslt : s - 1 < s := Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hs1) Nat.one_pos
    have hBlt : B.slot < τ.fslot et' :=
      lt_of_le_of_lt hBslot0 (lt_of_lt_of_le hslt hslefe)
    have hEpos : 1 ≤ τ.slotsPerEpoch := τ.hSlotsPerEpoch
    have hepoch_pos : 1 ≤ τ.epochOf (τ.slotOf t') := by
      rcases Nat.eq_zero_or_pos (τ.epochOf (τ.slotOf t')) with h0 | hpos
      · exfalso
        have het'0 : et' = 0 := by rw [het', h0]
        have hsle0 : s ≤ τ.fslot et' := hslefe
        have hf0 : τ.fslot et' = 0 := by rw [het'0]; simp [Timing.fslot]
        rw [hf0] at hsle0
        exact Nat.not_succ_le_zero 0 (le_trans hs1 hsle0)
      · exact hpos
    have hfse1_le : τ.fslot (et' + 1) ≤ τ.slotOf t' := by
      have hsucc : et' + 1 = τ.epochOf (τ.slotOf t') := by
        rw [het']; exact Nat.succ_pred_eq_of_pos hepoch_pos
      rw [hsucc]
      simp only [Timing.fslot, Timing.epochOf]
      exact Nat.div_mul_le_self (τ.slotOf t') τ.slotsPerEpoch
    have hst_fse1 : τ.st (τ.fslot (et' + 1)) ≤ τ.st (τ.slotOf t') :=
      by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfse1_le
    -- `B` safe at `st(slot t')` (anchor `bal₀`).
    have hBsafe' : isLMDGHOSTSafe τ fm cm pb (gjFFG bal₀ 𝒱 v (τ.st (τ.slotOf t')))
        (𝒱 v (τ.st (τ.slotOf t'))) B (τ.st (τ.slotOf t')) :=
      canonical_epoch_imp_safe_flt hSync hNF hHB hcm hcover hpb
        (lt_of_lt_of_le hβ4 (min_le_right _ _)) hBne hBlt hslefe hgstS
        hBcanon hv (le_trans hst_fse1 (le_refl _))
    -- `B ∈ (𝒱 v (st(slot t'))).blocks` via `chain_in_view`.
    have hgst_slott' : τ.AfterGST (τ.st (τ.slotOf t' - 1)) := by
      refine le_trans hgstSb ?_
      exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le_sub_right hsslott' 1)
    have hcmSlott' : CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 v (τ.st (τ.slotOf t'))) :=
      hcm (w := v) (t := τ.st (τ.slotOf t'))
    have hBmem : B ∈ (𝒱 v (τ.st (τ.slotOf t'))).blocks :=
      chain_in_view (C := gjFFG bal₀ 𝒱 v (τ.st (τ.slotOf t'))) (t := τ.st (τ.slotOf t'))
        (t' := τ.st (τ.slotOf t')) hSync hNF hHB hcmSlott'
        hpb hv (by rw [Timing.slotOf_st]; exact h1slott')
        (by rw [Timing.slotOf_st]; exact hgst_slott') hBne hBsafe'
        hv (by rw [Timing.slotOf_st]) (Block.Ancestor.refl B)
    have hrange : τ.slotOf t' ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t') := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_refl _⟩
      have hstep : τ.fslot et' + 1 ≤ τ.fslot (et' + 1) := by
        change et' * τ.slotsPerEpoch + 1 ≤ (et' + 1) * τ.slotsPerEpoch
        have hexp : (et' + 1) * τ.slotsPerEpoch = et' * τ.slotsPerEpoch + τ.slotsPerEpoch := by ring
        rw [hexp]
        exact Nat.add_le_add_left hEpos (et' * τ.slotsPerEpoch)
      exact le_trans hstep hfse1_le
    have hB''slot := highestConfirmed_slot_ge_of_mem (e' := et') (t' := t') (v := v)
      (s' := τ.slotOf t') hrange hBmem hBsafe'
    rw [← hB''def] at hB''slot
    exact hB''slot

end FastConfirmation.HFC
