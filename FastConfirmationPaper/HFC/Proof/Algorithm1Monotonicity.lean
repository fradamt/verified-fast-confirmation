module
public import FastConfirmationPaper.HFC.Proof.Monotonicity
public import FastConfirmationPaper.HFC.Proof.Algorithm1FilterSafety

@[expose] public section

/-!
# HFC / Proof / MonotonicityAlg1 — monotonicity about Algorithm 1 (both branches)

`hfc_monotonicity_alg1` is the `isConfirmedAlg1` monotonicity proof. Its two
never-filter+engine sites are the HFC Algorithm-1 selectors (`highestConfirmedSinceEpochAlg1`)
at `t` and `t'`; both are driven by Algorithm 1's per-block rule `isConfirmedNoCaching`
(`hfc_canonical_alg1_unified_of_confirmed`, fed by the `SafeConfirmedAlg1Inputs` bundle) instead
of the assumed semantic gate. No gate-half: the Algorithm-1 predicate `isConfirmedNoCaching`
carries no separate gate. The unified canonicity dispatches each selected block to the current- or
previous-epoch fold, so the bundle no longer pins the current epoch.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **§4 HFC monotonicity from Algorithm 1 (both branches).** Once `isConfirmedAlg1` (`b ≼
    highestConfirmedSinceEpochAlg1 … t`), still `isConfirmedAlg1` at `t' ≥ t` — driven by
    Algorithm 1's `isConfirmedNoCaching` (via `SafeConfirmedAlg1Inputs` + the unified canonicity
    dispatcher) at each `highestConfirmedSinceEpochAlg1` block, rather than the assumed gate. -/
theorem hfc_monotonicity_alg1 {τ : Timing} (bal₀ : Stakes n)
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb) (hβ4 : fm.β < min (1 / 6) ((1 - pb) / 4))
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm) (hSCM : SlotCommitteeMinority fm cm bal₀) (hwe0 : 0 ≤ we)
    (hBundle : SafeConfirmedAlg1Inputs τ fm cm pb we boost bal₀ 𝒱)
    {v : Validator n} {b : Block n} {t t' : Time}
    (hv : v ∈ fm.honest) (hsg : sg τ b t) (hle : t ≤ t')
    (hcover : CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1))
    (hconf : isConfirmedAlg1 bal₀ fm cm pb we τ 𝒱 v b t) :
    isConfirmedAlg1 bal₀ fm cm pb we τ 𝒱 v b t' := by
  classical
  set et := τ.epochOf (τ.slotOf t) - 1 with het
  set et' := τ.epochOf (τ.slotOf t') - 1 with het'
  set B := highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v et t with hBdef
  have hbB : b ≼ B := by
    simpa [isConfirmedAlg1, Alg1.isConfirmed, highestConfirmedSinceEpochAlg1, het, hBdef]
      using hconf
  set B'' := highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v et' t' with hB''def
  change b ≼ B''
  have hslotle : τ.slotOf t ≤ τ.slotOf t' := Nat.div_le_div_right hle
  have hetle : et ≤ et' := by
    rw [het, het']
    exact Nat.sub_le_sub_right (Nat.div_le_div_right hslotle) 1
  rcases highestConfirmedAlg1_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (we := we)
      (𝒱 := 𝒱) bal₀ v et t with hgen | ⟨s, hs, hBblk, hBconf⟩
  · rw [← hBdef] at hgen
    have : b = Block.genesis := by
      have := hbB; rw [hgen] at this; cases this with | refl => rfl
    rw [this]; exact genesis_ancestor _
  rw [← hBdef] at hBblk hBconf
  rw [Finset.mem_Icc] at hs
  by_cases hBne : B = Block.genesis
  · have : b = Block.genesis := by
      have := hbB; rw [hBne] at this; cases this with | refl => rfl
    rw [this]; exact genesis_ancestor _
  have hs1 : 1 ≤ s := le_trans (Nat.le_add_left 1 _) hs.1
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have hgstSb : τ.AfterGST (τ.st (s - 1)) := by
    have hsg2 : τ.AfterGST (τ.st (τ.fslot et)) := hsg.2
    have hfle : τ.fslot et ≤ s - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs.1)
    exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle)
  have hgstS : τ.AfterGST (τ.st s) :=
    le_trans hgstSb (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le s 1))
  have hcmC : CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 v (τ.st s)) := hcm (w := v) (t := τ.st s)
  have hBsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) B (τ.st s) :=
    isLMDGHOSTSafe_of_isConfirmedNoCaching bal₀ hBconf
  obtain ⟨hBwf, hBslot0⟩ := safe_block_wf_slot (C := gjFFG bal₀ 𝒱 v (τ.st s)) (hVV _ _) hcmC hpb
    hBsafe hBne
  rw [hslots] at hBslot0
  have hBslot : B.slot ≤ s := le_trans hBslot0 (Nat.sub_le _ 1)
  have hBsafeC : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) B (τ.st s) := hBsafe
  -- M1 (Algorithm 1): `B` canonical from `st s` on, from the bundle's confirmation inputs.
  obtain ⟨_hconfBFromBundle, hdelBAll, hGFB, hpartB, hsrcB⟩ := hBundle hv hBsafeC
  have hBcanon : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t'') boost pb (ffgFilter bal₀ τ) (𝒱 w t'') t'' :=
    hfc_canonical_alg1_unified_of_confirmed bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz hs1
      hgstSb hBwf hBslot hwe0 hBconf hdelBAll hSCM hGFB hpartB hsrcB
  have hsslott' : s ≤ τ.slotOf t' := le_trans hs.2 hslotle
  have hst_s_t' : τ.st s ≤ t' :=
    le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hsslott') (Timing.st_slotOf_le τ t')
  set head := forkChoiceHead τ (gjFFG bal₀ 𝒱 v t') boost pb (ffgFilter bal₀ τ) (𝒱 v t') t'
    with hhead
  have hheadWf : head.WellFormed :=
    forkChoiceHead_WellFormed (τ := τ) _ (ffgFilter bal₀ τ) (𝒱 v t') t'
  have hBhead : B ≼ head := hBcanon hv hst_s_t'
  have hB''head : B'' ≼ head := by
    rcases highestConfirmedAlg1_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (we := we)
        (𝒱 := 𝒱) bal₀ v et' t' with hg | ⟨s2, hs2, _hB2blk, hB2conf⟩
    · rw [← hB''def] at hg; rw [hg]; exact genesis_ancestor _
    · rw [← hB''def] at hB2conf
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
        have hB2safe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s2)) B'' (τ.st s2) :=
          isLMDGHOSTSafe_of_isConfirmedNoCaching bal₀ hB2conf
        obtain ⟨hB2wf, hB2slot0⟩ :=
          safe_block_wf_slot (C := gjFFG bal₀ 𝒱 v (τ.st s2)) (hVV _ _) hcmC2 hpb hB2safe hB2ne
        rw [Timing.slotOf_st] at hB2slot0
        have hB2slot : B''.slot ≤ s2 := le_trans hB2slot0 (Nat.sub_le _ 1)
        have hB2safeC : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s2)) B'' (τ.st s2) := hB2safe
        obtain ⟨hconfB2, hdelB2All, hGFB2, hpartB2, hsrcB2⟩ :=
          hBundle hv hB2safeC
        have hB2canon := hfc_canonical_alg1_unified_of_confirmed bal₀ hSync hNF hHB hVV hcm hpb hv
          hAS hnoequiv hByz hs21 hgstS2 hB2wf hB2slot hwe0 hB2conf hdelB2All hSCM hGFB2 hpartB2
          hsrcB2
        have hs2slott' : s2 ≤ τ.slotOf t' := hs2.2
        have hst_s2_t' : τ.st s2 ≤ t' :=
          le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hs2slott')
            (Timing.st_slotOf_le τ t')
        exact hB2canon hv hst_s2_t'
  suffices hslot : B.slot ≤ B''.slot from
    Block.Ancestor.trans hbB (canonical_ancestor_of_slot_le_flt hBhead hB''head hheadWf hslot)
  by_cases hcase : s ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t')
  · exact highestConfirmedAlg1_slot_ge_of_mem (bal₀ := bal₀) (e' := et') hcase hBblk hBconf
  · rw [Finset.mem_Icc] at hcase
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
    have hBsafe' : isLMDGHOSTSafe τ fm cm pb (gjFFG bal₀ 𝒱 v (τ.st (τ.slotOf t')))
        (𝒱 v (τ.st (τ.slotOf t'))) B (τ.st (τ.slotOf t')) :=
      canonical_epoch_imp_safe_flt hSync hNF hHB hcm hcover hpb
        (lt_of_lt_of_le hβ4 (min_le_right _ _)) hBne hBlt hslefe hgstS
        hBcanon hv (le_trans hst_fse1 (le_refl _))
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
    obtain ⟨hBconf', _hdelBAll', _hGFB', _hpartB', _hsrcB'⟩ :=
      hBundle hv hBsafe'
    have hrange : τ.slotOf t' ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t') := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_refl _⟩
      have hstep : τ.fslot et' + 1 ≤ τ.fslot (et' + 1) := by
        change et' * τ.slotsPerEpoch + 1 ≤ (et' + 1) * τ.slotsPerEpoch
        have hexp : (et' + 1) * τ.slotsPerEpoch = et' * τ.slotsPerEpoch + τ.slotsPerEpoch := by ring
        rw [hexp]
        exact Nat.add_le_add_left hEpos (et' * τ.slotsPerEpoch)
      exact le_trans hstep hfse1_le
    have hB''slot := highestConfirmedAlg1_slot_ge_of_mem (bal₀ := bal₀) (e' := et') (t' := t')
      (v := v) (s' := τ.slotOf t') hrange hBmem hBconf'
    rw [← hB''def] at hB''slot
    exact hB''slot

end FastConfirmation.HFC

end
