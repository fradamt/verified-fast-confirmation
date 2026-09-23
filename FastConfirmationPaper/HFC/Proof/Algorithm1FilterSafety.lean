module
public import FastConfirmationPaper.HFC.Proof.JustifiedChainFilterSafety
public import FastConfirmationPaper.HFC.Proof.CheckpointCertificate
public import FastConfirmationPaper.HFC.Proof.Safety
public import FastConfirmationPaper.HFC.Proof.AnchorRule

@[expose] public section

/-!
# HFC / Proof / NeverFilteredAlg1 — the Algorithm-1 never-filter

`confirmedNotFFGFiltered_alg1_proved` is `confirmedNotFFGFiltered_proved` with its single gate
consumption (the ANCESTOR-case `greatestRealizedJustified_on_chain` call) replaced by
`greatestRealizedJustified_on_chain_from_confirmation` — so the FFG never-filter is driven by
Algorithm 1's local `willChkpBeJustified` (+ the assumed Gasper `P-link` and the committee
partition) instead of the assumed semantic gate
`WillNoConflictingChkpBeJustified`. The module proves both the current-epoch
branch (`epochOf s = epochOf b.slot`) and the previous-epoch branch, then
combines them for the full Algorithm-1 statement.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **The never-filter from Algorithm 1 (current-epoch).** For a current-epoch confirmation of `b`
    (`hte : epochOf s = epochOf b.slot`), with Algorithm 1's `willChkpBeJustified(b)` (`hwill`), the
    Gasper common-source `P-link` (`hsrc`), the committee partition (`hpart`), the justified anchor
    `S = vs(b, st s)` delivered (`hSjust`), and the GU-anchor inputs for `b` (`hGUb`, `hGFr`), every
    safe descendant's ancestor is `NeverFiltered`. The gate is gone — its ANCESTOR comparability is
    now `greatestRealizedJustified_on_chain_from_confirmation` (which derives the §4.1 certificate
    inline). -/
theorem confirmedNotFFGFiltered_alg1_proved (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} {B : Block n} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1))) (hbB : b ≼ B)
    (hBsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) B (τ.st s))
    (hwe0 : 0 ≤ we) (hbwf : b.WellFormed)
    (hte : τ.epochOf s = τ.epochOf b.slot)
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1))
                      (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))))
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf b.slot) (τ.st s))
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
      τ.epochOf sl = τ.epochOf b.slot → i ∈ cm.member sl →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
        = ruleVotingSource bal₀ τ b (τ.st s))
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (ruleVotingSource bal₀ τ b (τ.st s)))
    (hGUb : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      ∃ GUc : Checkpoint n, Justified bal₀ (𝒱 w t') GUc ∧
        GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b)
    (hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block)
    (hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') :
    NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 B (τ.st s) := by
  intro k hk_ge hHead w hw t' hk_eq ht' B' hB'B
  classical
  have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t) C₁ → Justified bal₀ (𝒱 w t) C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block :=
    hAS.2.1
  have hGU := hGUb hw ht'
  have hsel := hselAt hw ht'
  have hs_le_St' : s ≤ τ.slotOf t' := by
    have hd : τ.slotOf (τ.st s) ≤ τ.slotOf t' :=
      Nat.div_le_div_right (by rw [hslots] at ht'; exact ht')
    rw [hslots] at hd; exact hd
  have hB_le_s : B.slot ≤ s := by
    by_cases hBne0 : B = Block.genesis
    · rw [hBne0]; exact Nat.zero_le _
    · obtain ⟨_hBwf0, hBslot00⟩ :=
        safe_block_wf_slot (C := bal₀) (hVV _ _) (hcm (w := v) (t := τ.st s)) hpb hBsafe hBne0
      rw [hslots] at hBslot00
      exact le_trans hBslot00 (Nat.sub_le _ 1)
  have hB_le_St' : B.slot ≤ τ.slotOf t' := le_trans hB_le_s hs_le_St'
  have hbt' : τ.epochOf B.slot ≤ τ.epochOf (τ.slotOf t') := Nat.div_le_div_right hB_le_St'
  by_cases hcase : τ.epochOf s < (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch
  · -- DESCENDANT case — verbatim from `confirmedNotFFGFiltered_proved`.
    set eGJ := (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch with heGJ
    have hHead' : ∀ ⦃j : Slot⦄, s ≤ j → j < k → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
        B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
          (τ.st j) := by
      intro j hj1 hjk i hi
      exact hHead (by rw [hslots]; exact hj1) hjk hi
    have hreal : eGJ < τ.epochOf (τ.slotOf t') :=
      greatestRealizedJustified_realized_of_pos bal₀ τ (𝒱 w t') t'
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hcase)
    have hlo : s ≤ τ.fslot eGJ := by
      have h1 : s ≤ τ.lslot (τ.epochOf s) := le_lslot_epochOf τ s
      have h2 : τ.lslot (τ.epochOf s) < τ.fslot (τ.epochOf s + 1) := by
        unfold Timing.lslot Timing.fslot
        have hE1 : τ.slotsPerEpoch - 1 < τ.slotsPerEpoch := Nat.sub_lt τ.hSlotsPerEpoch Nat.one_pos
        calc τ.epochOf s * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1)
              < τ.epochOf s * τ.slotsPerEpoch + τ.slotsPerEpoch := Nat.add_lt_add_left hE1 _
          _ = (τ.epochOf s + 1) * τ.slotsPerEpoch := by ring
      have h3 : τ.fslot (τ.epochOf s + 1) ≤ τ.fslot eGJ := by
        unfold Timing.fslot; exact Nat.mul_le_mul_right τ.slotsPerEpoch hcase
      exact le_trans (le_trans h1 (le_of_lt h2)) h3
    have hhi : τ.lslot eGJ < k := by
      rw [hk_eq] at hreal
      unfold Timing.lslot
      have hE1 : τ.slotsPerEpoch - 1 < τ.slotsPerEpoch := Nat.sub_lt τ.hSlotsPerEpoch Nat.one_pos
      have hub : eGJ * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) < (eGJ + 1) * τ.slotsPerEpoch := by
        calc eGJ * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1)
              < eGJ * τ.slotsPerEpoch + τ.slotsPerEpoch := Nat.add_lt_add_left hE1 _
          _ = (eGJ + 1) * τ.slotsPerEpoch := by ring
      have hle : (eGJ + 1) * τ.slotsPerEpoch ≤ k := by
        have : eGJ + 1 ≤ τ.epochOf k := hreal
        calc (eGJ + 1) * τ.slotsPerEpoch
              ≤ τ.epochOf k * τ.slotsPerEpoch := Nat.mul_le_mul_right τ.slotsPerEpoch this
          _ = k / τ.slotsPerEpoch * τ.slotsPerEpoch := rfl
          _ ≤ k := Nat.div_mul_le_self k τ.slotsPerEpoch
      exact lt_of_lt_of_le hub hle
    have hcanonGJ : CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 B eGJ :=
      canonicalEpoch_of_headWindow hHead' hlo hhi
    have hBep_s : τ.epochOf B.slot ≤ τ.epochOf s := Nat.div_le_div_right hB_le_s
    have hBGJ : B ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
      realizedGJ_descends_of_canonicalEpoch hwit hByz hNF hnoequiv hw hcanonGJ
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hcase) rfl
        (Nat.lt_of_le_of_lt hBep_s hcase)
        (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t')
    exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hBGJ)
  · -- ANCESTOR case: the gate consumption is replaced by `on_chain_from_confirmation`.
    push Not at hcase
    have hcompB : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ B
        ∨ B ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block := by
      -- head-safety for `b` over `[slotOf(st s), slotOf t')` (from `hHead` on `B`, `b ≼ B`).
      have hHeadb : ∀ ⦃j : Slot⦄, τ.slotOf (τ.st s) ≤ j → j < τ.slotOf t' →
          ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
          b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
            (τ.st j) := by
        intro j hj1 hj2 i hi
        exact Block.Ancestor.trans hbB (hHead hj1 (by rw [← hk_eq]; exact hj2) hi)
      -- GST at `lslot(epoch b)`: `gst ≤ st(s-1) ≤ st(lslot(epoch b))`.
      have hslsb : s - 1 ≤ τ.lslot (τ.epochOf b.slot) := by
        have hsl : s ≤ τ.lslot (τ.epochOf b.slot) := by rw [← hte]; exact le_lslot_epochOf τ s
        exact Nat.le_trans (Nat.sub_le s 1) hsl
      have hgstb : τ.AfterGST (τ.st (τ.lslot (τ.epochOf b.slot))) :=
        le_trans hgst (by unfold Timing.st; exact Nat.mul_le_mul_right τ.slotDur hslsb)
      have hteb : τ.epochOf (τ.slotOf (τ.st s)) = τ.epochOf b.slot := by rw [hslots]; exact hte
      have hbt'b : τ.epochOf b.slot ≤ τ.epochOf (τ.slotOf t') := by
        rw [← hte]; exact Nat.div_le_div_right hs_le_St'
      have hGJub : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ τ.epochOf b.slot := by
        rw [← hte]; exact hcase
      have hbGJ : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b :=
        greatestRealizedJustified_on_chain_from_confirmation bal₀ hv hSync.messageRelay
          hSync.monotone hHB hnoequiv (hcm (w := v) (t := τ.st s)) hgstb hteb hwe0 hbwf hpart hwill
          hsrc hSjust huniq hw hbt'b hHeadb hGU hGJub
      exact Or.inl (Block.Ancestor.trans hbGJ hbB)
    rcases hcompB with hGJb | hBleGJ
    · have hGFGJ : (greatestFinalized bal₀ (𝒱 w t')).block ≼
          (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block := hGFr hw ht'
      rcases GJ_le_or_ge_B' hGJb (Block.Ancestor.refl B) hB'B with hD1 | hGJB'
      · exact keep_of_ancestor_GJ hsel hD1
      · have hGFB' : (greatestFinalized bal₀ (𝒱 w t')).block ≼ B' :=
          Block.Ancestor.trans hGFGJ hGJB'
        by_cases hBne : B = Block.genesis
        · have hB'gen : B' = Block.genesis := by
            rw [hBne] at hB'B; cases hB'B with | refl => rfl
          exact Or.inl (by rw [hB'gen]; exact genesis_ancestor _)
        · have hB'mem : B' ∈ (𝒱 w t').blocks :=
            chain_in_view hSync hNF hHB (hcm (w := v) (t := τ.st s)) hpb hv
              (by rw [hslots]; exact hs1) (by rw [hslots]; exact hgst) hBne hBsafe hw
              (by rw [hslots]; rw [hslots] at ht'; exact ht') hB'B
          obtain ⟨hBwf, _hBslot0⟩ :=
            safe_block_wf_slot (C := bal₀) (hVV _ _) (hcm (w := v) (t := τ.st s)) hpb hBsafe hBne
          have hB'slot : B'.slot ≤ τ.slotOf t' :=
            le_trans (slot_le_of_ancestor hB'B hBwf) hB_le_St'
          obtain ⟨b'', hb''mem, hB'b'', hb''slot, hGFb'', hep, hleaf, hvs⟩ :=
            ffg_leaf_witness hwit hB'mem hB'slot hGFB' hGJB'
              (fun h₁ h₂ he => hAS.2.1 hw (t := t') h₁ h₂ he)
          have hGJB'_rule : (ruleRealizedGJ bal₀ τ (𝒱 w t') t').block ≼ B' := by
            rw [hsel.1]; exact hGJB'
          have hGFb''_rule : (ruleRealizedGF bal₀ τ (𝒱 w t') t').block ≼ b'' := by
            rw [hsel.2.1]; exact hGFb''
          have hVS_eq : ruleVotingSource bal₀ τ b'' t'
              = votingSource bal₀ τ (𝒱 w t') b'' t' :=
            hsel.2.2 hb''mem hb''slot
          have hvs_rule :
              ruleVotingSource bal₀ τ b'' t' = ruleRealizedGJ bal₀ τ (𝒱 w t') t'
              ∨ (ruleVotingSource bal₀ τ b'' t').epoch + 2 ≥ τ.epochOf (τ.slotOf t') := by
            rcases hvs with hleft | hright
            · left
              rw [hVS_eq, hsel.1]
              exact hleft
            · right
              rw [hVS_eq]
              exact hright
          exact Or.inr ⟨hGJB'_rule, b'', hb''mem, hB'b'', hGFb''_rule, hep, hleaf, hvs_rule⟩
    · exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hBleGJ)

/-- **Canonicity helper (current-epoch Algorithm 1).** `b` is on every honest LMD-GHOST-HFC head
    from `st s` on — the never-filter (`confirmedNotFFGFiltered_alg1_proved`, `b` itself the safe
    block) fed to the §3.1 engine (`hfc_canonical_from_engine`). The function form (no `∃ t0`) that
    monotonicity reuses at each `highestConfirmedSinceEpoch` block. -/
theorem hfc_canonical_alg1 (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ s)
    (hsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) b (τ.st s))
    (hwe0 : 0 ≤ we) (hte : τ.epochOf s = τ.epochOf b.slot)
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1))
                      (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))))
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf b.slot) (τ.st s))
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
      τ.epochOf sl = τ.epochOf b.slot → i ∈ cm.member sl →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
        = ruleVotingSource bal₀ τ b (τ.st s))
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (ruleVotingSource bal₀ τ b (τ.st s)))
    (hGUb : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      ∃ GUc : Checkpoint n, Justified bal₀ (𝒱 w t') GUc ∧
        GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b)
    (hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block)
    (hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' :=
  hfc_canonical_from_engine bal₀ hSync hNF hHB hVV hcm hpb hv hbwf hbslot hs1 hgst hsafe
    (confirmedNotFFGFiltered_alg1_proved bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz hs1
      hgst (Block.Ancestor.refl b) hsafe hwe0 hbwf hte hpart hwill hsrc hSjust hGUb hGFr hselAt)



/-- The canonicity function (no `∃ t0`) of `hfc_safety_alg1_of_confirmed` — `b` on every honest head
    from `st s` on, from `isConfirmedNoCaching(b, st s)` + the Gasper/anchor interface. Monotonicity
    reuses this per `highestConfirmedSinceEpoch` block. -/
theorem hfc_canonical_alg1_of_confirmed (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ s) (hwe0 : 0 ≤ we)
    (hcur : τ.epochOf b.slot = τ.epochOf (τ.slotOf (τ.st s)))
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b (τ.st s))
    (hdel : OnChainAnchorInterface bal₀ fm τ 𝒱 b (τ.st s))
    (hGF : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t')
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1))
                      (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))))
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
      τ.epochOf sl = τ.epochOf b.slot → i ∈ cm.member sl →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
        = ruleVotingSource bal₀ τ b (τ.st s)) :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have hconf' := hconf
  unfold isConfirmedNoCaching at hconf'
  rw [if_pos hcur] at hconf'
  obtain ⟨hwill0, _hgjep, hsafe⟩ := hconf'
  have hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf b.slot) (τ.st s) := by
    rw [hcur]; exact hwill0
  have hInputs := greatestJustifiedAnchorInputs_of_interface hdel
    (greatestJustifiedAnchorPrecondition_of_confirmedNoCaching bal₀ hv hconf hdel hcur) hGF
  have hGUb : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      ∃ GUc : Checkpoint n, Justified bal₀ (𝒱 w t') GUc ∧
        GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b :=
    fun w hw t' ht' => (hInputs hw ht').1
  have hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
    fun w hw t' ht' => greatestFinalized_block_ancestor_greatestRealizedJustified bal₀ τ (𝒱 w t') t'
      (hAS.2.2 hw (t := t')) (hGF hw ht').1
  have hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t' :=
    fun w hw t' ht' => (hGF hw ht').2
  have hte : τ.epochOf s = τ.epochOf b.slot := by
    have h := hcur; rw [hslots] at h; exact h.symm
  have hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (ruleVotingSource bal₀ τ b (τ.st s)) := by
    intro w hw t' ht'
    refine hdel.ruleVotingSource_justified hw ?_
    have hsle : s ≤ τ.lslot (τ.epochOf b.slot) + 1 := by
      have hsl : s ≤ τ.lslot (τ.epochOf b.slot) := by
        rw [← hte]
        exact le_lslot_epochOf τ s
      exact Nat.le_succ_of_le hsl
    rw [hslots]
    exact le_trans (Timing.st_le_st τ hsle) ht'
  exact hfc_canonical_alg1 bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz hs1 hgst hbwf hbslot
    hsafe hwe0 hte hpart hwill hsrc hSjust hGUb hGFr hselAt

/-! ### Previous-epoch Algorithm-1 never-filter (confirmation at the first slot of the next
epoch) -/

/-- **The never-filter from Algorithm 1 (PREVIOUS-epoch) — faithful route, specialized to `B = b`.**
    The previous-epoch analogue of `confirmedNotFFGFiltered_alg1_proved`, for a confirmation at the
    **first slot of the next epoch**: `s = fslot(epochOf s)` (`hsfirst`) and `epochOf s = ec + 1`
    (`hteP`, `ec` the certificate epoch). The safe block tracked is **`b` itself** — the single use
    site (`hfc_canonical_alg1_prev`) calls it with `Block.Ancestor.refl b`, so the general `B ⪰ b`
    parameter is dropped: this is what lets the crux's *compatibility* output feed the
    `hcompB` split directly (two descendants of `b` need not be comparable, so a general `B` could
    not). The case split on the realized `GJ`'s epoch is at `ec`:
    * **DESCENDANT `ec < GJ.epoch`** — the ladder, exactly as before, reaching the boundary epoch
      `ec+1 = epochOf s`; safe block `b` has `epochOf b.slot ≤ ec < eGJ` since `b.slot < s`.
    * **ANCESTOR `GJ.epoch ≤ ec`** — `greatestRealizedJustified_on_chain_from_confirmation_prev`
      supplies the **compatibility** `block(GJ) ~ b` directly (Case A: `messageRelay`
      common-future-view no-conflicting; Case B: the witness source `vs(b',t)` delivered b'-keyed,
      realized via the *proven* bound `hWitUb`), which **is** the `hcompB` the D1/D2 split consumes
      (no `Or.inl (trans …)`). -/
theorem confirmedNotFFGFiltered_alg1_prev_proved (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} {ec : Epoch}
    (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) b (τ.st s))
    (_hwe0 : 0 ≤ we) (_hbwf : b.WellFormed)
    (hteP : τ.epochOf s = ec + 1)
    (hsfirst : s = τ.fslot (τ.epochOf s))
    (hTv : Justified bal₀ (𝒱 v (τ.st s)) (checkpointOf τ b ec))
    {b' : Block n} (hbb' : b ≼ b')
    (hdel' : OnChainAnchorInterface bal₀ fm τ 𝒱 b' (τ.st s))
    (hWitV : Justified bal₀ (𝒱 v (τ.st s)) (ruleVotingSource bal₀ τ b' (τ.st s)))
    (hWitUb : (ruleVotingSource bal₀ τ b' (τ.st s)).epoch ≤ ec)
    (hWitLo : ec ≤ (ruleVotingSource bal₀ τ b' (τ.st s)).epoch + 1)
    (hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block)
    (hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') :
    NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 b (τ.st s) := by
  intro k hk_ge hHead w hw t' hk_eq ht' B' hB'B
  classical
  have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t) C₁ → Justified bal₀ (𝒱 w t) C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block :=
    hAS.2.1
  have hsel := hselAt hw ht'
  have hs_le_St' : s ≤ τ.slotOf t' := by
    have hd : τ.slotOf (τ.st s) ≤ τ.slotOf t' :=
      Nat.div_le_div_right (by rw [hslots] at ht'; exact ht')
    rw [hslots] at hd; exact hd
  -- `s = (ec+1)·E` (first slot of epoch `ec+1 = epochOf s`).
  have hs_eq : s = (ec + 1) * τ.slotsPerEpoch := by
    conv_lhs => rw [hsfirst]
    unfold Timing.fslot; rw [hteP]
  -- the safe block `b` sits strictly before `s`, hence in epoch `≤ ec`.
  have hb_lt_s : b.slot < s := by
    by_cases hbne0 : b = Block.genesis
    · rw [hbne0]; exact hs1
    · obtain ⟨_hbwf0, hbslot00⟩ :=
        safe_block_wf_slot (C := bal₀) (hVV _ _) (hcm (w := v) (t := τ.st s)) hpb hsafe hbne0
      rw [hslots] at hbslot00
      exact Nat.lt_of_le_of_lt hbslot00 (Nat.sub_lt hs1 Nat.one_pos)
  have hbep_b : τ.epochOf b.slot ≤ ec := by
    have hlt : b.slot < (ec + 1) * τ.slotsPerEpoch := by rw [← hs_eq]; exact hb_lt_s
    have : b.slot / τ.slotsPerEpoch < ec + 1 :=
      (Nat.div_lt_iff_lt_mul τ.hSlotsPerEpoch).mpr hlt
    exact Nat.lt_succ_iff.mp this
  have hb_le_St' : b.slot ≤ τ.slotOf t' := le_trans (le_of_lt hb_lt_s) hs_le_St'
  -- `ec < epochOf(slotOf t')` (since `s = fslot(ec+1) ≤ slotOf t'`).
  have hbt'P : ec < τ.epochOf (τ.slotOf t') := by
    have h : τ.epochOf s ≤ τ.epochOf (τ.slotOf t') := Nat.div_le_div_right hs_le_St'
    rw [hteP] at h; exact h
  by_cases hcase : ec < (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch
  · -- DESCENDANT case — the ladder, reaching the boundary epoch `ec+1 = epochOf s`.
    set eGJ := (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch with heGJ
    have hHead' : ∀ ⦃j : Slot⦄, s ≤ j → j < k → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
        b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
          (τ.st j) := by
      intro j hj1 hjk i hi
      exact hHead (by rw [hslots]; exact hj1) hjk hi
    have hreal : eGJ < τ.epochOf (τ.slotOf t') :=
      greatestRealizedJustified_realized_of_pos bal₀ τ (𝒱 w t') t'
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hcase)
    have hlo : s ≤ τ.fslot eGJ := by
      rw [hs_eq]; unfold Timing.fslot
      exact Nat.mul_le_mul_right τ.slotsPerEpoch hcase
    have hhi : τ.lslot eGJ < k := by
      rw [hk_eq] at hreal
      unfold Timing.lslot
      have hE1 : τ.slotsPerEpoch - 1 < τ.slotsPerEpoch := Nat.sub_lt τ.hSlotsPerEpoch Nat.one_pos
      have hub : eGJ * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) < (eGJ + 1) * τ.slotsPerEpoch := by
        calc eGJ * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1)
              < eGJ * τ.slotsPerEpoch + τ.slotsPerEpoch := Nat.add_lt_add_left hE1 _
          _ = (eGJ + 1) * τ.slotsPerEpoch := by ring
      have hle : (eGJ + 1) * τ.slotsPerEpoch ≤ k := by
        have : eGJ + 1 ≤ τ.epochOf k := hreal
        calc (eGJ + 1) * τ.slotsPerEpoch
              ≤ τ.epochOf k * τ.slotsPerEpoch := Nat.mul_le_mul_right τ.slotsPerEpoch this
          _ = k / τ.slotsPerEpoch * τ.slotsPerEpoch := rfl
          _ ≤ k := Nat.div_mul_le_self k τ.slotsPerEpoch
      exact lt_of_lt_of_le hub hle
    have hcanonGJ : CanonicalThroughoutEpoch τ fm boost pb bal₀ 𝒱 b eGJ :=
      canonicalEpoch_of_headWindow hHead' hlo hhi
    have hbGJ : b ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
      realizedGJ_descends_of_canonicalEpoch hwit hByz hNF hnoequiv hw hcanonGJ
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hcase) rfl
        (Nat.lt_of_le_of_lt hbep_b hcase)
        (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t')
    exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hbGJ)
  · -- ANCESTOR case: prev-epoch *compatibility* `block(GJ) ~ b` direct from the faithful crux.
    push Not at hcase
    have hgst_cert : τ.AfterGST (τ.st (τ.slotOf (τ.st s))) := by
      rw [hslots]; exact le_trans hgst (Timing.st_le_st τ (Nat.sub_le s 1))
    have hcompB : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b
        ∨ b ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
      greatestRealizedJustified_on_chain_from_confirmation_prev bal₀ hv hSync.messageRelay
        hSync.monotone hgst_cert hTv hbb'
        (fun {Cc} hchain hlocal {w} hw {t'} ht'' =>
          OnChainAnchorInterface.justified hdel' (Cc := Cc) hchain hlocal (w := w) hw
            (t' := t') ht'')
        hWitV hWitUb hWitLo huniq hw ht' hbt'P hcase
    rcases hcompB with hGJb | hbleGJ
    · have hGFGJ : (greatestFinalized bal₀ (𝒱 w t')).block ≼
          (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block := hGFr hw ht'
      rcases GJ_le_or_ge_B' hGJb (Block.Ancestor.refl b) hB'B with hD1 | hGJB'
      · exact keep_of_ancestor_GJ hsel hD1
      · have hGFB' : (greatestFinalized bal₀ (𝒱 w t')).block ≼ B' :=
          Block.Ancestor.trans hGFGJ hGJB'
        by_cases hbne : b = Block.genesis
        · have hB'gen : B' = Block.genesis := by
            rw [hbne] at hB'B; cases hB'B with | refl => rfl
          exact Or.inl (by rw [hB'gen]; exact genesis_ancestor _)
        · have hB'mem : B' ∈ (𝒱 w t').blocks :=
            chain_in_view hSync hNF hHB (hcm (w := v) (t := τ.st s)) hpb hv
              (by rw [hslots]; exact hs1) (by rw [hslots]; exact hgst) hbne hsafe hw
              (by rw [hslots]; rw [hslots] at ht'; exact ht') hB'B
          obtain ⟨hbwf, _hbslot0⟩ :=
            safe_block_wf_slot (C := bal₀) (hVV _ _) (hcm (w := v) (t := τ.st s)) hpb hsafe hbne
          have hB'slot : B'.slot ≤ τ.slotOf t' :=
            le_trans (slot_le_of_ancestor hB'B hbwf) hb_le_St'
          obtain ⟨b'', hb''mem, hB'b'', hb''slot, hGFb'', hep, hleaf, hvs⟩ :=
            ffg_leaf_witness hwit hB'mem hB'slot hGFB' hGJB'
              (fun h₁ h₂ he => hAS.2.1 hw (t := t') h₁ h₂ he)
          have hGJB'_rule : (ruleRealizedGJ bal₀ τ (𝒱 w t') t').block ≼ B' := by
            rw [hsel.1]; exact hGJB'
          have hGFb''_rule : (ruleRealizedGF bal₀ τ (𝒱 w t') t').block ≼ b'' := by
            rw [hsel.2.1]; exact hGFb''
          have hVS_eq : ruleVotingSource bal₀ τ b'' t'
              = votingSource bal₀ τ (𝒱 w t') b'' t' :=
            hsel.2.2 hb''mem hb''slot
          have hvs_rule :
              ruleVotingSource bal₀ τ b'' t' = ruleRealizedGJ bal₀ τ (𝒱 w t') t'
              ∨ (ruleVotingSource bal₀ τ b'' t').epoch + 2 ≥ τ.epochOf (τ.slotOf t') := by
            rcases hvs with hleft | hright
            · left
              rw [hVS_eq, hsel.1]
              exact hleft
            · right
              rw [hVS_eq]
              exact hright
          exact Or.inr ⟨hGJB'_rule, b'', hb''mem, hB'b'', hGFb''_rule, hep, hleaf, hvs_rule⟩
    · exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hbleGJ)

/-- **Canonicity helper (PREVIOUS-epoch Algorithm 1).** `b` is on every honest LMD-GHOST-HFC head
    from `st s` on — the prev-epoch never-filter (`confirmedNotFFGFiltered_alg1_prev_proved`, `b`
    itself the safe block) fed to the §3.1 engine (`hfc_canonical_from_engine`). -/
theorem hfc_canonical_alg1_prev (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} {ec : Epoch} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ s)
    (hsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) b (τ.st s))
    (hwe0 : 0 ≤ we)
    (hteP : τ.epochOf s = ec + 1)
    (hsfirst : s = τ.fslot (τ.epochOf s))
    (hTv : Justified bal₀ (𝒱 v (τ.st s)) (checkpointOf τ b ec))
    {b' : Block n} (hbb' : b ≼ b')
    (hdel' : OnChainAnchorInterface bal₀ fm τ 𝒱 b' (τ.st s))
    (hWitV : Justified bal₀ (𝒱 v (τ.st s)) (ruleVotingSource bal₀ τ b' (τ.st s)))
    (hWitUb : (ruleVotingSource bal₀ τ b' (τ.st s)).epoch ≤ ec)
    (hWitLo : ec ≤ (ruleVotingSource bal₀ τ b' (τ.st s)).epoch + 1)
    (hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block)
    (hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' :=
  hfc_canonical_from_engine bal₀ hSync hNF hHB hVV hcm hpb hv hbwf hbslot hs1 hgst hsafe
    (confirmedNotFFGFiltered_alg1_prev_proved bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz
      hs1 hgst hsafe hwe0 hbwf hteP hsfirst hTv hbb' hdel' hWitV hWitUb hWitLo hGFr hselAt)


/-- **Canonicity helper from `isConfirmedNoCaching` directly (PREVIOUS-epoch) — faithful route.**
    The previous-epoch analogue of `hfc_canonical_alg1_of_confirmed`: it folds the rule's literal
    else-branch predicate `isConfirmedNoCaching(b, st s)` into the raw `hfc_canonical_alg1_prev`
    premises. From the branch we read off the **witness** `b' ⪰ b` and its AU source
    `A = ruleVotingSource(b', st s)`, and derive:

    * `hTv` — the epoch-`ec` certificate (Case A), from `willChkpBeJustified(b, epoch(t)-1)` via
      `checkpoint_justified_of_confirmedNoCaching_prev` (empty future committee);
    * `hWitUb` — `A.epoch ≤ ec`, the realization bound *proven* via
      `justified_epoch_le_of_firstSlot` (needs `SlotCommitteeMinority` — the new `hSCM` premise);
    * `hWitLo` — `ec ≤ A.epoch + 1`, the rule's revived lower-bound recency `≥ epoch(t)-2`;
    * `hdel'` — the **b'-keyed** AU interface `hdelAll (X := b')`, applied to the settled
      `epoch(t)-2` anchor `A`.

    This keeps the paper's previous-epoch branch conjunct set (no source upper bound, no
    `vs.block ≼ b` ancestor conjunct): the witness source is delivered keyed at `b'` (not a
    contemporaneous certificate at `b`), and the never-filter concludes only *compatibility*
    `block(GJ) ~ b`. -/
theorem hfc_canonical_alg1_prev_of_confirmed (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ s) (hwe0 : 0 ≤ we)
    (hprev : ¬ τ.epochOf b.slot = τ.epochOf (τ.slotOf (τ.st s)))
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b (τ.st s))
    (hdelRule : OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 b (τ.st s))
    (hSCM : SlotCommitteeMinority fm cm bal₀)
    (hGF : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  -- Destructure the rule's previous-epoch (else) branch (keep the witness `b'` + recency).
  have hconf' := hconf
  unfold isConfirmedNoCaching at hconf'
  rw [if_neg hprev] at hconf'
  obtain ⟨hfirst, hwill0, b', hb'mem, hbb', hb'ep, hrec_lo, hsafe⟩ := hconf'
  -- Certificate epoch `ec = epochOf s - 1`, introduced as a genuine variable (`τ.epochOf` is opaque
  -- division, so `omega` reasons only over `hteP`/the recency bounds as atoms).
  have hepos : 1 ≤ τ.epochOf s := by
    have h : τ.epochOf b'.slot < τ.epochOf s := by rw [hslots] at hb'ep; exact hb'ep
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) h
  obtain ⟨ec, hteP⟩ : ∃ ec : Epoch, τ.epochOf s = ec + 1 :=
    ⟨τ.epochOf s - 1, (Nat.succ_pred_eq_of_pos hepos).symm⟩
  have hsfirst : s = τ.fslot (τ.epochOf s) := by
    have h := hfirst; rw [hslots] at h; exact h
  have hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b ec (τ.st s) := by
    have h := hwill0; rw [hslots] at h
    have hee : τ.epochOf s - 1 = ec := by rw [hteP, Nat.add_sub_cancel]
    rwa [hee] at h
  have hSjustB : Justified bal₀ (𝒱 v (τ.st s)) (ruleVotingSource bal₀ τ b (τ.st s)) :=
    hdelRule.1.ruleVotingSource_justified hv (by rw [hslots])
  -- The epoch-`ec` certificate `C(b, ec)` (Case A), from the empty-future reservation.
  have hTv : Justified bal₀ (𝒱 v (τ.st s)) (checkpointOf τ b ec) :=
    checkpoint_justified_of_confirmedNoCaching_prev bal₀ hwe0 hteP hsfirst hwill hSjustB
  have hdel' : OnChainAnchorInterface bal₀ fm τ 𝒱 b' (τ.st s) :=
    hdelRule.2 hv hb'mem hbb' hb'ep
  -- The witness source `A = ruleVotingSource(b', st s)` (Case B) is the AU Def-2 selector on
  -- `chain(b')`, then made visible in the confirming view by the b'-keyed AU interface.
  have hWitV : Justified bal₀ (𝒱 v (τ.st s)) (ruleVotingSource bal₀ τ b' (τ.st s)) :=
    hdel'.ruleVotingSource_justified hv (by rw [hslots])
  -- realization bound `A.epoch ≤ ec`, PROVEN from `SlotCommitteeMinority` (no current-epoch
  -- checkpoint can be justified at the epoch's first slot).
  have hWitUb : (ruleVotingSource bal₀ τ b' (τ.st s)).epoch ≤ ec :=
    justified_epoch_le_of_firstSlot bal₀ hVV hNF hnoequiv hByz hSCM hSync.noFutureMessages hv hteP
      hsfirst hWitV
  -- recency lower bound `ec ≤ A.epoch + 1`, from the rule's revived `epoch(vs) ≥ epoch(t)-2`.
  have hWitLo : ec ≤ (ruleVotingSource bal₀ τ b' (τ.st s)).epoch + 1 := by
    have hlo := hrec_lo
    rw [hslots, hteP, show ec + 1 - 2 = ec - 1 from Nat.succ_sub_succ ec 1] at hlo
    exact Nat.sub_le_iff_le_add.mp hlo
  have hGFr : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).block ≼
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
    fun w hw t' ht' => greatestFinalized_block_ancestor_greatestRealizedJustified bal₀ τ (𝒱 w t') t'
      (hAS.2.2 hw (t := t')) (hGF hw ht').1
  have hselAt : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.slotOf (τ.st s)) ≤ t' → FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t' :=
    fun w hw t' ht' => (hGF hw ht').2
  exact hfc_canonical_alg1_prev bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz hs1 hgst hbwf
    hbslot hsafe hwe0 hteP hsfirst hTv hbb' hdel' hWitV hWitUb hWitLo hGFr hselAt


/-- **Unified canonicity from `isConfirmedNoCaching` (both branches).** Dispatches on
    `epoch(b) = epoch(t)` to `hfc_canonical_alg1_of_confirmed` (current-epoch) or
    `hfc_canonical_alg1_prev_of_confirmed` (previous-epoch); the previous-epoch branch ignores the
    current-epoch-only `hpart`/`hsrc` interface (it instead reads off the rule's witness
    `b'` and uses the rule-scoped AU interface + `SlotCommitteeMinority`). That scoped interface
    covers both the current-epoch GU-anchor (`b`) and any previous-epoch witness source
    (`b'`). The single entry point safety and monotonicity use. -/
theorem hfc_canonical_alg1_unified_of_confirmed (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    {s : Slot} (hs1 : 1 ≤ s) (hgst : τ.AfterGST (τ.st (s - 1)))
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ s) (hwe0 : 0 ≤ we)
    (hconf : isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b (τ.st s))
    (hdelRule : OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 b (τ.st s))
    (hSCM : SlotCommitteeMinority fm cm bal₀)
    (hGF : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
      (greatestFinalized bal₀ (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t')
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1))
                      (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))))
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
      τ.epochOf sl = τ.epochOf b.slot → i ∈ cm.member sl →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
        = ruleVotingSource bal₀ τ b (τ.st s)) :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  by_cases hcur : τ.epochOf b.slot = τ.epochOf (τ.slotOf (τ.st s))
  · exact hfc_canonical_alg1_of_confirmed bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz hs1
      hgst hbwf hbslot hwe0 hcur hconf hdelRule.1 hGF hpart hsrc
  · exact hfc_canonical_alg1_prev_of_confirmed bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz
      hs1 hgst hbwf hbslot hwe0 hcur hconf hdelRule hSCM hGF

/-- Public-shape Algorithm-1 safety wrapper: if `b` is confirmed by the top-level Algorithm-1
    selector, run the existing canonicity proof on the selected block `B` and inherit canonicity
    back to `b` by ancestry. -/
theorem hfc_safety_alg1_wrapper (bal₀ : Stakes n) {τ : Timing} {fm : FaultModel n}
    {cm : Committees n} {pb : Weight} {boost : ProposerBoost n (FFGVote n)}
    {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hSCM : SlotCommitteeMinority fm cm bal₀)
    {v : Validator n} {b : Block n} {s : Slot} {we : Weight}
    (hv : v ∈ fm.honest) (_hs1 : 1 ≤ s) (_hgst : τ.AfterGST (τ.st (s - 1)))
    (_hbwf : b.WellFormed) (_hbslot : b.slot ≤ s) (hwe0 : 0 ≤ we)
    (hconf : isConfirmedAlg1 bal₀ fm cm pb we τ 𝒱 v b (τ.st s))
    (hIF : Alg1SelectorSafetyInterface τ fm cm pb we boost bal₀ 𝒱 v
      (highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v
        (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s))
      (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s)) :
    ∃ t0 : Time, ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → t0 ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  let B := highestConfirmedSinceEpochAlg1 bal₀ fm cm pb we τ 𝒱 v
    (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s)
  change Alg1SelectorSafetyInterface τ fm cm pb we boost bal₀ 𝒱 v B
    (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s) at hIF
  have hbB : b ≼ B := by
    simpa [isConfirmedAlg1, Alg1.isConfirmed, highestConfirmedSinceEpochAlg1, B] using hconf
  rcases highestConfirmedAlg1_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (we := we)
      (𝒱 := 𝒱) bal₀ v (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s) with hgen |
      ⟨sB, hsBmem, hBblk, hconfB⟩
  · have hBgen : B = Block.genesis := by
      simpa [B] using hgen
    refine ⟨0, fun w t' hw ht' => ?_⟩
    have hbgen : b = Block.genesis := by
      have h := hbB
      rw [hBgen] at h
      cases h with
      | refl => rfl
    rw [hbgen]
    exact genesis_ancestor _
  change B ∈ (𝒱 v (τ.st sB)).blocks at hBblk
  change isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v B (τ.st sB) at hconfB
  by_cases hBgen : B = Block.genesis
  · refine ⟨0, fun w t' hw ht' => ?_⟩
    have hbgen : b = Block.genesis := by
      have h := hbB
      rw [hBgen] at h
      cases h with
      | refl => rfl
    rw [hbgen]
    exact genesis_ancestor _
  obtain ⟨hgstB, hIFB⟩ := hIF hsBmem hBblk hconfB
  rw [Finset.mem_Icc] at hsBmem
  have hsB1 : 1 ≤ sB := le_trans (Nat.le_add_left 1 _) hsBmem.1
  have hsafeB : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st sB)) B (τ.st sB) :=
    isLMDGHOSTSafe_of_isConfirmedNoCaching bal₀ hconfB
  have hcmC : CommitteeHonestMajority fm cm bal₀ := hcm (w := v) (t := τ.st sB)
  obtain ⟨hBwf, hBslot0⟩ := safe_block_wf_slot (C := bal₀) (hVV _ _) hcmC hpb hsafeB hBgen
  rw [Timing.slotOf_st] at hBslot0
  have hBslot : B.slot ≤ sB := le_trans hBslot0 (Nat.sub_le _ 1)
  obtain ⟨hdelAll, hGF, hpart, hsrc⟩ := hIFB
  exact ⟨τ.st sB, fun w t' hw ht' =>
    Block.Ancestor.trans hbB
      (hfc_canonical_alg1_unified_of_confirmed bal₀ hSync hNF hHB hVV hcm hpb hv hAS hnoequiv hByz
        hsB1 hgstB hBwf hBslot hwe0 hconfB hdelAll hSCM hGF hpart hsrc hw ht')⟩

/-- Public statement-shaped wrapper for `RuleConfirmedBlockSafety`. -/
theorem hfc_safety_alg1_public (τ : Timing) (bal₀ : Stakes n) : RuleConfirmedBlockSafety τ bal₀ := by
  intro fm cm pb boost 𝒱 gj C hSync hNF hHB hVV hcm hpb hAS hnoequiv hByz hSCM v b s we
  dsimp only
  intro hv hs1 hgst hbwf hbslot hwe0 hconf hIF
  exact hfc_safety_alg1_wrapper C hSync hNF hHB hVV hcm hpb hAS hnoequiv hByz hSCM
    (v := v) (b := b) (s := s) (we := we)
    hv hs1 hgst hbwf hbslot hwe0 hconf hIF

end FastConfirmation.HFC

end
