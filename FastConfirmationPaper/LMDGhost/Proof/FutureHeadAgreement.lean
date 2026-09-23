module
public import Mathlib.Tactic
public import FastConfirmationPaper.LMDGhost.Proof.Support
public import FastConfirmationPaper.LMDGhost.Proof.PositiveWeights
public import FastConfirmationPaper.LMDGhost.Proof.BlockAncestry
public import FastConfirmationPaper.LMDGhost.Proof.HeadCanonicality
public import FastConfirmationPaper.LMDGhost.Proof.Quorum
public import FastConfirmationPaper.LMDGhost.Claims

@[expose] public section

/-!
# LMDGhost / Proof / Monotone

Lemma 1 building blocks: how the committee weight `W` and honest committee weight
`J` grow with the cutoff slot, and the support-set monotonicity that makes the
honest support weight `H` non-decreasing.

The key arithmetic fact (`P_nondecreasing`) is **Lemma 1** in its faithful Def-7
form: the honest LMD-GHOST safety indicator `Phon = H/J` never decreases as the
cutoff grows, provided base supporters persist and every newly-counted honest
committee member supports `b'`. Writing `a = H_{σ₀}`, `b = J_{σ₀}`, and `gH` for the
honest weight of the committee growth set, `J_σ = b + gH` (exactly) while
`H_σ ≥ a + gH`, so `Phon_σ = H_σ/J_σ ≥ (a+gH)/(b+gH) ≥ a/b = Phon_{σ₀}`, the last
step needing only `a ≤ b`, i.e. `H ≤ J` (a free fact — `H_le_J`). **No growth bound
on the adversary is needed** — this is precisely why `HonestGrowth` is unnecessary
and the absolute-margin route was the wrong one: recurring honest validators dedup
identically on numerator and denominator, and adversarial weight never enters `J`.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}




/-- `J` decomposes as the value at `s` plus the honest weight of the committee growth set. -/
theorem J_eq_add_growth (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (b : Block n)
    {s s' : Slot} (h : s ≤ s') :
    J A cm fm b s' = J A cm fm b s
      + totalWeight A ((committeeUnion cm b.psPlus1 s' \ committeeUnion cm b.psPlus1 s).filter
          (fun i => i ∈ fm.honest)) := by
  unfold J totalWeight
  have hset : (committeeUnion cm b.psPlus1 s' \ committeeUnion cm b.psPlus1 s).filter
        (fun i => i ∈ fm.honest)
      = (committeeUnion cm b.psPlus1 s').filter (fun i => i ∈ fm.honest)
          \ (committeeUnion cm b.psPlus1 s).filter (fun i => i ∈ fm.honest) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [add_comm, hset]
  exact (Finset.sum_sdiff (Finset.filter_subset_filter _
    (committeeUnion_mono cm b.psPlus1 h))).symm

/-- Honest support `H` grows by at least the honest weight of the committee growth
    set, when base supporters persist and all new honest committee members support `b'`. -/
theorem H_ge_add_growth (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b' : Block n) {σ₀ σ : Slot} (hσ : σ₀ ≤ σ)
    (hpersist : ∀ i ∈ committeeUnion cm b'.psPlus1 σ₀, i ∈ fm.honest →
      V.supportsLMD b' i σ₀ = true → V.supportsLMD b' i σ = true)
    (hcanon : ∀ i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀,
      i ∈ fm.honest → V.supportsLMD b' i σ = true) :
    H A cm fm V b' σ₀
      + totalWeight A ((committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀).filter
          (fun i => i ∈ fm.honest))
      ≤ H A cm fm V b' σ := by
  set U₀ := committeeUnion cm b'.psPlus1 σ₀ with hU₀
  set U := committeeUnion cm b'.psPlus1 σ with hU
  have hsub : U₀ ⊆ U := committeeUnion_mono cm b'.psPlus1 hσ
  -- The base honest-supporter set, the honest growth set, and their disjoint union.
  set B₀ := U₀.filter (fun i => i ∈ fm.honest ∧ V.supportsLMD b' i σ₀ = true) with hB₀
  set Gh := (U \ U₀).filter (fun i => i ∈ fm.honest) with hGh
  have hdisj : Disjoint B₀ Gh := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi hi'
    exact hi'.1.2 hi.1
  have hunion_sub : B₀ ∪ Gh ⊆ U.filter (fun i => i ∈ fm.honest ∧ V.supportsLMD b' i σ = true) := by
    intro i hi
    simp only [Finset.mem_union, hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi
    simp only [Finset.mem_filter]
    rcases hi with ⟨hiU₀, hih, hisup⟩ | ⟨⟨hiU, hni⟩, hih⟩
    · exact ⟨hsub hiU₀, hih, hpersist i hiU₀ hih hisup⟩
    · exact ⟨hiU, hih, hcanon i (Finset.mem_sdiff.mpr ⟨hiU, hni⟩) hih⟩
  have hHeq : H A cm fm V b' σ₀ = totalWeight A B₀ := rfl
  have hkey : H A cm fm V b' σ₀ + totalWeight A Gh = totalWeight A (B₀ ∪ Gh) := by
    rw [hHeq]
    simp only [totalWeight, Finset.sum_union hdisj]
  rw [hkey]
  unfold H totalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun i _ _ => (A.hpos i).le)

/-- **Lemma 1 (Def-7 form): `Phon` is non-decreasing in the cutoff.** Given the base
    honest committee weight is positive (`hJpos`), base supporters persist, and every
    newly-counted honest committee member supports `b'`, the honest LMD-GHOST safety
    indicator `Phon_{σ₀} = H_{σ₀}/J_{σ₀}` does not exceed `Phon_σ`. The proof is the
    `(a+gH)/(b+gH) ≥ a/b` argument with `a = H_{σ₀}`, `b = J_{σ₀}`, `gH` the honest
    growth-set weight: `J_σ = b + gH` exactly, `H_σ ≥ a + gH`, and `a ≤ b` (`H_le_J`).
    **No adversarial-growth premise.** -/
theorem P_nondecreasing (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b' : Block n) {σ₀ σ : Slot} (hσ : σ₀ ≤ σ)
    (hJpos : 0 < J A cm fm b' σ₀)
    (hpersist : ∀ i ∈ committeeUnion cm b'.psPlus1 σ₀, i ∈ fm.honest →
      V.supportsLMD b' i σ₀ = true → V.supportsLMD b' i σ = true)
    (hcanon : ∀ i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀,
      i ∈ fm.honest → V.supportsLMD b' i σ = true) :
    Phon A cm fm V b' σ₀ ≤ Phon A cm fm V b' σ := by
  -- `a = H_{σ₀}`, `b = J_{σ₀}`, `gH` = honest growth-set weight.
  set gH := totalWeight A ((committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀).filter
      (fun i => i ∈ fm.honest)) with hgH
  have hgH0 : 0 ≤ gH := totalWeight_nonneg A _
  have hHgrow : H A cm fm V b' σ₀ + gH ≤ H A cm fm V b' σ :=
    H_ge_add_growth A cm fm V b' hσ hpersist hcanon
  have hJeq : J A cm fm b' σ = J A cm fm b' σ₀ + gH :=
    J_eq_add_growth A cm fm b' hσ
  have hHJ0 : H A cm fm V b' σ₀ ≤ J A cm fm b' σ₀ := H_le_J A cm fm V b' σ₀
  have hJσpos : 0 < J A cm fm b' σ := by rw [hJeq]; linarith [hgH0]
  -- `Phon_{σ₀} = H_{σ₀}/J_{σ₀} ≤ H_σ/J_σ = Phon_σ`.
  change H A cm fm V b' σ₀ / J A cm fm b' σ₀ ≤ H A cm fm V b' σ / J A cm fm b' σ
  rw [div_le_div_iff₀ hJpos hJσpos, hJeq]
  -- `H_{σ₀}·(J_{σ₀} + gH) ≤ H_σ·J_{σ₀}`, using `H_σ ≥ H_{σ₀} + gH` and `H_{σ₀} ≤ J_{σ₀}`.
  nlinarith [hHgrow, hHJ0, hgH0, hJpos.le]

end FastConfirmation.LMDGhost

/-!
# LMDGhost / Proof / Propagation

Lemma 5 (delivery half): if some honest validator has cast a GHOST vote for a
descendant of `b` in a slot `≤ slot(t)-1` (the witness), then `b` is in every
honest view by `st(slot(t))`. Pure gossip/delivery: `honestVoteUbiq` delivers the
vote, `votesCarryBlocks` carries its block, `blocksAncestorClosed` yields `b`
itself. The witness is supplied later by the canonicality/safety argument.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- A block supported by a delivered honest vote is in every honest view by the
    next slot boundary (Lemma 5, delivery form). -/
theorem safe_in_every_view' (τ : Timing) (fm : FaultModel n) {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) {b : Block n} {t : Time}
    (hslot : 1 ≤ τ.slotOf t) (hgst : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hwitness : ∃ i ∈ fm.honest, ∃ m : Message n P,
       HonestCast fm 𝒱 τ m ∧ m.ghost.slot ≤ τ.slotOf t - 1 ∧ b ≼ m.ghost.block) :
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → b ∈ (𝒱 w (τ.st (τ.slotOf t))).blocks := by
  obtain ⟨_, _, m, hcast, hmslot, hmb⟩ := hwitness
  intro w hw
  have hk : τ.slotOf t - 1 + 1 = τ.slotOf t := Nat.sub_add_cancel hslot
  -- delivery is gated on slot `slotOf t - 1` (the witness slot) being post-`gst`, and
  -- lands by `st(slotOf t - 1 + 1) = st(slotOf t)`.
  have hdeliv := hSync.honestVoteUbiq hw hcast hmslot hgst
  rw [hk] at hdeliv
  exact hSync.blocksAncestorClosed (hSync.votesCarryBlocks hdeliv) hmb

end FastConfirmation.LMDGhost

/-!
# LMDGhost / Proof / HeadSafety

Lemma 6 — the head-safety / future-agreement engine, the keystone of §3.1. It is
a strong induction on the cutoff slot `σ` that maintains, for every non-genesis
ancestor `b'` of the safe block `b`, the honest LMD-GHOST safety indicator
`Phon_{b',σ} ≥ Phon_{b',σ_base}` in every honest view past the delivery deadline,
and converts it to the absolute margin `H_{b',σ} > (W_{b',σ} + W_p)/2` only where
GHOST canonicality (Lemma 2) consumes it. The base case is the confirmation
hypothesis (Lemmas 3–4 via `P_base_of_Q`). The step combines:

* `honest_vote_is_head` + the inductive head-safety (IH) ⇒ every honest vote of
  slot `≥ slotOf t` supports `b'` (canonicality, Lemma 2 reused);
* hence base supporters persist and new honest committee members support `b'`;
* `P_nondecreasing` (Lemma 1) then transfers the **P-bound** to the larger cutoff,
  needing only `H ≤ J` (no adversarial-growth premise);
* the monotone `Wp/W` step (the threshold ratio shrinks as `W` grows) plus
  `Hmargin_of_P` (Lemma 3, Assumption 2) re-derive the absolute margin.

`head_of_Hmajority_filtered` (Lemma 2) turns the resulting margin into
`b ≼ forkChoiceHead` for every honest view.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

section Engine

variable {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight}
  {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
  {flt : BlockFilter n P} {𝒱 : ViewFamily n P} {C : Anchor n}

/-- If an honest validator's effective vote at cutoff `σ` lies at a slot `≥ slotOf t`
    where head-safety already holds, then that vote supports every ancestor `b'` of `b`.
    (`honest_vote_is_head` + the head-safety hypothesis at the vote's own slot.) -/
theorem effHigh_supports
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {st0 σ : Slot}
    (hgstlow : τ.AfterGST (τ.st st0))
    -- head-safety at every honest view for vote-slots in `[st0, σ]`:
    (hHead : ∀ ⦃k : Slot⦄, st0 ≤ k → k ≤ σ → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i (τ.st k)) boost pb flt (𝒱 i (τ.st k)) (τ.st k))
    {w : Validator n} {t' : Time} {i : Validator n} {gv : GhostVote n}
    (hw : w ∈ fm.honest) (hi : i ∈ fm.honest)
    (hev : (𝒱 w t').effectiveVote i σ = some gv) (hslot : st0 ≤ gv.slot) :
    (𝒱 w t').supportsLMD b' i σ = true := by
  -- The effective vote is the latest vote, so it is a genuine vote of `i`.
  rw [effectiveVote_eq_latest (hHB.noEquivocation hi (w := w) (t := t'))] at hev
  obtain ⟨hmem, hgvσ⟩ := latestVote_some_mem hev
  have hgstk : τ.AfterGST (τ.st gv.slot) := by
    unfold Timing.AfterGST at hgstlow ⊢
    refine le_trans hgstlow ?_
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur hslot
  have hblock := honest_vote_is_head hSync hNF hHB hi hw hmem hgstk
  have hbge : b ≼ gv.block := by rw [hblock]; exact hHead hslot hgvσ hi
  have hb'ge : b' ≼ gv.block := Block.Ancestor.trans hb'b hbge
  unfold View.supportsLMD
  rw [effectiveVote_eq_latest (hHB.noEquivocation hi (w := w) (t := t')), hev]
  exact isAncestorOf_of_ancestor hb'ge

/-- A growth-set committee member belongs to a committee of a slot strictly above `σ₀`. -/
theorem growth_mem_high {b' : Block n} {σ₀ σ : Slot} {i : Validator n}
    (hi : i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀) :
    ∃ k, b'.psPlus1 ≤ k ∧ k ≤ σ ∧ σ₀ < k ∧ i ∈ cm.member k := by
  rw [Finset.mem_sdiff, committeeUnion, Finset.mem_biUnion] at hi
  obtain ⟨⟨k, hk, hik⟩, hnot⟩ := hi
  rw [Finset.mem_Icc] at hk
  refine ⟨k, hk.1, hk.2, ?_, hik⟩
  by_contra hle
  push Not at hle
  exact hnot (by
    rw [committeeUnion, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_Icc.mpr ⟨hk.1, hle⟩, hik⟩)

/-- **Canonicality of new committee members.** A new honest committee member supports
    every ancestor `b'` of `b` at the larger cutoff, because it votes at a slot
    `≥ slotOf t` (where head-safety already holds). -/
theorem canon_support
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {st0 σ : Slot}
    (hgstlow : τ.AfterGST (τ.st st0))
    (hHead : ∀ ⦃k : Slot⦄, st0 ≤ k → k ≤ σ → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i (τ.st k)) boost pb flt (𝒱 i (τ.st k)) (τ.st k))
    {w : Validator n} {t' : Time} {i : Validator n} {σ₀ : Slot}
    (hw : w ∈ fm.honest) (hi : i ∈ fm.honest)
    (hst0 : σ₀ + 1 = st0) (hdeliv : τ.st (σ + 1) ≤ t')
    (hmem : i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀) :
    (𝒱 w t').supportsLMD b' i σ = true := by
  obtain ⟨k, _, hkσ, hk0, hik⟩ := growth_mem_high (b' := b') hmem
  have hk_st0 : st0 ≤ k := by rw [← hst0]; exact hk0
  -- `i` votes at slot `k`.
  obtain ⟨gv0, hgv0mem, hgv0slot, _⟩ := hHB.votesHead hi hik
  -- deliver to `𝒱 w t'`.
  have hgst_k : τ.AfterGST (τ.st k) := by
    unfold Timing.AfterGST at hgstlow ⊢
    refine le_trans hgstlow ?_
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur hk_st0
  have hge : τ.st (k + 1) ≤ t' := by
    refine le_trans ?_ hdeliv
    have : k + 1 ≤ σ + 1 := Nat.add_le_add_right hkσ 1
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur this
  have hkσ' : gv0.slot ≤ σ := by rw [hgv0slot]; exact hkσ
  have hgst_gv0 : τ.AfterGST (τ.st gv0.slot) := by rw [hgv0slot]; exact hgst_k
  have hge_gv0 : τ.st (gv0.slot + 1) ≤ t' := by rw [hgv0slot]; exact hge
  have hgv0w : gv0 ∈ (𝒱 w t').votesOf i :=
    honest_vote_ubiquitous hSync hNF hi hi hgv0mem hw (le_refl gv0.slot) hge_gv0 hgst_gv0
  -- the latest vote at cutoff σ exists and is at a slot ≥ k ≥ st0.
  have hsome : ((𝒱 w t').latestVote i σ).isSome := latestVote_isSome hgv0w hkσ'
  obtain ⟨gv1, hgv1⟩ := Option.isSome_iff_exists.mp hsome
  have hev : (𝒱 w t').effectiveVote i σ = some gv1 := by
    rw [effectiveVote_eq_latest (hHB.noEquivocation hi (w := w) (t := t')), hgv1]
  have hgv1ge : gv0.slot ≤ gv1.slot :=
    latestVote_is_max hgv1 hgv0w hkσ'
  have hgv1_st0 : st0 ≤ gv1.slot :=
    le_trans hk_st0 (le_trans (le_of_eq hgv0slot.symm) hgv1ge)
  exact effHigh_supports hSync hNF hHB hb'b hgstlow hHead hw hi hev hgv1_st0

/-- **Persistence.** A base honest supporter (at cutoff `σ₀ = st0 - 1`) still supports
    `b'` at the larger cutoff `σ`: its effective vote at `σ` either equals the base one
    (still supports) or is a strictly newer vote, hence at a slot `≥ st0` where
    head-safety holds (`effHigh_supports`). -/
theorem persist_support
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {st0 σ : Slot}
    (hgstlow : τ.AfterGST (τ.st st0))
    (hHead : ∀ ⦃k : Slot⦄, st0 ≤ k → k ≤ σ → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i (τ.st k)) boost pb flt (𝒱 i (τ.st k)) (τ.st k))
    {w : Validator n} {t' : Time} {i : Validator n} {σ₀ : Slot}
    (hw : w ∈ fm.honest) (hi : i ∈ fm.honest)
    (hst0 : σ₀ + 1 = st0) (hσ : σ₀ ≤ σ)
    (hbase : (𝒱 w t').supportsLMD b' i σ₀ = true) :
    (𝒱 w t').supportsLMD b' i σ = true := by
  have hne := hHB.noEquivocation hi (w := w) (t := t')
  -- The base support comes from an effective (= latest) vote at cutoff σ₀.
  have hbase' : ∃ gv0, (𝒱 w t').effectiveVote i σ₀ = some gv0 ∧
      b'.isAncestorOf gv0.block = true := by
    unfold View.supportsLMD at hbase
    cases hev0 : (𝒱 w t').effectiveVote i σ₀ with
    | none => rw [hev0] at hbase; simp at hbase
    | some gv0 => rw [hev0] at hbase; exact ⟨gv0, rfl, hbase⟩
  obtain ⟨gv0, hev0, hsupp0⟩ := hbase'
  obtain ⟨hgv0mem, hgv0σ₀⟩ := effectiveVote_some_mem hev0
  have hgv0σ : gv0.slot ≤ σ := le_trans hgv0σ₀ hσ
  -- At cutoff σ the latest vote exists.
  have hsome : ((𝒱 w t').latestVote i σ).isSome := latestVote_isSome hgv0mem hgv0σ
  obtain ⟨gv1, hgv1⟩ := Option.isSome_iff_exists.mp hsome
  have hev1 : (𝒱 w t').effectiveVote i σ = some gv1 := by
    rw [effectiveVote_eq_latest hne, hgv1]
  have hge : gv0.slot ≤ gv1.slot := latestVote_is_max hgv1 hgv0mem hgv0σ
  rcases Nat.lt_or_ge gv1.slot st0 with hlt | hge0
  · -- gv1.slot < st0 = σ₀+1, so gv1.slot ≤ σ₀; gv1 and gv0 are both latest at σ₀, hence equal.
    have hgv1σ₀ : gv1.slot ≤ σ₀ := by rw [← hst0] at hlt; exact Nat.lt_succ_iff.mp hlt
    obtain ⟨hgv1mem, _⟩ := latestVote_some_mem hgv1
    have hlat0 : (𝒱 w t').latestVote i σ₀ = some gv0 := by
      rw [← effectiveVote_eq_latest hne]; exact hev0
    have hmax0 : gv1.slot ≤ gv0.slot := latestVote_is_max hlat0 hgv1mem hgv1σ₀
    have hseq : gv0.slot = gv1.slot := le_antisymm hge hmax0
    have heq : gv1 = gv0 := noEquiv_unique_slot hne hgv1mem hgv0mem hseq.symm
    unfold View.supportsLMD; rw [hev1, heq]; exact hsupp0
  · -- gv1.slot ≥ st0: a newer vote at a slot where head-safety holds.
    exact effHigh_supports hSync hNF hHB hb'b hgstlow hHead hw hi hev1 hge0

/-- **`P` maintenance (the Lemma 1 + Lemma 2 fusion).** Given the base honest committee
    weight `J_{b',σ₀} > 0` in view `(𝒱 w t')`, head-safety at every honest view for slots
    `≥ st0`, the honest LMD-GHOST safety indicator `Phon` is non-decreasing from cutoff
    `σ₀ = st0 - 1` to any `σ ≥ σ₀`. No honest-growth premise — `P_nondecreasing` needs only
    `H ≤ J`. The `hJpos` side-condition is threaded from the BASE cutoff. -/
theorem P_maintained
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {st0 : Slot} {σ₀ : Slot} (hst0 : σ₀ + 1 = st0)
    (hgstlow : τ.AfterGST (τ.st st0))
    {σ : Slot}
    (hHead : ∀ ⦃k : Slot⦄, st0 ≤ k → k ≤ σ → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i (τ.st k)) boost pb flt (𝒱 i (τ.st k)) (τ.st k))
    {w : Validator n} {t' : Time} (hw : w ∈ fm.honest)
    (hdeliv : τ.st (σ + 1) ≤ t')
    (hσ : σ₀ ≤ σ)
    (hJpos : 0 < J C cm fm b' σ₀) :
    Phon C cm fm (𝒱 w t') b' σ₀ ≤ Phon C cm fm (𝒱 w t') b' σ := by
  refine P_nondecreasing C cm fm (𝒱 w t') b' hσ hJpos ?_ ?_
  · -- persistence of base supporters
    intro i _ hih hsup
    exact persist_support hSync hNF hHB hb'b hgstlow hHead hw hih hst0 hσ hsup
  · -- canonicality of new committee members
    intro i hi hih
    exact canon_support hSync hNF hHB hb'b hgstlow hHead hw hih hst0 hdeliv hi

/-- A positive honest support weight produces an honest supporter (balances are
    positive, so the honest-supporter set is nonempty). -/
theorem honest_supporter_of_H_pos {V : View n P} {b' : Block n} {σ : Slot}
    (hpos : 0 < H C cm fm V b' σ) :
    ∃ i, i ∈ fm.honest ∧ V.supportsLMD b' i σ = true := by
  by_contra hcon
  push Not at hcon
  have hempty : (committeeUnion cm b'.psPlus1 σ).filter
      (fun i => i ∈ fm.honest ∧ V.supportsLMD b' i σ = true) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    rintro ⟨hih, hsup⟩
    exact absurd hsup (hcon i hih)
  rw [H, hempty] at hpos
  simp only [totalWeight, Finset.sum_empty, lt_irrefl] at hpos

/-- A supporter's effective vote names a descendant of `b'`, and that vote (cast by
    an honest validator, hence `HonestCast` by no-forgery) witnesses delivery of `b'`. -/
theorem witness_of_honest_supporter
    (hNF : HonestNoForgery fm τ 𝒱)
    {b' : Block n} {σ : Slot} {w : Validator n} {t' : Time} {i : Validator n}
    (hw : w ∈ fm.honest) (hi : i ∈ fm.honest)
    (hsup : (𝒱 w t').supportsLMD b' i σ = true) :
    ∃ m : Message n P, HonestCast fm 𝒱 τ m ∧ m.ghost.slot ≤ σ ∧ b' ≼ m.ghost.block := by
  unfold View.supportsLMD at hsup
  cases hev : (𝒱 w t').effectiveVote i σ with
  | none => rw [hev] at hsup; simp at hsup
  | some gv =>
    rw [hev] at hsup
    obtain ⟨hmem, hslot⟩ := effectiveVote_some_mem hev
    simp only [View.votesOf, Finset.mem_filter] at hmem
    obtain ⟨m, hmmsg, _hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hmem.1
    have hval : m.ghost.validator ∈ fm.honest := by rw [hmg, hmem.2]; exact hi
    refine ⟨m, hNF hw hmmsg hval, ?_, ?_⟩
    · rw [hmg]; exact hslot
    · rw [hmg]; exact isAncestorOf_imp hsup

/-- **Base P-bound, transferred to any honest view.** From the confirmation hypothesis
    (`isLMDGHOSTSafe` in `v`'s view at `t`), every non-genesis ancestor `b'` of `b` has
    the P-lower-bound `Phon_{b',slotOf t - 1} > (1/(2(1−β)))(1 + Wp/W_{b',slotOf t - 1})`
    in *every* honest view past the delivery deadline `st(slotOf t)`. The Q-threshold gives
    the P-bound in `v`'s view (`P_base_of_Q`, Lemma 4); view-independence of the numerator
    `H` (post-GST) transfers it, with the denominator `J` literally view-free. -/
theorem base_P
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hcm : CommitteeHonestMajority fm cm C)
    {v : Validator n} {b : Block n} {t : Time} (hv : v ∈ fm.honest)
    (h1 : 1 ≤ τ.slotOf t) (hgst0 : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t)
    {w : Validator n} {t' : Time} (hw : w ∈ fm.honest) (ht' : τ.st (τ.slotOf t) ≤ t')
    {b' : Block n} (hb'b : b' ≼ b) (hb'ne : b' ≠ Block.genesis) :
    Phon C cm fm (𝒱 w t') b' (τ.slotOf t - 1) >
      (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' (τ.slotOf t - 1)) := by
  -- one-confirmed in v's own view ⇒ the Q-threshold ⇒ the P-bound there
  have h1c : isOneConfirmed τ fm cm pb C (𝒱 v t) b' t := (hsafe hb'b).resolve_left hb'ne
  have hQ : Q C cm (𝒱 v t) b' (τ.slotOf t - 1) >
      (1 / 2) * (1 + Wp C pb / W C cm b' (τ.slotOf t - 1)) + fm.β := by
    unfold isOneConfirmed safetyThreshold at h1c; exact h1c
  have hW := W_pos_of_Q_threshold C cm fm (𝒱 v t) b' (τ.slotOf t - 1) pb hQ
  have hPv := P_base_of_Q C cm fm (𝒱 v t) b' (τ.slotOf t - 1) pb hcm hW hQ
  -- view-independence transfers the numerator `H` to `(𝒱 w t')`; `J` is view-free.
  have hgstd : τ.AfterGST (τ.st (τ.slotOf t - 1)) := hgst0
  have htv : τ.st (τ.slotOf t - 1 + 1) ≤ t := by
    rw [Nat.sub_add_cancel h1]
    calc τ.st (τ.slotOf t) = τ.slotOf t * τ.slotDur := rfl
      _ ≤ t := by
          simpa [Timing.slotOf] using Nat.div_mul_le_self t τ.slotDur
  have htw : τ.st (τ.slotOf t - 1 + 1) ≤ t' := by rw [Nat.sub_add_cancel h1]; exact ht'
  have hHeq := H_view_indep C hSync hNF hHB (b' := b') (σ := τ.slotOf t - 1)
    hgstd hw htw hv htv
  -- `Phon C cm fm (𝒱 w t') b' σ = H (𝒱 w t') / J = H (𝒱 v t) / J = Phon C cm fm (𝒱 v t) b' σ`.
  have hPeq : Phon C cm fm (𝒱 w t') b' (τ.slotOf t - 1)
      = Phon C cm fm (𝒱 v t) b' (τ.slotOf t - 1) := by
    change H C cm fm (𝒱 w t') b' (τ.slotOf t - 1) / J C cm fm b' (τ.slotOf t - 1)
      = H C cm fm (𝒱 v t) b' (τ.slotOf t - 1) / J C cm fm b' (τ.slotOf t - 1)
    rw [hHeq]
  rw [hPeq]; exact hPv

/-- **Absolute honest margin maintained (the full Lemma 1 + 3 + 4 + 6 composition).**
    For a non-genesis ancestor `b'` of `b`, with `σ_base := slotOf t - 1` and any cutoff
    `σ ≥ σ_base` reachable from the engine, the absolute honest margin
    `H_{b',σ} > (W_{b',σ} + W_p)/2` holds in `(𝒱 w t')`. Composition:
    `base_P` (Q ⇒ P-bound at `σ_base`) ⟹ `P_maintained` (P non-decreasing to `σ`) ⟹ the
    monotone `Wp/W` step (`W` grows ⟹ the threshold ratio shrinks) ⟹ `Hmargin_of_P`
    (Assumption 2 conversion). The `(1−β)` cancellation lives in `Hmargin_of_P`. -/
theorem margin_maintained
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hcm : CommitteeHonestMajority fm cm C) (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} {t : Time} (hv : v ∈ fm.honest)
    (h1 : 1 ≤ τ.slotOf t) (hgst0 : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t)
    {w : Validator n} {t' : Time} (hw : w ∈ fm.honest)
    {σ : Slot}
    (hHead : ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k → k ≤ σ → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i (τ.st k)) boost pb flt (𝒱 i (τ.st k)) (τ.st k))
    (hdeliv : τ.st (σ + 1) ≤ t')
    (hσ : τ.slotOf t - 1 ≤ σ)
    {b' : Block n} (hb'b : b' ≼ b) (hb'ne : b' ≠ Block.genesis) :
    H C cm fm (𝒱 w t') b' σ > (W C cm b' σ + Wp C pb) / 2 := by
  set σ₀ := τ.slotOf t - 1 with hσ₀
  have hβ1 : (0 : Weight) < 1 - fm.β := by have := fm.hβ; linarith
  -- 1. base P-bound at `σ₀` in `(𝒱 w t')`.
  have ht' : τ.st (τ.slotOf t) ≤ t' := by
    refine le_trans ?_ hdeliv
    have : τ.slotOf t ≤ σ + 1 := by
      calc τ.slotOf t = σ₀ + 1 := by rw [hσ₀, Nat.sub_add_cancel h1]
        _ ≤ σ + 1 := Nat.add_le_add_right hσ 1
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur this
  have hbaseP := base_P hSync hNF hHB hcm hv h1 hgst0 hsafe hw ht' hb'b hb'ne
  rw [← hσ₀] at hbaseP
  -- `Phon σ₀ > P_base(σ₀) > 0`, so `J σ₀ > 0`.
  have hWpos0 : 0 < W C cm b' σ₀ := by
    -- from the Q-threshold (via `base_P`'s internal `W_pos_of_Q_threshold`)
    have h1c : isOneConfirmed τ fm cm pb C (𝒱 v t) b' t := (hsafe hb'b).resolve_left hb'ne
    have hQ : Q C cm (𝒱 v t) b' σ₀ > (1 / 2) * (1 + Wp C pb / W C cm b' σ₀) + fm.β := by
      unfold isOneConfirmed safetyThreshold at h1c; rw [← hσ₀] at h1c; exact h1c
    exact W_pos_of_Q_threshold C cm fm (𝒱 v t) b' σ₀ pb hQ
  have hPbase0_pos : (0 : Weight) < (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ₀) := by
    have hWpnn : 0 ≤ Wp C pb := mul_nonneg hpb (totalWeight_nonneg C _)
    have : 0 ≤ Wp C pb / W C cm b' σ₀ := div_nonneg hWpnn (le_of_lt hWpos0)
    positivity
  have hPhon0_pos : 0 < Phon C cm fm (𝒱 w t') b' σ₀ := lt_trans hPbase0_pos hbaseP
  have hJpos0 : 0 < J C cm fm b' σ₀ := by
    by_contra hle
    push Not at hle
    have hJ0 : J C cm fm b' σ₀ = 0 := le_antisymm hle (totalWeight_nonneg C _)
    rw [show Phon C cm fm (𝒱 w t') b' σ₀ = H C cm fm (𝒱 w t') b' σ₀ / J C cm fm b' σ₀ from rfl,
      hJ0, div_zero] at hPhon0_pos
    exact lt_irrefl 0 hPhon0_pos
  -- 2. `P_maintained`: `Phon σ₀ ≤ Phon σ`.
  -- `P_maintained` operates from `st0 := slotOf t` (new committee members at slots `≥ slotOf t`),
  -- so it needs the *weaker* `AfterGST(st(slotOf t))`, derived from the base
  -- `AfterGST(st(slotOf t-1))`.
  have hgst0t : τ.AfterGST (τ.st (τ.slotOf t)) := by
    unfold Timing.AfterGST at hgst0 ⊢
    refine le_trans hgst0 ?_
    exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le (τ.slotOf t) 1)
  have hPmono := P_maintained hSync hNF hHB hb'b (st0 := τ.slotOf t)
    (Nat.sub_add_cancel h1) hgst0t (σ := σ)
    (fun {k} hk1 hk2 {i} hi => hHead hk1 hk2 hi)
    hw hdeliv hσ hJpos0
  -- 3. monotone `Wp/W` step: `P_base(σ₀) ≥ P_base(σ)` since `W σ ≥ W σ₀`.
  have hWmono : W C cm b' σ₀ ≤ W C cm b' σ :=
    W_le_of_slot_le C cm b' hσ
  have hWpnn : 0 ≤ Wp C pb := mul_nonneg hpb (totalWeight_nonneg C _)
  have hWdiv : Wp C pb / W C cm b' σ ≤ Wp C pb / W C cm b' σ₀ :=
    div_le_div_of_nonneg_left hWpnn hWpos0 hWmono
  have hthr_mono : (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ)
      ≤ (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ₀) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hWdiv]
  -- 4. `Phon σ > P_base(σ)`, then `Hmargin_of_P`.
  have hPσ : Phon C cm fm (𝒱 w t') b' σ >
      (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ) := by
    calc (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ)
        ≤ (1 / (2 * (1 - fm.β))) * (1 + Wp C pb / W C cm b' σ₀) := hthr_mono
      _ < Phon C cm fm (𝒱 w t') b' σ₀ := hbaseP
      _ ≤ Phon C cm fm (𝒱 w t') b' σ := hPmono
  exact Hmargin_of_P C cm fm (𝒱 w t') b' σ pb hcm hpb hPσ

/-- The non-genesis safe block `b` is present (with its whole prefix) in every honest
    view from `st(slotOf t)` onward, at any time `t' ≥ st(slotOf t)`. (Lemma 5: the base
    majority produces an honest supporter whose vote witnesses delivery via
    `safe_in_every_view'`; monotone views + ancestor-closure carry it forward to later
    times and to all prefixes.) -/
theorem chain_in_view
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hcm : CommitteeHonestMajority fm cm C) (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} {t : Time} (hv : v ∈ fm.honest)
    (h1 : 1 ≤ τ.slotOf t) (hgst0 : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hbne : b ≠ Block.genesis)
    (hsafe : isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t)
    {i : Validator n} {t' : Time} (hi : i ∈ fm.honest) (ht' : τ.st (τ.slotOf t) ≤ t')
    {b'' : Block n} (hb''b : b'' ≼ b) :
    b'' ∈ (𝒱 i t').blocks := by
  -- A witness honest supporter of `b` at cutoff `slotOf t - 1` (the base majority is `> 0`).
  -- Use the absolute honest margin directly (kept for positivity) and transfer the
  -- numerator `H` to the honest view `(𝒱 v (st(slotOf t)))` via view-independence.
  have h1c : isOneConfirmed τ fm cm pb C (𝒱 v t) b t :=
    (hsafe (Block.Ancestor.refl b)).resolve_left hbne
  have hmajv := Hmaj_of_isOneConfirmed τ C cm fm pb (𝒱 v t) b t hcm h1c
  have hgstd : τ.AfterGST (τ.st (τ.slotOf t - 1)) := hgst0
  have htv : τ.st (τ.slotOf t - 1 + 1) ≤ t := by
    rw [Nat.sub_add_cancel h1]
    calc τ.st (τ.slotOf t) = τ.slotOf t * τ.slotDur := rfl
      _ ≤ t := by simpa [Timing.slotOf] using Nat.div_mul_le_self t τ.slotDur
  have htw : τ.st (τ.slotOf t - 1 + 1) ≤ τ.st (τ.slotOf t) := by
    rw [Nat.sub_add_cancel h1]
  have hHeq := H_view_indep C hSync hNF hHB (b' := b) (σ := τ.slotOf t - 1)
    hgstd hv htw hv htv
  have hmaj : H C cm fm (𝒱 v (τ.st (τ.slotOf t))) b (τ.slotOf t - 1) >
      (W C cm b (τ.slotOf t - 1) + Wp C pb) / 2 := by rw [hHeq]; exact hmajv
  have hWnn : 0 ≤ W C cm b (τ.slotOf t - 1) := totalWeight_nonneg C _
  have hWpnn : 0 ≤ Wp C pb := mul_nonneg hpb (totalWeight_nonneg C _)
  have hHpos : 0 < H C cm fm (𝒱 v (τ.st (τ.slotOf t))) b (τ.slotOf t - 1) := by
    have hhalf : (0 : Weight) ≤ (W C cm b (τ.slotOf t - 1) + Wp C pb) / 2 := by
      have := add_nonneg hWnn hWpnn; linarith
    linarith [hmaj, hhalf]
  obtain ⟨i0, hi0, hsup0⟩ := honest_supporter_of_H_pos hHpos
  obtain ⟨m, hcast, hmslot, hmb⟩ := witness_of_honest_supporter hNF hv hi0 hsup0
  -- `b` is in every honest view by `st(slotOf t)` (Lemma 5).
  have hb_in : b ∈ (𝒱 i (τ.st (τ.slotOf t))).blocks := by
    refine safe_in_every_view' τ fm hSync h1 hgst0 ⟨i0, hi0, m, hcast, hmslot, hmb⟩ hi
  -- monotone views carry it to `t'`.
  have hb_ink : b ∈ (𝒱 i t').blocks := (hSync.monotone i _ _ ht').2 hb_in
  exact hSync.blocksAncestorClosed hb_ink hb''b

/-- **`AnchorsCoincide` is the §3.1 specialization of Lemma 6 hypothesis (4).** Under
    `StaticBalances` (Assumption 1 — every `gj`-anchor assigns the same balance to each
    validator), choosing the engine anchor `C := gj 𝒱 v t` makes *every* honest voter's
    own `gj`-anchor (read at any slot boundary) coincide with `C`: two anchors are equal
    as soon as their `.bal` fields agree (`Stakes` is a balance source; its positivity
    field is a proof, hence proof-irrelevant). This is exactly the operative use of
    `StaticBalances` in the engine — it pins honest fork-choice anchors to `C`. -/
theorem AnchorsCoincide_of_StaticBalances {gj : ViewFamily n P → Validator n → Time → Anchor n}
    {𝒱 : ViewFamily n P} (fm : FaultModel n) (τ : Timing)
    {v : Validator n} {t : Time} (hsb : StaticBalances gj 𝒱) :
    AnchorsCoincide gj 𝒱 fm τ (gj 𝒱 v t) := by
  intro j _ kk
  -- Two `Stakes` are equal once their `.bal` fields agree (the `.hpos` field is a
  -- proof, hence proof-irrelevant). `StaticBalances` gives exactly the `.bal` equality.
  have hbal : (gj 𝒱 j (τ.st kk)).bal = (gj 𝒱 v t).bal := by
    funext i; exact hsb j (τ.st kk) v t i
  cases hA : gj 𝒱 j (τ.st kk) with
  | mk b1 h1 =>
    cases hB : gj 𝒱 v t with
    | mk b2 h2 =>
      rw [hA, hB] at hbal
      simp only at hbal
      subst hbal
      rfl

/-- **The slot-aligned head-safety induction (Lemma 6 core).** By strong induction on
    the cutoff slot `k`, for every honest validator `i` and every `k ≥ slotOf t`, the
    safe block `b` is on `i`'s LMD-GHOST head computed at `st k`. The inductive step
    re-establishes the per-ancestor honest margin at cutoff `k-1` (via `margin_maintained`,
    composing the P-bound base + `P_nondecreasing` + the monotone `Wp/W` step + the
    Assumption-2 conversion; its head-safety premise for vote-slots `≤ k-1` is supplied by
    the IH, re-anchored to `C` via `AnchorsCoincide`), then applies
    `head_of_Hmajority_filtered`. -/
theorem head_safety_at_slot
    {v : Validator n} {b : Block n} {t : Time}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hVV : ViewsValid cm 𝒱) (hcm : CommitteeHonestMajority fm cm C) (hpb : 0 ≤ pb)
    (hAnchor : AnchorsCoincide gj 𝒱 fm τ C)
    (hv : v ∈ fm.honest)
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ τ.slotOf t)
    (h1 : 1 ≤ τ.slotOf t) (hgst0 : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t)
    (hNFilOfHead : ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k →
      (∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j)) →
      ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.slotOf t' = k →
        τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b') :
    ∀ (k : Slot), τ.slotOf t ≤ k → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ C boost pb flt (𝒱 i (τ.st k)) (τ.st k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk i hi
    -- genesis is trivial
    by_cases hbne : b = Block.genesis
    · rw [hbne]; exact genesis_ancestor _
    -- `slotOf (st k) = k`, so the cutoff is `k - 1`.
    set V := 𝒱 i (τ.st k) with hV
    have hslotk : τ.slotOf (τ.st k) = k := Timing.slotOf_st τ k
    have hkge1 : 1 ≤ k := le_trans h1 hk
    -- the IH gives head-safety for vote-slots `j ∈ [slotOf t, k-1]` (note `j < k`).
    have hHead : ∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j ≤ k - 1 → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j) := by
      intro j hj1 hj2 i' hi'
      have hjk : j < k := lt_of_le_of_lt hj2 (Nat.sub_lt hkge1 Nat.one_pos)
      -- The IH gives head-safety under the engine anchor `C`; honest voters compute their
      -- head under their own `gj`-anchor, which `AnchorsCoincide` pins to `C`.
      rw [hAnchor hi' j]
      exact IH j hjk hj1 hi'
    -- per-ancestor honest margin at cutoff `k-1` in view `V`.
    have hmaj : ∀ ⦃b' : Block n⦄, b' ≼ b → b' ≠ Block.genesis →
        H C cm fm V b' (τ.slotOf (τ.st k) - 1) >
          (W C cm b' (τ.slotOf (τ.st k) - 1) + Wp C pb) / 2 := by
      intro b' hb'b hb'ne
      rw [hslotk]
      have hσ : τ.slotOf t - 1 ≤ k - 1 := Nat.sub_le_sub_right hk 1
      have hdeliv : τ.st (k - 1 + 1) ≤ τ.st k := by
        rw [Nat.sub_add_cancel hkge1]
      exact margin_maintained hSync hNF hHB hcm hpb hv h1 hgst0 hsafe hi
        (σ := k - 1)
        (fun {j} hj1 hj2 {i'} hi' => hHead hj1 hj2 hi')
        hdeliv hσ hb'b hb'ne
    -- chain-in-view, filter-eligibility, slot bound.
    have hstk : τ.st (τ.slotOf t) ≤ τ.st k := by
      exact_mod_cast Nat.mul_le_mul_right τ.slotDur hk
    have hchain : ∀ ⦃b'' : Block n⦄, b'' ≼ b → b'' ∈ V.blocks :=
      fun b'' hb''b => chain_in_view hSync hNF hHB hcm hpb hv h1 hgst0 hbne hsafe hi hstk hb''b
    -- The IH-built `hHead` (head-safety at vote-slots `j ≤ k-1 ⟺ j < k`) discharges the
    -- filter-eligibility premise via the `hNFilOfHead` functional, at cutoff `k`, time `st k`.
    have hHeadlt : ∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j) :=
      fun j hj1 hjk i' hi' => hHead hj1 (Nat.le_sub_one_of_lt hjk) hi'
    have hflt : ∀ ⦃b'' : Block n⦄, b'' ≼ b → flt V (τ.st k) b'' :=
      fun b'' hb''b => hNFilOfHead hk hHeadlt hi hslotk hstk hb''b
    have hslot : b.slot ≤ τ.slotOf (τ.st k) := by rw [hslotk]; exact le_trans hbslot hk
    exact head_of_Hmajority_filtered τ C cm fm pb boost flt V (τ.st k) hpb (hVV i (τ.st k))
      hbwf hchain hslot hflt hmaj

/-- **The arbitrary-time head-safety engine (Lemma 6).** Strengthens `head_safety_at_slot`
    from slot boundaries `st k` to *any* time `t'` with `st(slotOf t) ≤ t'`: for every
    honest validator `w`, the safe block `b` is on `w`'s LMD-GHOST head computed *at `t'`
    in `w`'s view `𝒱 w t'`*. `forkChoiceHead` is not view-monotone, so this genuinely reads
    `(𝒱 w t', t')` — the proof is a strong induction on the cutoff slot `k := slotOf t'`,
    whose predicate quantifies over all such times `s` at slot `k`. The inductive step still
    feeds the IH at slot boundaries `st j` (which is what `margin_maintained` consumes), then
    closes the goal at the actual time `t'` via the arbitrary-time `chain_in_view` and the
    delivery bound `st(slotOf t') ≤ t'`. -/
theorem head_safety_engine
    {v : Validator n} {b : Block n} {t : Time}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    (hVV : ViewsValid cm 𝒱) (hcm : CommitteeHonestMajority fm cm C) (hpb : 0 ≤ pb)
    (hAnchor : AnchorsCoincide gj 𝒱 fm τ C)
    (hv : v ∈ fm.honest)
    (hbwf : b.WellFormed) (hbslot : b.slot ≤ τ.slotOf t)
    (h1 : 1 ≤ τ.slotOf t) (hgst0 : τ.AfterGST (τ.st (τ.slotOf t - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t)
    (hNFilOfHead : ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k →
      (∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j)) →
      ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.slotOf t' = k →
        τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b') :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st (τ.slotOf t) ≤ t' →
      b ≼ forkChoiceHead τ C boost pb flt (𝒱 w t') t' := by
  -- Strong induction on the cutoff slot `k = slotOf t'`, quantifying over all witnessing
  -- times `s` at slot `k` with `st(slotOf t) ≤ s`.
  suffices H : ∀ (k : Slot), ∀ (s : Time), τ.slotOf s = k → τ.st (τ.slotOf t) ≤ s →
      ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
        b ≼ forkChoiceHead τ C boost pb flt (𝒱 i s) s by
    intro w t' hw ht'
    exact H (τ.slotOf t') t' rfl ht' hw
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro s hslots hst0s i hi
    -- `slotOf t ≤ k`, since `st(slotOf t) ≤ s` and `slotOf s = k`.
    have hk : τ.slotOf t ≤ k := by
      rw [← hslots]
      have := Timing.slotOf_st τ (τ.slotOf t)
      calc τ.slotOf t = τ.slotOf (τ.st (τ.slotOf t)) := (Timing.slotOf_st τ _).symm
        _ ≤ τ.slotOf s := Nat.div_le_div_right hst0s
    -- genesis is trivial
    by_cases hbne : b = Block.genesis
    · rw [hbne]; exact genesis_ancestor _
    set V := 𝒱 i s with hV
    have hkge1 : 1 ≤ k := le_trans h1 hk
    -- the IH gives head-safety for vote-slots `j ∈ [slotOf t, k-1]`, read at slot
    -- boundaries `st j` (which is what `margin_maintained` consumes).
    have hHead : ∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j ≤ k - 1 → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j) := by
      intro j hj1 hj2 i' hi'
      have hjk : j < k := lt_of_le_of_lt hj2 (Nat.sub_lt hkge1 Nat.one_pos)
      -- The IH gives head-safety under the engine anchor `C`; honest voters compute their
      -- head under their own `gj`-anchor, which `AnchorsCoincide` pins to `C`.
      rw [hAnchor hi' j]
      have hslotstj : τ.slotOf (τ.st j) = j := Timing.slotOf_st τ j
      have hst0stj : τ.st (τ.slotOf t) ≤ τ.st j := by
        exact_mod_cast Nat.mul_le_mul_right τ.slotDur hj1
      exact IH j hjk (τ.st j) hslotstj hst0stj hi'
    -- delivery bound `st k ≤ s` and base-time bound `st(slotOf t) ≤ s`.
    have hdelivs : τ.st k ≤ s := by rw [← hslots]; exact Timing.st_slotOf_le τ s
    -- per-ancestor honest margin at cutoff `k-1` in view `V = 𝒱 i s`.
    have hmaj : ∀ ⦃b' : Block n⦄, b' ≼ b → b' ≠ Block.genesis →
        H C cm fm V b' (τ.slotOf s - 1) >
          (W C cm b' (τ.slotOf s - 1) + Wp C pb) / 2 := by
      intro b' hb'b hb'ne
      rw [hslots]
      have hσ : τ.slotOf t - 1 ≤ k - 1 := Nat.sub_le_sub_right hk 1
      have hdeliv' : τ.st (k - 1 + 1) ≤ s := by rw [Nat.sub_add_cancel hkge1]; exact hdelivs
      exact margin_maintained hSync hNF hHB hcm hpb hv h1 hgst0 hsafe hi
        (σ := k - 1)
        (fun {j} hj1 hj2 {i'} hi' => hHead hj1 hj2 hi')
        hdeliv' hσ hb'b hb'ne
    -- chain-in-view, filter-eligibility, slot bound (all at the actual time `s`).
    have hchain : ∀ ⦃b'' : Block n⦄, b'' ≼ b → b'' ∈ V.blocks :=
      fun b'' hb''b => chain_in_view hSync hNF hHB hcm hpb hv h1 hgst0 hbne hsafe hi hst0s hb''b
    -- The IH-built `hHead` (head-safety at vote-slots `j ≤ k-1 ⟺ j < k`) discharges the
    -- filter-eligibility premise via the `hNFilOfHead` functional, at cutoff `k`, time `s`.
    have hHeadlt : ∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j) :=
      fun j hj1 hjk i' hi' => hHead hj1 (Nat.le_sub_one_of_lt hjk) hi'
    have hflt : ∀ ⦃b'' : Block n⦄, b'' ≼ b → flt V s b'' :=
      fun b'' hb''b => hNFilOfHead hk hHeadlt hi hslots hst0s hb''b
    have hslot : b.slot ≤ τ.slotOf s := by rw [hslots]; exact le_trans hbslot hk
    exact head_of_Hmajority_filtered τ C cm fm pb boost flt V s hpb (hVV i s)
      hbwf hchain hslot hflt hmaj

/-- **Static `NeverFiltered` ⇒ the head-safety functional.** A static, time-uniform
    `NeverFiltered … b t` hypothesis is, in particular, an `hNFilOfHead` functional:
    it already gives filter-eligibility at every honest view past the delivery deadline
    *unconditionally*, so the head-safety antecedent is simply ignored. This is the wrapper
    every §3.1/§4 caller that owns a static `NeverFiltered` plugs into the generalized
    engine, leaving its proof byte-for-byte unchanged. -/
theorem neverFiltered_to_hNFilOfHead {b : Block n} {t : Time}
    (hNFil : NeverFiltered τ fm flt 𝒱 b t) :
    ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k →
      (∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
        b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j)) →
      ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.slotOf t' = k →
        τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b' :=
  fun _k _hk _hHead _w hw _t' _ht'k hst0 _b' hb'b => hNFil hw hst0 hb'b

end Engine

end FastConfirmation.LMDGhost

end
