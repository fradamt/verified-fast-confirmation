module
public import FastConfirmationPaper.HFC.Proof.Justification
public import FastConfirmationPaper.HFC.Proof.SourceRecency
public import FastConfirmationPaper.HFC.Proof.CrossEpoch
public import FastConfirmationPaper.LMDGhost.Proof.BlockAncestry
public import FastConfirmationPaper.LMDGhost.Proof.FutureHeadAgreement
public import FastConfirmationPaper.LMDGhost.Proof.RuleSafety

@[expose] public section

/-!
# HFC / Proof / NeverFiltered

This module contains `keep_of_ancestor_GJ`, `votingSource_disjunct`, `GJ_le_or_ge_B'` and related declarations.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}


/-- **II.2 — D1 close.** If `B'` is an ancestor of the *realized* greatest-justified block
    (the filter's `gjC = greatestRealizedJustified bal₀ τ V t'`), the `ffgFilterAt` keep-disjunction
    holds by its first disjunct. -/
theorem keep_of_ancestor_GJ {τ : Timing} {bal₀ : Stakes n}
    {V : View n (FFGVote n)} {t' : Time} {B' : Block n}
    (hsel : FilterSelectorAgreementAt bal₀ τ V t')
    (h : B' ≼ (greatestRealizedJustified bal₀ τ V t').block) :
    ffgFilterAt bal₀ τ V t' B' :=
  Or.inl (by rw [hsel.1]; exact h)

/-- **II.4 — voting-source disjunct** (proven **structurally** — no recency/liveness premise; the
    proof-facing Def-2 epoch split). With `votingSource` chain-relative in both view-realized
    branches:
    * **same-epoch** (`epoch(b'') = epoch(t')`): the voting source is the chain-relative
      `gjblock(b'')` (`votingSource_eq_gjblock`, `rfl`). It equals `gjC` (the **left** disjunct) by
      the SAME realized-max + uniqueness pattern as the cross-epoch branch: same-epoch,
      `gjblock(b'')` is itself **realized** (`gjblock_realized`: epoch `< epoch(t')`), so
      `greatestRealizedJustified_max` gives `(gjblock b'').epoch ≤ gjC.epoch`; conversely `gjC` is
      justified, on `chain(b'')` (`hGJb''`) and epoch-cut, so `gjblock_max` gives `≥`; `le_antisymm`
      + `huniq` (accountable-safety justified-uniqueness) ⇒ `gjblock(b'') = gjC`. (Running epoch
      `0`: both genesis, taken via the trivially-true right disjunct.) **No recency premise.**
    * **different-epoch**: the voting source is the view-realized chain selector at `b''`. The
      on-chain placement `block(GJ_real) ≼ b''` (`hGJb''`) +
      `greatestJustifiedOfChain_ge_of_justified` give `(GJ_real).epoch ≤` that selector's epoch.
      Then either that selector is **realized**
      (`epoch < current`): `greatestRealizedJustified_max` forces
      its epoch to equal `(GJ_real).epoch`, so accountable-safety
      **justified-uniqueness** (`huniq`) makes it `gjC` — **left** disjunct; or it is **not
      realized**: its epoch is `≥ current`, so `+ 2 ≥ epoch(t')` — **right** disjunct. The
      chain-relative recency is *proven*, not assumed. -/
theorem votingSource_disjunct {τ : Timing} {bal₀ : Stakes n}
    (V : View n (FFGVote n)) (b'' : Block n) (t' : Time)
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (huniq : ∀ {C₁ C₂ : Checkpoint n},
      Justified bal₀ V C₁ → Justified bal₀ V C₂ → C₁.epoch = C₂.epoch → C₁.block = C₂.block)
    (hGJb'' : (greatestRealizedJustified bal₀ τ V t').block ≼ b'') :
    votingSource bal₀ τ V b'' t' = greatestRealizedJustified bal₀ τ V t'
    ∨ (votingSource bal₀ τ V b'' t').epoch + 2 ≥ τ.epochOf (τ.slotOf t') := by
  by_cases hep : τ.epochOf b''.slot = τ.epochOf (τ.slotOf t')
  · -- same-epoch: `vs = gjblock b''` (Def 2). Show `gjblock b'' = gjC` (the realized `GJ`) — the
    -- LEFT disjunct — via the SAME realized-max + accountable-safety-uniqueness pattern as the
    -- cross-epoch branch. In the same-epoch case `gjblock b''` is **always realized** (epoch cut
    -- `< epoch(b''.slot) = epochOf(slotOf t')`), so it lands in the realized argmax; and `gjC`
    -- (justified, on `chain(b'')` by `hGJb''`, epoch-cut) lands in `gjblock b''`'s argmax — each
    -- dominates the other in epoch, then `huniq` forces equal blocks. NO recency premise. (When the
    -- running epoch is `0` both selectors are genesis; that edge is taken via the trivially-true
    -- right disjunct `_ + 2 ≥ 0`.)
    rw [votingSource_eq_gjblock bal₀ τ V b'' t' hep]
    by_cases h0 : τ.epochOf (τ.slotOf t') = 0
    · exact Or.inr (by rw [h0]; exact Nat.zero_le _)
    · refine Or.inl ?_
      have hpos : 1 ≤ τ.epochOf (τ.slotOf t') := Nat.one_le_iff_ne_zero.mpr h0
      have hposb : 1 ≤ τ.epochOf b''.slot := by rw [hep]; exact hpos
      -- `gjblock b''` realized: epoch `< epoch(b''.slot) = epochOf(slotOf t')`.
      have hgjbReal : (gjblock bal₀ τ V b'').epoch < τ.epochOf (τ.slotOf t') := by
        rw [← hep]; exact gjblock_realized bal₀ τ V b'' hposb
      -- `gjC` realized: epoch `< epochOf(slotOf t')`.
      have hgjCReal : (greatestRealizedJustified bal₀ τ V t').epoch < τ.epochOf (τ.slotOf t') :=
        greatestRealizedJustified_realized bal₀ τ V t' hpos
      -- direction 1: `gjblock b'' ≤ gjC` (realized-max — `gjblock b''` is justified + realized).
      have hle1 : (gjblock bal₀ τ V b'').epoch ≤ (greatestRealizedJustified bal₀ τ V t').epoch :=
        greatestRealizedJustified_max bal₀ τ V t'
          (justified_mem_mentioned bal₀ V hwit (gjblock_justified bal₀ τ V b''))
          (gjblock_justified bal₀ τ V b'') hgjbReal
      -- direction 2: `gjC ≤ gjblock b''` (gjblock-max — `gjC` on `chain(b'')`, epoch-cut).
      have hle2 : (greatestRealizedJustified bal₀ τ V t').epoch ≤ (gjblock bal₀ τ V b'').epoch :=
        gjblock_max bal₀ τ V b''
          (justified_mem_mentioned bal₀ V hwit (greatestRealizedJustified_justified bal₀ τ V t'))
          (greatestRealizedJustified_justified bal₀ τ V t') hGJb'' (by rw [hep]; exact hgjCReal)
      have hepeq : (gjblock bal₀ τ V b'').epoch = (greatestRealizedJustified bal₀ τ V t').epoch :=
        le_antisymm hle1 hle2
      have hblockeq : (gjblock bal₀ τ V b'').block
          = (greatestRealizedJustified bal₀ τ V t').block :=
        huniq (gjblock_justified bal₀ τ V b'')
          (greatestRealizedJustified_justified bal₀ τ V t') hepeq
      -- same block + same epoch ⇒ same checkpoint (structure eta + field rewrite).
      calc gjblock bal₀ τ V b''
          = (⟨(gjblock bal₀ τ V b'').block, (gjblock bal₀ τ V b'').epoch⟩ : Checkpoint n) := rfl
        _ = (⟨(greatestRealizedJustified bal₀ τ V t').block,
              (greatestRealizedJustified bal₀ τ V t').epoch⟩ : Checkpoint n) := by
              rw [hblockeq, hepeq]
        _ = greatestRealizedJustified bal₀ τ V t' := rfl
  · -- cross-epoch: `vs = greatestJustifiedOfChain b''`. Discharged **structurally** from the
    -- on-chain placement `gjC.block ≼ b''` + accountable-safety justified-uniqueness (`huniq`)
    -- + realization — NO recency/liveness premise. `GU(b'') ≥ gjC` (in epoch), and either
    -- `GU(b'')` is realized (`epoch < current`), forcing `GU(b'').epoch = gjC.epoch` and hence
    -- (uniqueness) `GU(b'') = gjC` — left disjunct — or it is not realized, so its epoch is
    -- `≥ current`, giving the right disjunct directly.
    have hvs : votingSource bal₀ τ V b'' t' = greatestJustifiedOfChain bal₀ V b'' := by
      unfold votingSource; rw [if_neg hep]
    rw [hvs]
    have hGUj : Justified bal₀ V (greatestJustifiedOfChain bal₀ V b'') :=
      greatestJustifiedOfChain_justified bal₀ V b''
    have hge : (greatestRealizedJustified bal₀ τ V t').epoch
        ≤ (greatestJustifiedOfChain bal₀ V b'').epoch :=
      greatestJustifiedOfChain_ge_of_justified bal₀ V b'' hwit
        (greatestRealizedJustified_justified bal₀ τ V t') hGJb''
    by_cases hlt : (greatestJustifiedOfChain bal₀ V b'').epoch < τ.epochOf (τ.slotOf t')
    · -- realized ⇒ `≤ gjC.epoch` (`greatestRealizedJustified_max`) ⇒ `= gjC.epoch` ⇒ same block.
      have hGUmax : (greatestJustifiedOfChain bal₀ V b'').epoch
          ≤ (greatestRealizedJustified bal₀ τ V t').epoch :=
        greatestRealizedJustified_max bal₀ τ V t'
          (justified_mem_mentioned bal₀ V hwit hGUj) hGUj hlt
      have hepeq : (greatestJustifiedOfChain bal₀ V b'').epoch
          = (greatestRealizedJustified bal₀ τ V t').epoch := le_antisymm hGUmax hge
      have hblockeq : (greatestJustifiedOfChain bal₀ V b'').block
          = (greatestRealizedJustified bal₀ τ V t').block :=
        huniq hGUj (greatestRealizedJustified_justified bal₀ τ V t') hepeq
      refine Or.inl ?_
      -- same block + same epoch ⇒ same checkpoint (structure eta + field rewrite).
      calc greatestJustifiedOfChain bal₀ V b''
          = (⟨(greatestJustifiedOfChain bal₀ V b'').block,
              (greatestJustifiedOfChain bal₀ V b'').epoch⟩ : Checkpoint n) := rfl
        _ = (⟨(greatestRealizedJustified bal₀ τ V t').block,
              (greatestRealizedJustified bal₀ τ V t').epoch⟩ : Checkpoint n) := by
              rw [hblockeq, hepeq]
        _ = greatestRealizedJustified bal₀ τ V t' := rfl
    · push Not at hlt
      exact Or.inr (le_trans hlt (Nat.le_add_right _ 2))

/-- **II.3 — comparability split.** Given the realized-GJ-rooted invariant `gjC.block ≼ b`
    (the LMD-GHOST-HFC fork choice is rooted at the *realized* greatest justified checkpoint,
    Def 3, so the confirmed block descends from it — derived by
    `greatestRealizedJustified_on_chain`), every
    ancestor `B'` of the safe descendant `B ⪰ b` is comparable with `gjC.block`: since
    `gjC.block ≼ b ≼ B` and `B' ≼ B`, both `B'` and `gjC.block` are ancestors of `B`. The result is
    stated for the realized `GJ`, which is exactly the filter's `gjC`. -/
theorem GJ_le_or_ge_B' {τ : Timing} {bal₀ : Stakes n} {V : View n (FFGVote n)} {t' : Time}
    {b B B' : Block n}
    (hGJb : (greatestRealizedJustified bal₀ τ V t').block ≼ b) (hbB : b ≼ B) (hB'B : B' ≼ B) :
    B' ≼ (greatestRealizedJustified bal₀ τ V t').block
      ∨ (greatestRealizedJustified bal₀ τ V t').block ≼ B' :=
  ancestor_comparable hB'B (Block.Ancestor.trans hGJb hbB)

/-- **II.5a — the structural leaf walk** (the `EpochLeafWitness` derivation). Given any in-view
    block `x` whose slot is `≤ slotOf t'`, there is an in-view **leaf** descendant `b'' ⪰ x` with
    no eligible children (`eligibleChildren τ trivialFilter (𝒱 w t') t' b'' = ∅`) and still of slot
    `≤ slotOf t'`. Proof: well-founded recursion on `slotOf t' − x.slot`. If `x` already has no
    eligible children it is the leaf; otherwise pick an eligible child `c` (in-view, well-formed,
    `c.slot ≤ slotOf t'`, `c.parent? = some x`). Well-formedness gives
    `x.slot < c.slot ≤ slotOf t'`,
    so the measure strictly decreases; recurse on `c` and prepend `x ≼ c` (`parent_ancestor`). This
    is the finiteness/termination fact the §4 D2 existential rests on — purely a property of the
    view's finite block tree, with **no** FFG / block-production assumption (the epoch bound comes
    from staying inside `slot ≤ slotOf t'`, the view's slot-cut). -/
theorem view_leaf_witness {τ : Timing} {P : Type} {V : View n P} {t' : Time} :
    ∀ (d : ℕ) (x : Block n), τ.slotOf t' - x.slot = d → x ∈ V.blocks → x.slot ≤ τ.slotOf t' →
      ∃ b'' ∈ V.blocks, x ≼ b'' ∧ b''.slot ≤ τ.slotOf t' ∧
        eligibleChildren τ trivialFilter V t' b'' = ∅ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hxmem hxslot
    by_cases hleaf : eligibleChildren τ trivialFilter V t' x = ∅
    · exact ⟨x, hxmem, Block.Ancestor.refl x, hxslot, hleaf⟩
    · -- nonempty ⇒ pick an eligible child `c`, recurse on the smaller measure.
      have hne : (eligibleChildren τ trivialFilter V t' x).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hleaf
      obtain ⟨c, hc⟩ := hne
      rw [mem_eligibleChildren] at hc
      obtain ⟨hcmem, hcpar, hcwf, hcslot, _⟩ := hc
      have hxc : x.slot < c.slot := parent_slot_lt hcpar hcwf
      -- the measure at `c` is strictly smaller than `d`.
      have hmeas : τ.slotOf t' - c.slot < d := by
        rw [← hd]
        exact Nat.sub_lt_sub_left (lt_of_lt_of_le hxc hcslot) hxc
      obtain ⟨b'', hb''mem, hcb'', hb''slot, hb''leaf⟩ :=
        ih _ hmeas c rfl hcmem hcslot
      exact ⟨b'', hb''mem, Block.Ancestor.trans (parent_ancestor hcpar) hcb'', hb''slot, hb''leaf⟩

/-- **II.5 — the D2 leaf witness and structural recency.** In the D2 branch `B'` is an in-view block with
    `gfC.block ≼ B'`, of slot `≤ slotOf t'`, and on the chain of the *realized* greatest-justified
    block (`gjC.block ≼ B'`, the D2 case fact, where `gjC` is the filter's realized `GJ`). The
    structural leaf walk `view_leaf_witness` supplies an in-view leaf `b'' ⪰ B'` of slot
    `≤ slotOf t'`; the finalized-chain descent `gfC.block ≼ b''` is `gfC.block ≼ B' ≼ b''`, the
    epoch bound is `b''.slot ≤ slotOf t' ⇒ epochOf b''.slot ≤ epochOf (slotOf t')` (`epochOf` is
    `/E`, monotone). The voting-source disjunct comes from `votingSource_disjunct`, which
    proves the cross-epoch recency **structurally** from the on-chain placement
    `gjC.block ≼ b''` (`gjC.block ≼ B' ≼ b''`) + accountable-safety justified-uniqueness (`huniq`)
    + realization — **no recency / liveness premise is required**. The leaf existence is the
    view's finite-tree termination. -/
theorem ffg_leaf_witness {τ : Timing} {bal₀ : Stakes n}
    {𝒱 : ViewFamily n (FFGVote n)}
    {w : Validator n} {t' : Time} {B' : Block n}
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    (hB'mem : B' ∈ (𝒱 w t').blocks)
    (hB'slot : B'.slot ≤ τ.slotOf t')
    (hGFB' : (greatestFinalized bal₀ (𝒱 w t')).block ≼ B')
    (hGJB' : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ B')
    (huniq : ∀ {C₁ C₂ : Checkpoint n},
      Justified bal₀ (𝒱 w t') C₁ → Justified bal₀ (𝒱 w t') C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block) :
    ∃ b'' ∈ (𝒱 w t').blocks, B' ≼ b'' ∧ b''.slot ≤ τ.slotOf t' ∧
      (greatestFinalized bal₀ (𝒱 w t')).block ≼ b'' ∧
      τ.epochOf b''.slot ≤ τ.epochOf (τ.slotOf t') ∧
      eligibleChildren τ trivialFilter (𝒱 w t') t' b'' = ∅ ∧
      ( votingSource bal₀ τ (𝒱 w t') b'' t' = greatestRealizedJustified bal₀ τ (𝒱 w t') t'
        ∨ (votingSource bal₀ τ (𝒱 w t') b'' t').epoch + 2 ≥ τ.epochOf (τ.slotOf t') ) := by
  obtain ⟨b'', hb''mem, hB'b'', hb''slot, hb''leaf⟩ :=
    view_leaf_witness _ B' rfl hB'mem hB'slot
  have hGJb'' : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b'' :=
    Block.Ancestor.trans hGJB' hB'b''
  refine ⟨b'', hb''mem, hB'b'', hb''slot, Block.Ancestor.trans hGFB' hB'b'', ?_, hb''leaf,
    votingSource_disjunct (𝒱 w t') b'' t' hwit huniq hGJb''⟩
  exact Nat.div_le_div_right hb''slot

/-- **II.6 — `ConfirmedNotFFGFiltered`.**
    Given the §3.1 engine premises (for `chain_in_view`) and the §4 premises, every safe
    descendant `B ⪰ b` is `NeverFiltered` at `ffgFilter`. Per honest `w`, cutoff `k`, time `t'`
    with `slotOf t' = k`, and ancestor `B' ≼ B`. The realized `GJ`'s placement relative to `B`
    splits on `epochOf s < epoch(GJ_real)` (`s = B`'s safe slot, `E := epochOf s`):

    * **DESCENDANT case `epoch(GJ_real) > E`** — handled by the **explicit cross-epoch ladder**
      (`CrossEpoch.lean`). The engine's `hHead` window `[s, k)` covers the *whole* epoch
      `eGJ := epoch(GJ_real)` (`E < eGJ ⇒ s ≤ fslot eGJ`; realization `eGJ < epochOf k ⇒
      lslot eGJ < k`), so `canonicalEpoch_of_headWindow` builds `CanonicalThroughoutEpoch B eGJ`
      (the ladder rung — `B` canonical throughout the GJ's whole epoch, including its early-epoch
      voters), and `realizedGJ_descends_of_canonicalEpoch` gives `B ≼ block(GJ_real)`. **No
      GU-root slot bound, no gate** — the cross-epoch induction's per-rung descendant placement
      replaces them. (The ladder is non-circular: it consumes only head safety at the *earlier*
      slots `j < k` the engine's strong induction already grants.)

    * **ANCESTOR case `epoch(GJ_real) ≤ E` (slot-bound-free)** —
      `greatestRealizedJustified_on_chain` (gate + GU-recency, comparability form) supplies only the
      *compatibility* `block(GJ_real) ≼ B ∨ B ≼ block(GJ_real)`; the never-filter **case-splits on
      its direction** rather than pinning one with a slot bound; both directions keep the block:
      - `B ≼ block(GJ_real)`: every ancestor `B' ≼ B ≼ block(GJ_real)` is kept **directly** by the
        first `ffgFilter` disjunct (`keep_of_ancestor_GJ`, D1) — no recency, no slot bound, just the
        gate's compatibility. This is the branch that obviates the slot bound: the realized GJ of
        epoch in `[epoch(b), E]` may be justified by *pre-confirmation* voters (slots `< s`) where
        `B` has no head-safety, but here `B` (hence each `B' ≼ B`) is itself an *ancestor* of
        `block(GJ_real)`, so the keep-by-ancestry disjunct fires without any timing argument.
      - `block(GJ_real) ≼ B`: the existing D1/D2 comparability-split logic (`GJ_le_or_ge_B'` + the
        realized D1 + the D2 leaf witness). The `epoch(GJ_real) < epoch(B)` sub-band returns this
        direction from the gate's GU-recency/uniqueness route (`greatestRealizedJustified_max`
        forces `epoch(GJ_real) = epoch(GUc)`, then `huniq` forces `block(GJ_real) = GUc.block ≼ B`).
      The comparability case-split therefore eliminates the GU-root slot-bound premise.
    * `block(GF) ≼ block(GJ_real)` is **D1**
      (`greatestFinalized_block_ancestor_greatestRealizedJustified`), consuming the finalized-prefix
      clause of `FFG_AccountableSafety` (`hAS.2.2`).

    The result then follows from the comparability split (II.3), D1-close
    (`keep_of_ancestor_GJ`), and D2 leaf witness (II.5). -/
theorem confirmedNotFFGFiltered_proved (bal₀ : Stakes n)
    {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} (hv : v ∈ fm.honest) :
    ConfirmedNotFFGFiltered τ fm cm pb boost bal₀ 𝒱 v b := by
  -- Joint-induction functional form: cutoff `k`, head safety for `B` at `j < k`.
  intro hAS hnoequiv hByz s B hs1 hgst hbB hBsafe hgate hAnchor
    k hk_ge hHead w hw t' hk_eq ht' B' hB'B
  classical
  have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
  -- The lower bound `ht'` is `st(slotOf(st s)) ≤ t'`; rewrite `slotOf (st s) = s`.
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  -- justified-uniqueness-per-epoch from `FFG_AccountableSafety` (the GU-recency case of J2/D3).
  have huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t) C₁ → Justified bal₀ (𝒱 w t) C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block :=
    hAS.2.1
  -- Unpack the GU-anchor inputs at this honest view: GU recency and root, plus the
  -- greatest-finalized realization used by realized D1. No slot bound is needed because the proof
  -- handles both comparability directions below.
  obtain ⟨hGU, hGFreal, hsel⟩ := hAnchor hw ht'
  -- `s ≤ slotOf t'` from `st s ≤ t'`, then `B.slot ≤ slotOf t'` (genesis: slot 0; else `≤ s - 1`).
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
  -- realization of `B`'s epoch: `epochOf B.slot ≤ epochOf(slotOf t')` (`epochOf` is `/E`, mono).
  have hbt' : τ.epochOf B.slot ≤ τ.epochOf (τ.slotOf t') := Nat.div_le_div_right hB_le_St'
  -- **`block(GJ_real)` placed relative to `B`** — the R3 case split on the realized GJ's epoch vs
  -- `epochOf s` (= `epochOf(slotOf(st s))`). `epochOf s = epochOf(slotOf(st s))` after `hslots`.
  by_cases hcase : τ.epochOf s < (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch
  · -- **DESCENDANT case** (`epoch(GJ_real) > epochOf s`): the realized `GJ` descends *from* `B`,
    -- via the **explicit cross-epoch ladder**. The engine's `hHead` window `[s, k)` covers the
    -- *whole* epoch `eGJ := epoch(GJ_real)` (since `epochOf s < eGJ` ⇒ `s ≤ fslot eGJ`, and
    -- realization `eGJ < epochOf k` ⇒ `lslot eGJ < k`), so `canonicalEpoch_of_headWindow` builds
    -- `CanonicalThroughoutEpoch B eGJ` — B is canonical throughout the GJ's whole epoch, including
    -- the early-epoch voters. Then `realizedGJ_descends_of_canonicalEpoch` (the STEP placement)
    -- gives `B ≼ block(GJ_real)` since `epochOf B.slot ≤ epochOf s < eGJ`. **No GU-root slot
    -- bound is used** — the cross-epoch induction's per-rung descendant placement replaces it.
    set eGJ := (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch with heGJ
    have hHead' : ∀ ⦃j : Slot⦄, s ≤ j → j < k → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
        B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
          (τ.st j) := by
      intro j hj1 hjk i hi
      exact hHead (by rw [hslots]; exact hj1) hjk hi
    have hreal : eGJ < τ.epochOf (τ.slotOf t') :=
      greatestRealizedJustified_realized_of_pos bal₀ τ (𝒱 w t') t'
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hcase)
    -- whole epoch `eGJ` inside the window `[s, k)`.
    have hlo : s ≤ τ.fslot eGJ := by
      -- `s ≤ lslot(epochOf s) < fslot(epochOf s + 1) ≤ fslot eGJ` (from `epochOf s < eGJ`).
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
      -- `lslot eGJ = eGJ·E + (E−1) < (eGJ+1)·E ≤ (epochOf k)·E ≤ k`, from `eGJ < epochOf k = k`.
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
    -- `B' ≼ B ≼ block(GJ_real)` ⇒ keep by the **first** filter disjunct (`ffgFilterAt` D1).
    exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hBGJ)
  · -- **LOWER-OR-EQUAL-EPOCH case** (`epoch(GJ_real) ≤ epochOf s`): the realized
    -- `GJ` is *comparable* with `B` via the gate / GU-recency route
    -- (`greatestRealizedJustified_on_chain`, in its **slot-bound-free comparability form**:
    -- `block(GJ_real) ≼ B ∨ B ≼ block(GJ_real)`). **No GU-root slot bound is used** — instead the
    -- never-filter case-splits on the comparability direction: the gate keeps
    -- the block whichever way `B` and `block(GJ_real)` compare.
    push Not at hcase
    have hcompB : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ B
        ∨ B ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
      greatestRealizedJustified_on_chain (b := B) (t := τ.st s) hgate huniq hw
        (by rw [hslots]; rw [hslots] at ht'; exact ht') hbt' hGU
    rcases hcompB with hGJb | hBleGJ
    · -- **`block(GJ_real) ≼ B`** — the existing ancestor-case logic (D1/D2 comparability split).
      -- **Realized D1**: `block(GF) ≼ block(GJ_real)` (finalized-prefix from `FFG_AS`).
      have hGFGJ : (greatestFinalized bal₀ (𝒱 w t')).block ≼
          (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
        greatestFinalized_block_ancestor_greatestRealizedJustified bal₀ τ (𝒱 w t') t'
          (hAS.2.2 hw (t := t')) hGFreal
      -- comparability of `B'` with the realized greatest-justified block (II.3), at `b := B`.
      rcases GJ_le_or_ge_B' hGJb (Block.Ancestor.refl B) hB'B with hD1 | hGJB'
      · -- D1: B' ≼ gjC.block — keep by the first disjunct.
        exact keep_of_ancestor_GJ hsel hD1
      · -- D2: gjC.block ≼ B'. First, `gfC.block ≼ B'` via `gfC.block ≼ gjC.block` (realized D1).
        have hGFB' : (greatestFinalized bal₀ (𝒱 w t')).block ≼ B' :=
          Block.Ancestor.trans hGFGJ hGJB'
        by_cases hBne : B = Block.genesis
        · -- B = genesis ⇒ B' = genesis ⇒ B' ≼ gjC.block (D1) by genesis_ancestor.
          have hB'gen : B' = Block.genesis := by
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
          -- the leaf witness (derived structurally) discharges the D2 existential; the recency
          -- disjunct is *proven* **structurally** (no recency premise) from the on-chain placement
          -- `gjC.block ≼ B'` (`hGJB'`) + accountable-safety uniqueness (`hAS.2.1`) + realization.
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
    · -- **`B ≼ block(GJ_real)`** — keep DIRECTLY by the first `ffgFilter` disjunct, no recency:
      -- `B' ≼ B ≼ block(GJ_real)` ⇒ `B' ≼ block(GJ_real)` (`keep_of_ancestor_GJ`, D1). This is the
      -- branch that obviates the slot bound entirely.
      exact keep_of_ancestor_GJ hsel (Block.Ancestor.trans hB'B hBleGJ)

end FastConfirmation.HFC

end
