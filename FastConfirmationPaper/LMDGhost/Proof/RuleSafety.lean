module
public import Mathlib.Tactic
public import FastConfirmationPaper.LMDGhost.Proof.FutureHeadAgreement
public import FastConfirmationPaper.LMDGhost.Claims

@[expose] public section

/-!
# LMDGhost / Proof / Rule

Lemmas 7–9: from `isConfirmed` to the Algorithm-4 headline results (Theorem 1).

A confirmed block `b` is an ancestor of `B := highestConfirmedSinceEpoch …`, the
argmax-by-slot of the blocks that were `isLMDGHOSTSafe` in `v`'s own start-view at
some slot `s' ∈ [fslot e + 1, slot(t)]` of the previous epoch `e`. The key bridge:

* `safe_block_wf_slot` — such a `B` is well-formed and of slot `≤ s' - 1` (derived from
  `isLMDGHOSTSafe` via the honest-majority ⇒ honest-supporter ⇒ `ViewValid` chain).
* `highestConfirmed_mem` — `B` is genesis, or a candidate: in some honest start-view,
  safe at that view's start time, with `1 ≤ s'` and `s'`-after-GST (from `sg`).

Plugging `B` (at that start view/time, anchor `gj 𝒱 v (st s')`) into the arbitrary-time
`head_safety_engine`, with `AnchorsCoincide` from `StaticBalances` and `NeverFiltered`
trivial for `trivialFilter`, yields the head-safety conclusion for `b ≼ B` (Lemma 7–8,
Safety). Monotonicity (Lemma 9) is `Rule`-internal: a confirmed block stays confirmed.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

section Rule

variable {τ : Timing} {fm : FaultModel n} {cm : Committees n} {pb : Weight}
  {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
  {𝒱 : ViewFamily n P} {C : Anchor n}

/-- `trivialFilter` never filters anything, so `NeverFiltered` is vacuous for it. -/
theorem NeverFiltered_trivial (b : Block n) (t : Time) :
    NeverFiltered τ fm (trivialFilter (n := n) (P := P)) 𝒱 b t :=
  fun _ _ _ _ _ _ => trivial

/-- A `ghostAux` traversal from a well-formed start lands on a well-formed block (each
    GHOST step moves to an eligible — hence well-formed — child). -/
theorem ghostAux_WellFormed (A : Anchor n) (flt : BlockFilter n P) (V : View n P) (t : Time) :
    ∀ (fuel : ℕ) (b : Block n), b.WellFormed →
      (ghostAux τ A boost pb flt V t fuel b).WellFormed := by
  intro fuel
  induction fuel with
  | zero => intro b hb; exact hb
  | succ fuel ih =>
    intro b hb
    unfold ghostAux
    cases hstep : ghostStep τ A boost pb flt V t b with
    | none => exact hb
    | some best =>
      have hmem := ghostStep_some_mem hstep
      rw [mem_eligibleChildren] at hmem
      exact ih best hmem.2.2.1

/-- **The LMD-GHOST head is well-formed.** Genesis is well-formed (`True`) and every
    GHOST step lands on a well-formed eligible child. -/
theorem forkChoiceHead_WellFormed (A : Anchor n) (flt : BlockFilter n P) (V : View n P)
    (t : Time) : (forkChoiceHead τ A boost pb flt V t).WellFormed := by
  unfold forkChoiceHead
  exact ghostAux_WellFormed A flt V t (τ.slotOf t + 1) Block.genesis trivial

/-- **A safe block is well-formed and of past slot.** If `B ≠ genesis` is `isLMDGHOSTSafe`
    in a valid view `V` at time `t` (with the committee-honest-majority and `0 ≤ pb`), then
    `B` is well-formed and `B.slot ≤ slot(t) - 1`. The honest majority forced by Def 8 (via
    `Hmaj_of_isOneConfirmed`) yields an honest supporter whose effective vote names a
    descendant of `B`; `ViewValid` makes that block well-formed of slot `≤` the vote's slot,
    and ancestry transports both facts down to `B`. -/
theorem safe_block_wf_slot {V : View n P} {B : Block n} {t : Time}
    (hVV : ViewValid cm V) (hcm : CommitteeHonestMajority fm cm C) (hpb : 0 ≤ pb)
    (hsafe : isLMDGHOSTSafe τ fm cm pb C V B t) (hBne : B ≠ Block.genesis) :
    B.WellFormed ∧ B.slot ≤ τ.slotOf t - 1 := by
  -- one-confirmed in `V` ⇒ honest majority at cutoff `slot(t) - 1`.
  have h1c : isOneConfirmed τ fm cm pb C V B t := (hsafe (Block.Ancestor.refl B)).resolve_left hBne
  have hmaj := Hmaj_of_isOneConfirmed τ C cm fm pb V B t hcm h1c
  -- the majority is positive (`W`, `Wp` are nonnegative).
  have hWnn : 0 ≤ W C cm B (τ.slotOf t - 1) := totalWeight_nonneg C _
  have hWpnn : 0 ≤ Wp C pb := mul_nonneg hpb (totalWeight_nonneg C _)
  have hHpos : 0 < H C cm fm V B (τ.slotOf t - 1) := by
    have : (0 : Weight) ≤ (W C cm B (τ.slotOf t - 1) + Wp C pb) / 2 := by
      have := add_nonneg hWnn hWpnn; linarith
    linarith [hmaj]
  -- an honest supporter, and its effective vote names a descendant of `B`.
  obtain ⟨i, _hi, hsup⟩ := honest_supporter_of_H_pos hHpos
  unfold View.supportsLMD at hsup
  cases hev : V.effectiveVote i (τ.slotOf t - 1) with
  | none => rw [hev] at hsup; simp at hsup
  | some gv =>
    rw [hev] at hsup
    obtain ⟨hmem, hgvslot⟩ := effectiveVote_some_mem hev
    have hBanc : B ≼ gv.block := isAncestorOf_imp hsup
    -- `ViewValid` on the supporter's vote: its block is well-formed of slot `≤ gv.slot`.
    have hgvmem : gv ∈ V.ghostVotes := Finset.filter_subset _ _ hmem
    obtain ⟨m, hmmsg, _hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hgvmem
    obtain ⟨_, hblkslot, hblkwf⟩ := hVV m hmmsg
    rw [hmg] at hblkslot hblkwf
    refine ⟨WellFormed_of_ancestor hBanc hblkwf, ?_⟩
    calc B.slot ≤ gv.block.slot := slot_le_of_ancestor hBanc hblkwf
      _ ≤ gv.slot := hblkslot
      _ ≤ τ.slotOf t - 1 := hgvslot

/-- **The highest-confirmed block is genesis or a candidate.** Either
    `highestConfirmedSinceEpoch … e t = genesis`, or it is some block `B` that lives in
    `v`'s start-view of a slot `s' ∈ [fslot e + 1, slot(t)]` and is `isLMDGHOSTSafe` there
    (anchored at `gj 𝒱 v (st s')`). This unpacks the `argmax`-over-`biUnion` definition. -/
theorem highestConfirmed_mem (v : Validator n) (e : Epoch) (t : Time) :
    highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v e t = Block.genesis ∨
    ∃ s', s' ∈ Finset.Icc (τ.fslot e + 1) (τ.slotOf t) ∧
      (highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v e t) ∈ (𝒱 v (τ.st s')).blocks ∧
      isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s')) (𝒱 v (τ.st s'))
        (highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v e t) (τ.st s') := by
  unfold highestConfirmedSinceEpoch
  extract_lets cand
  split
  · -- argmax = some B: `B ∈ cand`, unpack the biUnion/filter.
    rename_i B harg
    right
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList] at hmem
    simp only [cand, Finset.mem_biUnion, Finset.mem_filter] at hmem
    obtain ⟨s', hs', hBblk, hBsafe⟩ := hmem
    exact ⟨s', hs', hBblk, hBsafe⟩
  · -- argmax = none: result is genesis.
    left; rfl

/-- Under `StaticBalances`, *every* `gj`-anchor is the same `Stakes` (their `.bal`
    fields all coincide, and the positivity field is proof-irrelevant). The full
    equality (not just at slot boundaries) the Safety conclusion needs. -/
theorem gj_const_of_StaticBalances (hsb : StaticBalances gj 𝒱)
    (w : Validator n) (t' : Time) (v : Validator n) (t : Time) :
    gj 𝒱 w t' = gj 𝒱 v t := by
  have hbal : (gj 𝒱 w t').bal = (gj 𝒱 v t).bal := by funext i; exact hsb w t' v t i
  cases hA : gj 𝒱 w t' with
  | mk b1 h1 =>
    cases hB : gj 𝒱 v t with
    | mk b2 h2 =>
      rw [hA, hB] at hbal
      simp only at hbal
      subst hbal
      rfl

/-- **Safe ⇒ canonical from `st s` on (Lemma 7 bridge).** A block `B` that is
    `isLMDGHOSTSafe` in `v`'s own start-view at `st s` (with `B` well-formed, of slot `≤ s`,
    `1 ≤ s`, `st s` after GST) is on *every* honest validator's fork-choice head at every
    time `t' ≥ st s`. Pure reduction to `head_safety_engine` at `C := gj 𝒱 v (st s)`, with
    `AnchorsCoincide` from `StaticBalances`, `NeverFiltered` trivial, and the honest anchor
    `gj 𝒱 w t'` swapped to `C` (every `gj`-anchor coincides under `StaticBalances`). -/
theorem safe_canonical_from_engine
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb trivialFilter 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t))
    (hpb : 0 ≤ pb) (hsb : StaticBalances gj 𝒱)
    {v : Validator n} {B : Block n} {s : Slot}
    (hv : v ∈ fm.honest) (hBwf : B.WellFormed) (hBslot : B.slot ≤ s) (h1 : 1 ≤ s)
    (hgst : τ.AfterGST (τ.st (s - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s)) (𝒱 v (τ.st s)) B (τ.st s)) :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      B ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t' := by
  intro w t' hw ht'
  set C := gj 𝒱 v (τ.st s) with hC
  have hcmC : CommitteeHonestMajority fm cm C := hcm (w := v) (t := τ.st s)
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have hAnchorC : AnchorsCoincide gj 𝒱 fm τ C :=
    AnchorsCoincide_of_StaticBalances fm τ (v := v) (t := τ.st s) hsb
  have heng := head_safety_engine (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gj)
    (boost := boost) (flt := trivialFilter) (𝒱 := 𝒱) (C := C) (v := v) (b := B)
    (t := τ.st s) hSync hNF hHB hVV hcmC hpb hAnchorC hv hBwf
    (by rw [hslots]; exact hBslot) (by rw [hslots]; exact h1) (by rw [hslots]; exact hgst)
    hsafe (neverFiltered_to_hNFilOfHead (NeverFiltered_trivial B (τ.st s)))
  have hdeliv : τ.st (τ.slotOf (τ.st s)) ≤ t' := by rw [hslots]; exact ht'
  have hBhead := heng (w := w) (t' := t') hw hdeliv
  have hanc : gj 𝒱 w t' = C := gj_const_of_StaticBalances hsb w t' v (τ.st s)
  rw [hanc]; exact hBhead


/-- **Comparable canonical blocks, ordered by slot.** Two blocks both on a single
    (well-formed) honest fork-choice head are comparable; the one of not-greater slot is
    the ancestor. Closes both cases of the monotonicity assembly. -/
theorem canonical_ancestor_of_slot_le {w : Validator n} {t' : Time} {B B' : Block n}
    (hB : B ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t')
    (hB' : B' ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t')
    (hHeadWf : (forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t').WellFormed)
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

/-- **The highest-confirmed block dominates every candidate by slot.** If `B'` lives in
    `v`'s start-view of some slot `s' ∈ [fslot e' + 1, slot(t')]` and is `isLMDGHOSTSafe`
    there, then `B'.slot ≤ slot(highestConfirmedSinceEpoch … e' t')`. (Inverse of
    `highestConfirmed_mem`: `B'` is one of the `argmax` candidates.) -/
theorem highestConfirmed_slot_ge_of_mem {v : Validator n} {e' : Epoch} {t' : Time}
    {B' : Block n} {s' : Slot}
    (hs' : s' ∈ Finset.Icc (τ.fslot e' + 1) (τ.slotOf t'))
    (hmem : B' ∈ (𝒱 v (τ.st s')).blocks)
    (hsafe : isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s')) (𝒱 v (τ.st s')) B' (τ.st s')) :
    B'.slot ≤ (highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v e' t').slot := by
  classical
  -- `B'` is in the candidate set `cand`.
  set cand : Finset (Block n) :=
    (Finset.Icc (τ.fslot e' + 1) (τ.slotOf t')).biUnion (fun s'' =>
      (𝒱 v (τ.st s'')).blocks.filter (fun b' =>
        isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s'')) (𝒱 v (τ.st s'')) b' (τ.st s''))) with hcand
  have hmemcand : B' ∈ cand := by
    rw [hcand, Finset.mem_biUnion]
    exact ⟨s', hs', Finset.mem_filter.mpr ⟨hmem, hsafe⟩⟩
  -- `highestConfirmedSinceEpoch` is `argmax (·.slot) cand.toList`, defaulting to genesis.
  unfold highestConfirmedSinceEpoch
  simp only [← hcand]
  cases harg : cand.toList.argmax (·.slot) with
  | none =>
    -- argmax = none ⇒ list is empty ⇒ `cand = ∅`, contradicting `B' ∈ cand`.
    rw [List.argmax_eq_none, Finset.toList_eq_nil] at harg
    rw [harg] at hmemcand
    simp at hmemcand
  | some B =>
    -- `B'.slot ≤ B.slot` since `B` is the argmax and `B' ∈ cand.toList`.
    exact List.le_of_mem_argmax (Finset.mem_toList.mpr hmemcand) harg

/-- **Every honest validator supports `b'` at the later cutoff (the `M5` content).**
    Suppose head-safety `b ≼ forkChoiceHead` holds at every honest view from `st s` on,
    `b'` is an ancestor of `b`, and `i` is an honest validator that belongs to some
    committee of slot `k ∈ [s, σ]` (so it votes for its `b`-descendant head there, and that
    vote — or any later one up to `σ` — is delivered to `𝒱 v t'`). Then `i` supports `b'`
    at cutoff `σ` in `𝒱 v t'`. The slot of `i`'s effective vote at `σ` is `≥ k ≥ s`, where
    head-safety holds, so its head is a `b`- hence `b'`-descendant. -/
theorem honest_member_supports
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb trivialFilter 𝒱)
    {b b' : Block n} (hb'b : b' ≼ b) {s σ : Slot}
    (hgst : τ.AfterGST (τ.st s))
    (hHead : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      b ≼ forkChoiceHead τ (gj 𝒱 w t'') boost pb trivialFilter (𝒱 w t'') t'')
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

/-- **Canonical-for-an-epoch ⇒ safe at the later epoch (Lemma 8 — the crux).** If `b`
    (`≠ genesis`, slot-epoch `< e`) is, from `st s` on (with `s ≤ fslot e`, `st s` after
    GST), on every honest validator's fork-choice head, then for every honest `v` and every
    `t' ≥ st(fslot(e+1))`, `b` is `isLMDGHOSTSafe` in `𝒱 v t'`. **This is where Assumption 4
    (`β < (1 - pb)/4`) and `CommitteeCoversEpoch` are consumed.** For each `b' ≼ b`,
    full-epoch coverage makes the committee union `univ`, so `W_{b'} = totalWeight univ` and
    `Wp/W_{b'} = pb`; every honest committee member of epoch `e` votes for a `b`-, hence
    `b'`-descendant (`honest_member_supports`), so `H = J ≥ (1-β)W` and `Q = S/W ≥ 1-β`;
    Assumption 4 gives `1-β > ½(1+pb)+β`, the safety threshold. -/
theorem canonical_epoch_imp_safe
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb trivialFilter 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t))
    {b : Block n} {e : Epoch} {s : Slot}
    (hcover : CommitteeCoversEpoch τ cm e)
    (_hpb : 0 ≤ pb) (hβ4 : fm.β < (1 - pb) / 4)
    (_hbne : b ≠ Block.genesis) (hbepoch : b.slot < τ.fslot e) (hsfe : s ≤ τ.fslot e)
    (hgst : τ.AfterGST (τ.st s))
    (hHead : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      b ≼ forkChoiceHead τ (gj 𝒱 w t'') boost pb trivialFilter (𝒱 w t'') t'') :
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
      (forkChoiceHead_WellFormed (τ := τ) A trivialFilter (𝒱 v t') t')
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
      have hsupp := honest_member_supports hSync hNF hHB hb'b hgst hHead hv hih hik hsk hkσ hdeliv
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

end Rule

section Theorems

variable {τ : Timing} {gj : ViewFamily n P → Validator n → Time → Anchor n}

/-- **Theorem 1, Safety (Lemmas 7–8) is proved** for plain LMD-GHOST. A confirmed block
    `b` is an ancestor of `highestConfirmedSinceEpoch`, which is genesis or a block `B` safe
    in `v`'s start-view of some slot `s'` of the previous epoch (anchored at `gj 𝒱 v (st s')`).
    Plugging `B` into the arbitrary-time `head_safety_engine` (with `AnchorsCoincide` from
    `StaticBalances`, `NeverFiltered` trivial), and using that `StaticBalances` pins every
    honest fork-choice anchor to the engine anchor, yields `b ≼ forkChoiceHead` for every
    honest validator from time `st s'` on. -/
theorem proof_Theorem1_Safety : Theorem1_Safety (n := n) (P := P) τ gj := by
  intro fm cm pb boost 𝒱 hSync hNF hHB hVV hcm hWFB hpb hsb
    v b t hv _hsg hconf
  -- `b ≼ B := highestConfirmedSinceEpoch …`.
  set e := τ.epochOf (τ.slotOf t) - 1 with he
  set B := highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v e t with hB
  have hbB : b ≼ B := hconf
  rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gj)
      (𝒱 := 𝒱) v e t with hgen | ⟨s', hs', _hBblk, hBsafe⟩
  · -- `B = genesis`, so `b = genesis`; safety is trivial (genesis ≼ everything).
    rw [← hB] at hgen
    refine ⟨0, fun w t' _ _ => ?_⟩
    have : b = Block.genesis := by
      have := hbB; rw [hgen] at this
      cases this with
      | refl => rfl
    rw [this]; exact genesis_ancestor _
  · -- `B` is safe in `v`'s start-view at `st s'`, anchor `C := gj 𝒱 v (st s')`.
    rw [← hB] at hBsafe
    rw [Finset.mem_Icc] at hs'
    set C := gj 𝒱 v (τ.st s') with hC
    -- `1 ≤ s'` and `AfterGST (st s')`.
    have hs'1 : 1 ≤ s' := le_trans (Nat.le_add_left 1 _) hs'.1
    have hslots' : τ.slotOf (τ.st s') = s' := Timing.slotOf_st τ s'
    have hgstS : τ.AfterGST (τ.st (τ.slotOf (τ.st s') - 1)) := by
      rw [hslots']
      -- `_hsg.2`: GST at `st(fslot e)`. Algorithm 4's candidate range starts at `fslot e + 1`,
      -- so `fslot e + 1 ≤ s'`, hence `fslot e ≤ s' - 1` — exactly the one-slot GST margin the
      -- engine's faithful base delivery needs.
      have hsg2 : τ.AfterGST (τ.st (τ.fslot e)) := _hsg.2
      have hfle : τ.fslot e ≤ s' - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs'.1)
      have hmono : τ.st (τ.fslot e) ≤ τ.st (s' - 1) := by
        exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle
      exact le_trans hsg2 hmono
    -- engine for `B` at the start view/time, anchor `C`.
    have hAnchorC : AnchorsCoincide gj 𝒱 fm τ C :=
      AnchorsCoincide_of_StaticBalances fm τ (v := v) (t := τ.st s') hsb
    by_cases hBne : B = Block.genesis
    · -- B genesis ⇒ b genesis ⇒ trivial.
      refine ⟨0, fun w t' _ _ => ?_⟩
      have : b = Block.genesis := by
        have := hbB; rw [hBne] at this
        cases this with | refl => rfl
      rw [this]; exact genesis_ancestor _
    · have hcmC : CommitteeHonestMajority fm cm C := hcm (w := v) (t := τ.st s')
      obtain ⟨hBwf, hBslot⟩ := safe_block_wf_slot (C := C) (hVV _ _) hcmC hpb hBsafe hBne
      have heng := head_safety_engine (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gj)
        (boost := boost) (flt := trivialFilter) (𝒱 := 𝒱) (C := C) (v := v) (b := B)
        (t := τ.st s') hSync hNF hHB hVV hcmC hpb hAnchorC hv hBwf
        (le_trans hBslot (Nat.sub_le _ 1)) (by rw [hslots']; exact hs'1) hgstS hBsafe
        (neverFiltered_to_hNFilOfHead (NeverFiltered_trivial B (τ.st s')))
      refine ⟨τ.st s', fun w t' hw ht' => ?_⟩
      have hdeliv : τ.st (τ.slotOf (τ.st s')) ≤ t' := by rw [hslots']; exact ht'
      have hBhead := heng (w := w) (t' := t') hw hdeliv
      -- the honest anchor `gj 𝒱 w t'` equals `C`.
      have hanc : gj 𝒱 w t' = C := gj_const_of_StaticBalances hsb w t' v (τ.st s')
      rw [hanc]
      exact Block.Ancestor.trans hbB hBhead

/-- **Theorem 1, Monotonicity (Lemma 9) is proved** for plain LMD-GHOST: a confirmed
    block stays confirmed. Write `e_t := epochOf(slot t) - 1`, `e_t' := epochOf(slot t') - 1`
    (`e_t ≤ e_t'` since `t ≤ t'`). The old highest-confirmed `B` (`≽ b`) is safe at `st s`
    for some `s ∈ [fslot e_t + 1, slot t]`, hence (engine, `safe_canonical_from_engine`) on
    every honest head from `st s` on. To show `b` is still confirmed it suffices to show
    `B ≼ B'' := highestConfirmedSinceEpoch … e_t' t'`. Two cases on whether `s` is still in
    the new candidate range `[fslot e_t' + 1, slot t']`:
    * **same epoch** (`s` in range): `B` is itself a candidate at `t'`, so `slot B ≤ slot B''`;
    * **cross epoch** (`s ≤ fslot e_t'`): `B` is canonical throughout, so `canonical_epoch_imp_safe`
      (Lemma 8, Assumption 4) makes `B` safe at `st(slot t')`, a candidate slot, again giving
      `slot B ≤ slot B''`.
    Both `B`, `B''` are on `v`'s head at `t'`, so `slot B ≤ slot B''` gives `B ≼ B''`. -/
theorem proof_Theorem1_Monotonicity : Theorem1_Monotonicity (n := n) (P := P) τ gj := by
  intro fm cm pb boost 𝒱 hSync hNF hHB hVV hcm hWFB hpb hsb hβ4
    v b t t' hv hsg hle hcover hconf
  classical
  set et := τ.epochOf (τ.slotOf t) - 1 with het
  set et' := τ.epochOf (τ.slotOf t') - 1 with het'
  -- `B := highestConfirmedSinceEpoch … et t`, `b ≼ B`.
  set B := highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v et t with hBdef
  have hbB : b ≼ B := hconf
  -- target: `b ≼ B'' := highestConfirmedSinceEpoch … et' t'`.
  set B'' := highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v et' t' with hB''def
  change b ≼ B''
  -- `slot t ≤ slot t'` and `et ≤ et'`.
  have hslotle : τ.slotOf t ≤ τ.slotOf t' := Nat.div_le_div_right hle
  have hetle : et ≤ et' := by
    rw [het, het']
    exact Nat.sub_le_sub_right (Nat.div_le_div_right hslotle) 1
  -- unpack `B`: genesis, or safe at `st s`, `s ∈ [fslot et + 1, slot t]`.
  rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gj)
      (𝒱 := 𝒱) v et t with hgen | ⟨s, hs, hBblk, hBsafe⟩
  · -- `B = genesis` ⇒ `b = genesis` ⇒ `b ≼ B''`.
    rw [← hBdef] at hgen
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
  -- The base `AfterGST(st(s-1))` (engine's safe-block GST) and the weaker `AfterGST(st s)`
  -- (for the cross-epoch `canonical_epoch_imp_safe`). `fslot et + 1 ≤ s` gives `fslot et ≤ s-1`.
  have hgstSb : τ.AfterGST (τ.st (s - 1)) := by
    have hsg2 : τ.AfterGST (τ.st (τ.fslot et)) := hsg.2
    have hfle : τ.fslot et ≤ s - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs.1)
    exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle)
  have hgstS : τ.AfterGST (τ.st s) :=
    le_trans hgstSb (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le s 1))
  have hcmC : CommitteeHonestMajority fm cm (gj 𝒱 v (τ.st s)) := hcm (w := v) (t := τ.st s)
  obtain ⟨hBwf, hBslot0⟩ := safe_block_wf_slot (C := gj 𝒱 v (τ.st s)) (hVV _ _) hcmC hpb hBsafe hBne
  rw [hslots] at hBslot0
  have hBslot : B.slot ≤ s := le_trans hBslot0 (Nat.sub_le _ 1)
  -- M1: `B` is on every honest head from `st s` on.
  have hBcanon : ∀ ⦃w : Validator n⦄ ⦃t'' : Time⦄, w ∈ fm.honest → τ.st s ≤ t'' →
      B ≼ forkChoiceHead τ (gj 𝒱 w t'') boost pb trivialFilter (𝒱 w t'') t'' :=
    safe_canonical_from_engine hSync hNF hHB hVV hcm hpb hsb hv hBwf
      hBslot hs1 hgstSb hBsafe
  -- `st s ≤ t'`: `s ≤ slot t ≤ slot t'`, and `st(slot t') ≤ t'`.
  have hsslott' : s ≤ τ.slotOf t' := le_trans hs.2 hslotle
  have hst_s_t' : τ.st s ≤ t' :=
    le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hsslott') (Timing.st_slotOf_le τ t')
  -- the common head at `(v, t')`, and its well-formedness.
  set head := forkChoiceHead τ (gj 𝒱 v t') boost pb trivialFilter (𝒱 v t') t' with hhead
  have hheadWf : head.WellFormed := forkChoiceHead_WellFormed (τ := τ) _ trivialFilter (𝒱 v t') t'
  have hBhead : B ≼ head := hBcanon hv hst_s_t'
  -- `B''` is on the head at `(v, t')` (genesis trivially, else by M1).
  have hB''head : B'' ≼ head := by
    rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gj)
        (𝒱 := 𝒱) v et' t' with hg | ⟨s2, hs2, _hB2blk, hB2safe⟩
    · rw [← hB''def] at hg; rw [hg]; exact genesis_ancestor _
    · rw [← hB''def] at hB2safe
      rw [Finset.mem_Icc] at hs2
      by_cases hB2ne : B'' = Block.genesis
      · rw [hB2ne]; exact genesis_ancestor _
      · have hs21 : 1 ≤ s2 := le_trans (Nat.le_add_left 1 _) hs2.1
        have hgstS2 : τ.AfterGST (τ.st (s2 - 1)) := by
          -- GST at `fslot et'` from `sg.2` (GST at `fslot et`), lifted by `et ≤ et'`; then
          -- `fslot et' + 1 ≤ s2` gives `fslot et' ≤ s2 - 1` (the one-slot engine margin).
          have hsg2 : τ.AfterGST (τ.st (τ.fslot et')) :=
            le_trans hsg.2 (by
              exact_mod_cast Nat.mul_le_mul_right τ.slotDur
                (Nat.mul_le_mul_right τ.slotsPerEpoch hetle))
          have hfle2 : τ.fslot et' ≤ s2 - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs2.1)
          exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle2)
        have hcmC2 : CommitteeHonestMajority fm cm (gj 𝒱 v (τ.st s2)) := hcm (w := v) (t := τ.st s2)
        obtain ⟨hB2wf, hB2slot0⟩ :=
          safe_block_wf_slot (C := gj 𝒱 v (τ.st s2)) (hVV _ _) hcmC2 hpb hB2safe hB2ne
        rw [Timing.slotOf_st] at hB2slot0
        have hB2slot : B''.slot ≤ s2 := le_trans hB2slot0 (Nat.sub_le _ 1)
        have hB2canon := safe_canonical_from_engine hSync hNF hHB hVV hcm hpb hsb hv hB2wf
          hB2slot hs21 hgstS2 hB2safe
        have hs2slott' : s2 ≤ τ.slotOf t' := hs2.2
        have hst_s2_t' : τ.st s2 ≤ t' :=
          le_trans (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hs2slott')
            (Timing.st_slotOf_le τ t')
        exact hB2canon hv hst_s2_t'
  -- It remains to show `slot B ≤ slot B''`, then `B ≼ B''` (`canonical_ancestor_of_slot_le`).
  suffices hslot : B.slot ≤ B''.slot from
    Block.Ancestor.trans hbB (canonical_ancestor_of_slot_le hBhead hB''head hheadWf hslot)
  by_cases hcase : s ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t')
  · -- Case 1 (same epoch): `B` is a candidate at `t'` at its own slot `s`.
    exact highestConfirmed_slot_ge_of_mem (e' := et') hcase hBblk hBsafe
  · -- Case 2 (cross epoch): `s ≤ fslot et'`. Use M6 to make `B` safe at `st(slot t')`.
    rw [Finset.mem_Icc] at hcase
    push Not at hcase
    have hslefe : s ≤ τ.fslot et' := by
      by_contra hlt
      push Not at hlt
      have := hcase (Nat.succ_le_of_lt hlt)
      exact absurd hsslott' (not_le.mpr this)
    -- `1 ≤ slot t'`: `s ≥ 1` and `s ≤ slot t'`.
    have h1slott' : 1 ≤ τ.slotOf t' := le_trans hs1 hsslott'
    -- `B.slot < fslot et'`: `B.slot ≤ s - 1 < s ≤ fslot et'`.
    have hslt : s - 1 < s := Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hs1) Nat.one_pos
    have hBlt : B.slot < τ.fslot et' :=
      lt_of_le_of_lt hBslot0 (lt_of_lt_of_le hslt hslefe)
    -- `fslot (et' + 1) ≤ slot t'`: in Case 2, `epochOf(slot t') ≥ 1` (else `s = 0`).
    have hEpos : 1 ≤ τ.slotsPerEpoch := τ.hSlotsPerEpoch
    have hepoch_pos : 1 ≤ τ.epochOf (τ.slotOf t') := by
      rcases Nat.eq_zero_or_pos (τ.epochOf (τ.slotOf t')) with h0 | hpos
      · -- epochOf = 0 ⇒ et' = 0 ⇒ fslot et' = 0 ⇒ s ≤ 0, contradicting `1 ≤ s`.
        exfalso
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
      -- `fslot (epochOf s) = (s / E) * E ≤ s`.
      simp only [Timing.fslot, Timing.epochOf]
      exact Nat.div_mul_le_self (τ.slotOf t') τ.slotsPerEpoch
    have hst_fse1 : τ.st (τ.fslot (et' + 1)) ≤ τ.st (τ.slotOf t') :=
      by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfse1_le
    -- M6: `B` safe at `st(slot t')`.
    have hBsafe' : isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st (τ.slotOf t')))
        (𝒱 v (τ.st (τ.slotOf t'))) B (τ.st (τ.slotOf t')) :=
      canonical_epoch_imp_safe hSync hNF hHB hcm hcover hpb hβ4 hBne hBlt hslefe hgstS
        hBcanon hv (le_trans hst_fse1 (le_refl _))
    -- `B ∈ (𝒱 v (st(slot t'))).blocks` via `chain_in_view`.
    have hgst_slott' : τ.AfterGST (τ.st (τ.slotOf t' - 1)) := by
      refine le_trans hgstSb ?_
      exact_mod_cast Nat.mul_le_mul_right τ.slotDur (Nat.sub_le_sub_right hsslott' 1)
    have hcmSlott' : CommitteeHonestMajority fm cm (gj 𝒱 v (τ.st (τ.slotOf t'))) :=
      hcm (w := v) (t := τ.st (τ.slotOf t'))
    have hBmem : B ∈ (𝒱 v (τ.st (τ.slotOf t'))).blocks :=
      chain_in_view (C := gj 𝒱 v (τ.st (τ.slotOf t'))) (t := τ.st (τ.slotOf t'))
        (t' := τ.st (τ.slotOf t')) hSync hNF hHB hcmSlott'
        hpb hv (by rw [Timing.slotOf_st]; exact h1slott')
        (by rw [Timing.slotOf_st]; exact hgst_slott') hBne hBsafe'
        hv (by rw [Timing.slotOf_st]) (Block.Ancestor.refl B)
    -- M4 at candidate slot `s' := slot t'`.
    have hrange : τ.slotOf t' ∈ Finset.Icc (τ.fslot et' + 1) (τ.slotOf t') := by
      rw [Finset.mem_Icc]
      refine ⟨?_, le_refl _⟩
      -- `fslot et' + 1 ≤ slot t'`: `fslot et' + 1 ≤ fslot (et' + 1) ≤ slot t'`.
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

end Theorems

end FastConfirmation.LMDGhost

end
