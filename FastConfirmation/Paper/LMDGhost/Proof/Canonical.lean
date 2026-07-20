import Mathlib.Tactic
import FastConfirmation.Paper.Core.Model.ForkChoice
import FastConfirmation.Paper.LMDGhost.Proof.Blocks
import FastConfirmation.Paper.LMDGhost.Proof.Positivity
import FastConfirmation.Paper.LMDGhost.Proof.Support
import FastConfirmation.Paper.LMDGhost.Proof.Weights

/-!
# LMDGhost / Proof / Canonical

Toward Lemma 2 (GHOST canonicality). This file builds the structural facts about
`eligibleChildren`/`ghostStep`/`ghostAux` and the `List.argmax` tie-break. The
key lemma `argmax_eq_of_strict_dominant` says a *strictly* dominant element is
returned by `argmax` regardless of list order — so Definition 8's strict
inequality makes the tie-break irrelevant on the safe path.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- `totalWeight` depends on the anchor only through its balance function. -/
theorem totalWeight_congr_bal {A A' : Anchor n} (h : A.bal = A'.bal) (X : Finset (Validator n)) :
    totalWeight A X = totalWeight A' X := by
  unfold totalWeight; rw [h]

/-- `latestSupportWeight` depends on the anchor only through its balance function. -/
theorem latestSupportWeight_congr_bal {A A' : Anchor n} (h : A.bal = A'.bal)
    (V : View n P) (upTo : Slot) (c : Block n) :
    latestSupportWeight A V upTo c = latestSupportWeight A' V upTo c := by
  unfold latestSupportWeight; exact totalWeight_congr_bal h _

/-- `boostWeight` depends on the anchor only through its balance function. -/
theorem boostWeight_congr_bal {A A' : Anchor n} (h : A.bal = A'.bal)
    (boost : ProposerBoost n P) (pb : Weight) (V : View n P) (t : Time) (c : Block n) :
    boostWeight A boost pb V t c = boostWeight A' boost pb V t c := by
  unfold boostWeight
  cases boost.proposalAt V t with
  | none => rfl
  | some bp =>
    split
    · rw [totalWeight_congr_bal h]
    · rfl

/-- `childWeight` depends on the anchor only through its balance function. -/
theorem childWeight_congr_bal {A A' : Anchor n} (h : A.bal = A'.bal)
    (boost : ProposerBoost n P) (pb : Weight) (V : View n P) (t : Time) (upTo : Slot)
    (c : Block n) :
    childWeight A boost pb V t upTo c = childWeight A' boost pb V t upTo c := by
  unfold childWeight
  rw [latestSupportWeight_congr_bal h, boostWeight_congr_bal h]

/-- `ghostStep` depends on the anchor only through its balance function. -/
theorem ghostStep_congr_bal {τ : Timing} {A A' : Anchor n} (h : A.bal = A'.bal)
    (boost : ProposerBoost n P) (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time)
    (b : Block n) :
    ghostStep τ A boost pb flt V t b = ghostStep τ A' boost pb flt V t b := by
  unfold ghostStep
  have hfun : childWeight A boost pb V t (τ.slotOf t - 1)
      = childWeight A' boost pb V t (τ.slotOf t - 1) := by
    funext c; exact childWeight_congr_bal h boost pb V t (τ.slotOf t - 1) c
  rw [hfun]

/-- `ghostAux` depends on the anchor only through its balance function. -/
theorem ghostAux_congr_bal {τ : Timing} {A A' : Anchor n} (h : A.bal = A'.bal)
    (boost : ProposerBoost n P) (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time) :
    ∀ (fuel : ℕ) (b : Block n),
      ghostAux τ A boost pb flt V t fuel b = ghostAux τ A' boost pb flt V t fuel b := by
  intro fuel
  induction fuel with
  | zero => intro b; rfl
  | succ fuel ih =>
    intro b
    unfold ghostAux
    rw [ghostStep_congr_bal h]
    cases ghostStep τ A' boost pb flt V t b with
    | none => rfl
    | some best => exact ih best

/-- **`forkChoiceHead` depends on the anchor only through its balance function.** -/
theorem forkChoiceHead_congr_bal {τ : Timing} {A A' : Anchor n} (h : A.bal = A'.bal)
    (boost : ProposerBoost n P) (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time) :
    forkChoiceHead τ A boost pb flt V t = forkChoiceHead τ A' boost pb flt V t := by
  unfold forkChoiceHead
  exact ghostAux_congr_bal h boost pb flt V t (τ.slotOf t + 1) Block.genesis

/-- A strictly dominant element is the `argmax` (the tie-break never matters). -/
theorem argmax_eq_of_strict_dominant {α β : Type*} [LinearOrder β] {f : α → β} {l : List α}
    {c : α} (hc : c ∈ l) (hdom : ∀ a ∈ l, a ≠ c → f a < f c) : l.argmax f = some c := by
  have hne_nil : l ≠ [] := List.ne_nil_of_mem hc
  rcases ho : l.argmax f with _ | m
  · rw [List.argmax_eq_none] at ho; exact absurd ho hne_nil
  · have hmem := List.argmax_mem ho
    have hle := List.le_of_mem_argmax hc ho
    have hmc : m = c := by
      by_contra hne
      exact absurd hle (not_le.mpr (hdom m hmem hne))
    exact congrArg some hmc

/-- Membership in `eligibleChildren`. -/
theorem mem_eligibleChildren {τ : Timing} {flt : BlockFilter n P} {V : View n P} {t : Time}
    {b b' : Block n} :
    b' ∈ eligibleChildren τ flt V t b ↔
      b' ∈ V.blocks ∧ b'.parent? = some b ∧ b'.WellFormed ∧ b'.slot ≤ τ.slotOf t ∧ flt V t b' := by
  simp only [eligibleChildren, Finset.mem_filter]

/-- The proposer boost is nonnegative. -/
theorem boostWeight_nonneg (A : Anchor n) (boost : ProposerBoost n P) (pb : Weight)
    (V : View n P) (t : Time) (c : Block n) (hpb : 0 ≤ pb) :
    0 ≤ boostWeight A boost pb V t c := by
  unfold boostWeight
  split
  · split
    · exact mul_nonneg hpb (totalWeight_nonneg A _)
    · exact le_refl 0
  · exact le_refl 0

/-- The proposer boost is at most `Wp` (one current-slot boost). -/
theorem boostWeight_le_Wp (A : Anchor n) (boost : ProposerBoost n P) (pb : Weight)
    (V : View n P) (t : Time) (c : Block n) (hpb : 0 ≤ pb) :
    boostWeight A boost pb V t c ≤ Wp A pb := by
  unfold boostWeight Wp
  split
  · split
    · exact le_refl _
    · exact mul_nonneg hpb (totalWeight_nonneg A _)
  · exact mul_nonneg hpb (totalWeight_nonneg A _)

/-- An effective vote belongs to the validator's votes and respects the cutoff. -/
theorem effectiveVote_some_mem {V : View n P} {i : Validator n} {upTo : Slot}
    {gv : GhostVote n} (h : V.effectiveVote i upTo = some gv) :
    gv ∈ V.votesOf i ∧ gv.slot ≤ upTo := by
  unfold View.effectiveVote at h
  split at h
  · simp at h
  · unfold View.latestVote at h
    have hmem := List.argmax_mem h
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem

/-- **Reconciliation.** Under `ViewValid`, fork-choice support over `univ` equals the
    committee-based support `S` (every supporter lies in the block's committee range). -/
theorem latestSupportWeight_eq_S (A : Anchor n) (cm : Committees n) (V : View n P)
    (c : Block n) (upTo : Slot) (hVV : ViewValid cm V) (hc : c.WellFormed)
    (hcne : c ≠ Block.genesis) :
    latestSupportWeight A V upTo c = S A cm V c upTo := by
  have hpsp : c.psPlus1 ≤ c.slot := by
    cases c with
    | genesis => exact absurd rfl hcne
    | mk bid p s =>
      have hlt : p.slot < s := hc.1
      simp only [Block.psPlus1, Block.parentSlot, Block.slot]
      exact hlt
    | mkWithVotes bid p s votes =>
      have hlt : p.slot < s := hc.1
      simp only [Block.psPlus1, Block.parentSlot, Block.slot]
      exact hlt
  unfold latestSupportWeight S
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsupp
    refine ⟨?_, hsupp⟩
    unfold View.supportsLMD at hsupp
    cases hev : V.effectiveVote i upTo with
    | none => rw [hev] at hsupp; simp at hsupp
    | some gv =>
      rw [hev] at hsupp
      obtain ⟨hmem, hslot⟩ := effectiveVote_some_mem hev
      simp only [View.votesOf, Finset.mem_filter] at hmem
      obtain ⟨m, hmmsg, _hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hmem.1
      obtain ⟨hcom, hbs, hbwf⟩ := hVV m hmmsg
      rw [hmg] at hcom hbs hbwf
      have hanc : c ≼ gv.block := isAncestorOf_imp hsupp
      have hcs : c.slot ≤ gv.block.slot := slot_le_of_ancestor hanc hbwf
      rw [committeeUnion, Finset.mem_biUnion]
      refine ⟨gv.slot, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨le_trans hpsp (le_trans hcs hbs), hslot⟩
      · rw [hmem.2] at hcom; exact hcom
  · intro h; exact h.2

/-- The chain-child's GHOST weight is at least its honest support `H`. -/
theorem childWeight_ge_H (τ : Timing) (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (boost : ProposerBoost n P) (pb : Weight) (V : View n P) (t : Time) (c : Block n)
    (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hcwf : c.WellFormed) (hcne : c ≠ Block.genesis) :
    H A cm fm V c (τ.slotOf t - 1) ≤ childWeight A boost pb V t (τ.slotOf t - 1) c := by
  unfold childWeight
  rw [latestSupportWeight_eq_S A cm V c (τ.slotOf t - 1) hVV hcwf hcne]
  have h1 := H_le_S A cm fm V c (τ.slotOf t - 1)
  have h2 := boostWeight_nonneg A boost pb V t c hpb
  linarith

/-- Honest supporters of two incompatible siblings are disjoint, so their honest
    support weights sum to at most the honest committee weight `J`. -/
theorem honest_support_disjoint_sum (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) {c c' : Block n} (s : Slot)
    (hpsp : c'.psPlus1 = c.psPlus1) (hincomp : ¬ c ~ c') :
    H A cm fm V c s + H A cm fm V c' s ≤ J A cm fm c s := by
  simp only [H, J, totalWeight]
  rw [hpsp]
  have hdisj : Disjoint
      ((committeeUnion cm c.psPlus1 s).filter
        (fun i => i ∈ fm.honest ∧ V.supportsLMD c i s = true))
      ((committeeUnion cm c.psPlus1 s).filter
        (fun i => i ∈ fm.honest ∧ V.supportsLMD c' i s = true)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter] at hi hi'
    exact honest_supports_at_most_one_sibling V i s hincomp ⟨hi.2.2, hi'.2.2⟩
  rw [← Finset.sum_union hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨hu, hh, _⟩ | ⟨hu, hh, _⟩ <;> exact ⟨hu, hh⟩
  · exact fun i _ _ => (A.hpos i).le

/-- A sibling's GHOST weight is bounded by `W − H_{c} + Wp` (it can claim at most the
    non-`c*`-honest committee weight plus the adversary plus one proposer boost). -/
theorem childWeight_sibling_le (τ : Timing) (A : Anchor n) (cm : Committees n)
    (fm : FaultModel n) (boost : ProposerBoost n P) (pb : Weight) (V : View n P) (t : Time)
    {c c' : Block n} (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hc'wf : c'.WellFormed)
    (hc'ne : c' ≠ Block.genesis) (hpsp : c'.psPlus1 = c.psPlus1) (hincomp : ¬ c ~ c') :
    childWeight A boost pb V t (τ.slotOf t - 1) c'
      ≤ W A cm c (τ.slotOf t - 1) - H A cm fm V c (τ.slotOf t - 1) + Wp A pb := by
  set s := τ.slotOf t - 1 with hs
  unfold childWeight
  rw [latestSupportWeight_eq_S A cm V c' s hVV hc'wf hc'ne]
  have hSsplit := S_eq_H_add_adv A cm fm V c' s
  have hadv := adv_support_le_committee A cm fm V c' s
  have hWsplit := W_eq_J_add_adv A cm fm c' s
  have hdisj := honest_support_disjoint_sum A cm fm V s hpsp hincomp
  have hWeq : W A cm c' s = W A cm c s := by unfold W; rw [hpsp]
  have hJeq : J A cm fm c' s = J A cm fm c s := by unfold J; rw [hpsp]
  have hboost := boostWeight_le_Wp A boost pb V t c' hpb
  have hSle : S A cm V c' s ≤ W A cm c s - H A cm fm V c s := by
    linarith [hSsplit, hadv, hWsplit, hdisj, hWeq, hJeq]
  linarith [hSle, hboost]

/-- A successful GHOST step lands on an eligible child. -/
theorem ghostStep_some_mem {τ : Timing} {A : Anchor n} {boost : ProposerBoost n P} {pb : Weight}
    {flt : BlockFilter n P} {V : View n P} {t : Time} {y best : Block n}
    (h : ghostStep τ A boost pb flt V t y = some best) :
    best ∈ eligibleChildren τ flt V t y := by
  unfold ghostStep at h
  have hm := List.argmax_mem h
  rwa [Finset.mem_toList] at hm

/-- The GHOST head is always a descendant of the start node. -/
theorem ghostAux_ge (τ : Timing) (A : Anchor n) (boost : ProposerBoost n P) (pb : Weight)
    (flt : BlockFilter n P) (V : View n P) (t : Time) (fuel : ℕ) (y : Block n) :
    y ≼ ghostAux τ A boost pb flt V t fuel y := by
  induction fuel generalizing y with
  | zero => exact Block.Ancestor.refl _
  | succ fuel ih =>
    unfold ghostAux
    cases h : ghostStep τ A boost pb flt V t y with
    | none => exact Block.Ancestor.refl _
    | some best =>
      have hmem := ghostStep_some_mem h
      rw [mem_eligibleChildren] at hmem
      exact Block.Ancestor.trans (parent_ancestor hmem.2.1) (ih best)

/-- **Lemma 2 step.** At a node `x` strictly above `b`, GHOST moves to the child of
    `x` on the path to `b` (the chain-child strictly dominates every sibling). -/
theorem ghostStep_eq_chain_child (τ : Timing) (A : Anchor n) (cm : Committees n)
    (fm : FaultModel n) (pb : Weight) (boost : ProposerBoost n P) (V : View n P) (t : Time)
    {x b : Block n} (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hbwf : b.WellFormed)
    (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2)
    (hxb : x ≼ b) (hne : x ≠ b) :
    ∃ c, c.parent? = some x ∧ x ≼ c ∧ c ≼ b ∧
      ghostStep τ A boost pb trivialFilter V t x = some c := by
  obtain ⟨c, hpar, hxc, hcb⟩ := chain_child hxb hne
  have hcwf : c.WellFormed := WellFormed_of_ancestor hcb hbwf
  have hcne : c ≠ Block.genesis := by
    intro hc; rw [hc] at hpar; simp [Block.parent?] at hpar
  have hcslot : c.slot ≤ τ.slotOf t := le_trans (slot_le_of_ancestor hcb hbwf) hslot
  refine ⟨c, hpar, hxc, hcb, ?_⟩
  unfold ghostStep
  apply argmax_eq_of_strict_dominant
  · rw [Finset.mem_toList, mem_eligibleChildren]
    exact ⟨hchain hcb, hpar, hcwf, hcslot, trivial⟩
  · intro c' hc'mem hc'ne
    rw [Finset.mem_toList, mem_eligibleChildren] at hc'mem
    obtain ⟨_, hc'par, hc'wf, _, _⟩ := hc'mem
    have hincomp : ¬ c ~ c' := siblings_incompatible hcwf hc'wf hpar hc'par (Ne.symm hc'ne)
    have hpsp : c'.psPlus1 = c.psPlus1 := by
      rw [psPlus1_eq_of_parent hc'par, psPlus1_eq_of_parent hpar]
    have hc'gen : c' ≠ Block.genesis := by
      intro hg; rw [hg] at hc'par; simp [Block.parent?] at hc'par
    have hge := childWeight_ge_H τ A cm fm boost pb V t c hpb hVV hcwf hcne
    have hHmaj := hmaj hcb hcne
    have hle := childWeight_sibling_le τ A cm fm boost pb V t hpb hVV hc'wf hc'gen hpsp hincomp
    linarith [hge, hHmaj, hle]

/-- The GHOST traversal from any `x ≼ b` (with enough fuel) reaches `b`. -/
theorem b_le_ghostAux (τ : Timing) (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (pb : Weight) (boost : ProposerBoost n P) (V : View n P) (t : Time) {b : Block n}
    (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hbwf : b.WellFormed)
    (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2) :
    ∀ (fuel : ℕ) (x : Block n), x ≼ b → b.slot ≤ x.slot + fuel →
      b ≼ ghostAux τ A boost pb trivialFilter V t fuel x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hxb hbnd
    have hxle : x.slot ≤ b.slot := slot_le_of_ancestor hxb hbwf
    have heq : x = b := eq_of_ancestor_slot hxb hbwf (le_antisymm hxle (by simpa using hbnd))
    rw [heq]; unfold ghostAux; exact Block.Ancestor.refl _
  | succ fuel ih =>
    intro x hxb hbnd
    by_cases hxe : x = b
    · rw [hxe]; exact ghostAux_ge τ A boost pb trivialFilter V t (fuel + 1) b
    · obtain ⟨c, hpar, _, hcb, hstep⟩ :=
        ghostStep_eq_chain_child τ A cm fm pb boost V t hpb hVV hbwf hchain hslot hmaj hxb hxe
      have hcwf : c.WellFormed := WellFormed_of_ancestor hcb hbwf
      have hcgt : x.slot < c.slot := parent_slot_lt hpar hcwf
      have hbnd' : b.slot ≤ c.slot + fuel := by
        calc b.slot ≤ x.slot + (fuel + 1) := hbnd
          _ = (x.slot + 1) + fuel := by ring
          _ ≤ c.slot + fuel := Nat.add_le_add_right hcgt fuel
      unfold ghostAux
      rw [hstep]
      exact ih c hcb hbnd'

/-- Filtered analogue of `ghostStep_eq_chain_child`: with `flt` eligible along
    `b`'s chain, the chain-child still strictly dominates every sibling. -/
theorem ghostStep_eq_chain_child_filtered (τ : Timing) (A : Anchor n) (cm : Committees n)
    (fm : FaultModel n) (pb : Weight) (boost : ProposerBoost n P) (flt : BlockFilter n P)
    (V : View n P) (t : Time) {x b : Block n} (hpb : 0 ≤ pb) (hVV : ViewValid cm V)
    (hbwf : b.WellFormed) (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hflt : ∀ ⦃b'⦄, b' ≼ b → flt V t b')
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2)
    (hxb : x ≼ b) (hne : x ≠ b) :
    ∃ c, c.parent? = some x ∧ x ≼ c ∧ c ≼ b ∧
      ghostStep τ A boost pb flt V t x = some c := by
  obtain ⟨c, hpar, hxc, hcb⟩ := chain_child hxb hne
  have hcwf : c.WellFormed := WellFormed_of_ancestor hcb hbwf
  have hcne : c ≠ Block.genesis := by
    intro hc; rw [hc] at hpar; simp [Block.parent?] at hpar
  have hcslot : c.slot ≤ τ.slotOf t := le_trans (slot_le_of_ancestor hcb hbwf) hslot
  refine ⟨c, hpar, hxc, hcb, ?_⟩
  unfold ghostStep
  apply argmax_eq_of_strict_dominant
  · rw [Finset.mem_toList, mem_eligibleChildren]
    exact ⟨hchain hcb, hpar, hcwf, hcslot, hflt hcb⟩
  · intro c' hc'mem hc'ne
    rw [Finset.mem_toList, mem_eligibleChildren] at hc'mem
    obtain ⟨_, hc'par, hc'wf, _, _⟩ := hc'mem
    have hincomp : ¬ c ~ c' := siblings_incompatible hcwf hc'wf hpar hc'par (Ne.symm hc'ne)
    have hpsp : c'.psPlus1 = c.psPlus1 := by
      rw [psPlus1_eq_of_parent hc'par, psPlus1_eq_of_parent hpar]
    have hc'gen : c' ≠ Block.genesis := by
      intro hg; rw [hg] at hc'par; simp [Block.parent?] at hc'par
    have hge := childWeight_ge_H τ A cm fm boost pb V t c hpb hVV hcwf hcne
    have hHmaj := hmaj hcb hcne
    have hle := childWeight_sibling_le τ A cm fm boost pb V t hpb hVV hc'wf hc'gen hpsp hincomp
    linarith [hge, hHmaj, hle]

/-- Filtered analogue of `b_le_ghostAux`. -/
theorem b_le_ghostAux_filtered (τ : Timing) (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (pb : Weight) (boost : ProposerBoost n P) (flt : BlockFilter n P) (V : View n P) (t : Time)
    {b : Block n} (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hbwf : b.WellFormed)
    (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hflt : ∀ ⦃b'⦄, b' ≼ b → flt V t b')
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2) :
    ∀ (fuel : ℕ) (x : Block n), x ≼ b → b.slot ≤ x.slot + fuel →
      b ≼ ghostAux τ A boost pb flt V t fuel x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hxb hbnd
    have hxle : x.slot ≤ b.slot := slot_le_of_ancestor hxb hbwf
    have heq : x = b := eq_of_ancestor_slot hxb hbwf (le_antisymm hxle (by simpa using hbnd))
    rw [heq]; unfold ghostAux; exact Block.Ancestor.refl _
  | succ fuel ih =>
    intro x hxb hbnd
    by_cases hxe : x = b
    · rw [hxe]; exact ghostAux_ge τ A boost pb flt V t (fuel + 1) b
    · obtain ⟨c, hpar, _, hcb, hstep⟩ :=
        ghostStep_eq_chain_child_filtered τ A cm fm pb boost flt V t hpb hVV hbwf hchain hslot
          hflt hmaj hxb hxe
      have hcwf : c.WellFormed := WellFormed_of_ancestor hcb hbwf
      have hcgt : x.slot < c.slot := parent_slot_lt hpar hcwf
      have hbnd' : b.slot ≤ c.slot + fuel := by
        calc b.slot ≤ x.slot + (fuel + 1) := hbnd
          _ = (x.slot + 1) + fuel := by ring
          _ ≤ c.slot + fuel := Nat.add_le_add_right hcgt fuel
      unfold ghostAux
      rw [hstep]
      exact ih c hcb hbnd'

/-- **Lemma 2, filter-generic form.** If every ancestor of `b` (in view) has an honest
    majority and stays `flt`-eligible, then `b` is on the LMD-GHOST head. -/
theorem head_of_Hmajority_filtered (τ : Timing) (A : Anchor n) (cm : Committees n)
    (fm : FaultModel n) (pb : Weight) (boost : ProposerBoost n P) (flt : BlockFilter n P)
    (V : View n P) (t : Time) {b : Block n} (hpb : 0 ≤ pb) (hVV : ViewValid cm V)
    (hbwf : b.WellFormed) (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hflt : ∀ ⦃b'⦄, b' ≼ b → flt V t b')
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2) :
    b ≼ forkChoiceHead τ A boost pb flt V t := by
  unfold forkChoiceHead
  apply b_le_ghostAux_filtered τ A cm fm pb boost flt V t hpb hVV hbwf hchain hslot hflt hmaj
    (τ.slotOf t + 1) Block.genesis (genesis_ancestor b)
  simp only [Block.slot, Nat.zero_add]
  exact le_trans hslot (Nat.le_succ _)

/-- **Lemma 2.** If every ancestor of `b` (in view) has an honest majority, then `b`
    is on the LMD-GHOST head. -/
theorem head_of_Hmajority (τ : Timing) (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (pb : Weight) (boost : ProposerBoost n P) (V : View n P) (t : Time) {b : Block n}
    (hpb : 0 ≤ pb) (hVV : ViewValid cm V) (hbwf : b.WellFormed)
    (hchain : ∀ ⦃b'⦄, b' ≼ b → b' ∈ V.blocks) (hslot : b.slot ≤ τ.slotOf t)
    (hmaj : ∀ ⦃b'⦄, b' ≼ b → b' ≠ Block.genesis →
      H A cm fm V b' (τ.slotOf t - 1) > (W A cm b' (τ.slotOf t - 1) + Wp A pb) / 2) :
    b ≼ forkChoiceHead τ A boost pb trivialFilter V t := by
  unfold forkChoiceHead
  apply b_le_ghostAux τ A cm fm pb boost V t hpb hVV hbwf hchain hslot hmaj
    (τ.slotOf t + 1) Block.genesis (genesis_ancestor b)
  simp only [Block.slot, Nat.zero_add]
  exact le_trans hslot (Nat.le_succ _)

end FastConfirmation.LMDGhost
