import Mathlib.Tactic
import FastConfirmation.Paper.Core.Model.View
import FastConfirmation.Paper.Core.Model.Honest
import FastConfirmation.Paper.LMDGhost.Model.Weights
import FastConfirmation.Paper.LMDGhost.Proof.Blocks

/-!
# LMDGhost / Proof / Support

Persistence of honest LMD support across views and time — the workhorse of
Lemmas 1 and 6. An honest validator's effective (latest, non-equivocating) vote
is unforgeable (`HonestNoForgery`) hence `HonestCast`, so by `honestVoteUbiq` it
is delivered to *every* honest view. Combined with `noEquivocation` (so the
validator has a single vote per slot, in every honest view alike), the latest
vote at a fixed cutoff is the *same* in every honest view past the delivery
deadline. This makes honest support of a block monotone and view-independent,
which is exactly what the safety induction transfers.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- The effective vote of an honest non-equivocator equals its latest vote
    (the `FIL_eq` branch never fires). -/
theorem effectiveVote_eq_latest {V : View n P} {i : Validator n} {upTo : Slot}
    (hne : ¬ V.equivocator i) :
    V.effectiveVote i upTo = V.latestVote i upTo := by
  unfold View.effectiveVote
  rw [if_neg hne]

/-- A vote returned by `latestVote` belongs to the validator and respects the cutoff. -/
theorem latestVote_some_mem {V : View n P} {i : Validator n} {upTo : Slot}
    {gv : GhostVote n} (h : V.latestVote i upTo = some gv) :
    gv ∈ V.votesOf i ∧ gv.slot ≤ upTo := by
  unfold View.latestVote at h
  have hmem := List.argmax_mem h
  rw [Finset.mem_toList, Finset.mem_filter] at hmem
  exact hmem

/-- Every vote of `i` (slot `≤ upTo`) has slot at most the latest vote's slot. -/
theorem latestVote_is_max {V : View n P} {i : Validator n} {upTo : Slot}
    {gv : GhostVote n} (h : V.latestVote i upTo = some gv)
    {gv' : GhostVote n} (hmem : gv' ∈ V.votesOf i) (hslot : gv'.slot ≤ upTo) :
    gv'.slot ≤ gv.slot := by
  unfold View.latestVote at h
  have hmem' : gv' ∈ ((V.votesOf i).filter (fun g => g.slot ≤ upTo)).toList := by
    rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨hmem, hslot⟩
  exact List.le_of_mem_argmax hmem' h

/-- A vote of `i` present in a view (with slot `≤ upTo`) forces `latestVote` to be `some`. -/
theorem latestVote_isSome {V : View n P} {i : Validator n} {upTo : Slot}
    {gv : GhostVote n} (hmem : gv ∈ V.votesOf i) (hslot : gv.slot ≤ upTo) :
    (V.latestVote i upTo).isSome := by
  unfold View.latestVote
  rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]
  intro hnil
  have hmem' : gv ∈ ((V.votesOf i).filter (fun g => g.slot ≤ upTo)).toList := by
    rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨hmem, hslot⟩
  rw [hnil] at hmem'
  exact absurd hmem' (List.not_mem_nil)

/-- A non-equivocator casts at most one vote per slot. -/
theorem noEquiv_unique_slot {V : View n P} {i : Validator n} (hne : ¬ V.equivocator i)
    {gv₁ gv₂ : GhostVote n} (h₁ : gv₁ ∈ V.votesOf i) (h₂ : gv₂ ∈ V.votesOf i)
    (hslot : gv₁.slot = gv₂.slot) : gv₁ = gv₂ := by
  by_contra hne'
  exact hne ⟨gv₁, h₁, gv₂, h₂, hne', hslot⟩

/-- A GHOST vote in a view comes from a message in that view. -/
theorem mem_msg_of_mem_ghostVotes {V : View n P} {gv : GhostVote n}
    (h : gv ∈ V.ghostVotes) : ∃ m ∈ V.msgs, m.countsForLMD = true ∧ m.ghost = gv := by
  unfold View.ghostVotes at h
  rw [Finset.mem_image] at h
  obtain ⟨m, hm, hmg⟩ := h
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, hmg⟩

/-- **Honest-vote delivery / view independence.** A GHOST vote of an honest
    validator present in *one* honest view is present in *every* honest view at
    any time `t'` past a delivery deadline `st(s'+1)` (for any `s' ≥ gv.slot` that
    is itself past `gst`). (Unforgeability + `honestVoteUbiq` + monotonicity.) -/
theorem honest_vote_ubiquitous {fm : FaultModel n} {τ : Timing} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    {w : Validator n} {t : Time} {i : Validator n} {gv : GhostVote n}
    (hw : w ∈ fm.honest) (hi : i ∈ fm.honest) (hmem : gv ∈ (𝒱 w t).votesOf i)
    {w' : Validator n} {t' : Time} {s' : Slot} (hw' : w' ∈ fm.honest)
    (hcut : gv.slot ≤ s') (hge : τ.st (s' + 1) ≤ t') (hgst : τ.AfterGST (τ.st s')) :
    gv ∈ (𝒱 w' t').votesOf i := by
  simp only [View.votesOf, Finset.mem_filter] at hmem
  obtain ⟨hgvmem, hgveq⟩ := hmem
  obtain ⟨m, hmmsg, hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hgvmem
  have hval : m.ghost.validator ∈ fm.honest := by rw [hmg, hgveq]; exact hi
  have hcast : HonestCast fm 𝒱 τ m := hNF hw hmmsg hval
  have hmcut : m.ghost.slot ≤ s' := by rw [hmg]; exact hcut
  have hdeliv : m ∈ (𝒱 w' (τ.st (s' + 1))).msgs :=
    hSync.honestVoteUbiq hw' hcast hmcut hgst
  have hdeliv' : m ∈ (𝒱 w' t').msgs := (hSync.monotone w' _ _ hge).1 hdeliv
  simp only [View.votesOf, View.ghostVotes, Finset.mem_filter, Finset.mem_image]
  exact ⟨⟨m, ⟨hdeliv', hLMD⟩, hmg⟩, hgveq⟩

/-- **Honest votes are view-independent at a cutoff (post-GST).** For honest `i`, the
    votes of `i` of slot `≤ σ` are the *same* finite set in every honest view at any
    time `≥ st(σ+1)`, once **slot `σ` is past `gst`**. Every such vote is honest-cast
    (no forgery), so it is delivered to every honest view by its own deadline `≤ st(σ+1)`. -/
theorem votesOf_le_cutoff_view_indep {fm : FaultModel n} {τ : Timing} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    {i : Validator n} (hi : i ∈ fm.honest) {σ : Slot}
    (hgst : τ.AfterGST (τ.st σ))
    {w₁ : Validator n} {t₁ : Time} (hw₁ : w₁ ∈ fm.honest) (ht₁ : τ.st (σ + 1) ≤ t₁)
    {w₂ : Validator n} {t₂ : Time} (hw₂ : w₂ ∈ fm.honest) (ht₂ : τ.st (σ + 1) ≤ t₂) :
    ((𝒱 w₁ t₁).votesOf i).filter (fun gv => gv.slot ≤ σ)
      = ((𝒱 w₂ t₂).votesOf i).filter (fun gv => gv.slot ≤ σ) := by
  -- A symmetric transfer: any vote of `i` of slot ≤ σ in one honest view is in the other.
  have transfer : ∀ {wa : Validator n} {ta : Time}, wa ∈ fm.honest → τ.st (σ + 1) ≤ ta →
      ∀ {wb : Validator n} {tb : Time}, wb ∈ fm.honest → τ.st (σ + 1) ≤ tb →
      ∀ {gv : GhostVote n}, gv ∈ (𝒱 wa ta).votesOf i → gv.slot ≤ σ →
      gv ∈ (𝒱 wb tb).votesOf i := by
    intro wa ta hwa hta wb tb hwb htb gv hmem hslot
    exact honest_vote_ubiquitous hSync hNF hwa hi hmem hwb hslot htb hgst
  ext gv
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hslot⟩; exact ⟨transfer hw₁ ht₁ hw₂ ht₂ hmem hslot, hslot⟩
  · rintro ⟨hmem, hslot⟩; exact ⟨transfer hw₂ ht₂ hw₁ ht₁ hmem hslot, hslot⟩

/-- The latest vote at cutoff `σ` is view-independent across honest views (post-GST). -/
theorem latestVote_view_indep {fm : FaultModel n} {τ : Timing} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    {i : Validator n} (hi : i ∈ fm.honest) {σ : Slot}
    (hgst : τ.AfterGST (τ.st σ))
    {w₁ : Validator n} {t₁ : Time} (hw₁ : w₁ ∈ fm.honest) (ht₁ : τ.st (σ + 1) ≤ t₁)
    {w₂ : Validator n} {t₂ : Time} (hw₂ : w₂ ∈ fm.honest) (ht₂ : τ.st (σ + 1) ≤ t₂) :
    (𝒱 w₁ t₁).latestVote i σ = (𝒱 w₂ t₂).latestVote i σ := by
  unfold View.latestVote
  rw [votesOf_le_cutoff_view_indep hSync hNF hi hgst hw₁ ht₁ hw₂ ht₂]

/-- The effective vote at cutoff `σ` is view-independent across honest views (post-GST),
    using that honest validators never equivocate. -/
theorem effectiveVote_view_indep {fm : FaultModel n} {τ : Timing} {cm : Committees n}
    {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
    {pb : Weight} {flt : BlockFilter n P} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {i : Validator n} (hi : i ∈ fm.honest) {σ : Slot}
    (hgst : τ.AfterGST (τ.st σ))
    {w₁ : Validator n} {t₁ : Time} (hw₁ : w₁ ∈ fm.honest) (ht₁ : τ.st (σ + 1) ≤ t₁)
    {w₂ : Validator n} {t₂ : Time} (hw₂ : w₂ ∈ fm.honest) (ht₂ : τ.st (σ + 1) ≤ t₂) :
    (𝒱 w₁ t₁).effectiveVote i σ = (𝒱 w₂ t₂).effectiveVote i σ := by
  rw [effectiveVote_eq_latest (hHB.noEquivocation hi (w := w₁) (t := t₁)),
      effectiveVote_eq_latest (hHB.noEquivocation hi (w := w₂) (t := t₂))]
  exact latestVote_view_indep hSync hNF hi hgst hw₁ ht₁ hw₂ ht₂

/-- Honest support of a block at cutoff `σ` is view-independent (post-GST). -/
theorem supportsLMD_view_indep {fm : FaultModel n} {τ : Timing} {cm : Committees n}
    {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
    {pb : Weight} {flt : BlockFilter n P} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {i : Validator n} (hi : i ∈ fm.honest) {b' : Block n} {σ : Slot}
    (hgst : τ.AfterGST (τ.st σ))
    {w₁ : Validator n} {t₁ : Time} (hw₁ : w₁ ∈ fm.honest) (ht₁ : τ.st (σ + 1) ≤ t₁)
    {w₂ : Validator n} {t₂ : Time} (hw₂ : w₂ ∈ fm.honest) (ht₂ : τ.st (σ + 1) ≤ t₂) :
    (𝒱 w₁ t₁).supportsLMD b' i σ = (𝒱 w₂ t₂).supportsLMD b' i σ := by
  unfold View.supportsLMD
  rw [effectiveVote_view_indep hSync hNF hHB hi hgst hw₁ ht₁ hw₂ ht₂]

/-- **Honest votes are fork-choice-head votes.** Any vote of an honest validator `i`
    of slot `s` appearing in an honest view (with **slot `s` past `gst`**) names `i`'s
    own LMD-GHOST head at `st s`. (`votesHead` gives the head-vote; no-equivocation +
    delivery identify it with the observed vote.) -/
theorem honest_vote_is_head {fm : FaultModel n} {τ : Timing} {cm : Committees n}
    {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
    {pb : Weight} {flt : BlockFilter n P} {𝒱 : ViewFamily n P}
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {i : Validator n} (hi : i ∈ fm.honest) {w : Validator n} {t : Time} {gv : GhostVote n}
    (hw : w ∈ fm.honest) (hmem : gv ∈ (𝒱 w t).votesOf i)
    (hgst : τ.AfterGST (τ.st gv.slot)) :
    gv.block = forkChoiceHead τ (gj 𝒱 i (τ.st gv.slot)) boost pb flt (𝒱 i (τ.st gv.slot))
      (τ.st gv.slot) := by
  -- `i` is in the committee of `gv.slot` (it cast a vote there).
  have hcom : i ∈ cm.member gv.slot := hHB.votesInCommittee hi hmem
  obtain ⟨gv', hgv'mem, hgv'slot, hgv'block⟩ := hHB.votesHead hi hcom
  -- Deliver `gv` and `gv'` into a common honest view `𝒱 i (st (gv.slot + 1))`.
  have hge : τ.st (gv.slot + 1) ≤ τ.st (gv.slot + 1) := le_refl _
  have hgvmem' : gv ∈ (𝒱 i (τ.st (gv.slot + 1))).votesOf i :=
    honest_vote_ubiquitous hSync hNF hw hi hmem hi (le_refl _) hge hgst
  have hgv'mem' : gv' ∈ (𝒱 i (τ.st (gv.slot + 1))).votesOf i := by
    apply honest_vote_ubiquitous hSync hNF hi hi hgv'mem hi (s' := gv.slot) _ hge hgst
    exact le_of_eq hgv'slot
  have hsl : gv.slot = gv'.slot := hgv'slot.symm
  have heq : gv = gv' := noEquiv_unique_slot
    (hHB.noEquivocation hi (w := i) (t := τ.st (gv.slot + 1))) hgvmem' hgv'mem' hsl
  rw [heq, hgv'block, hsl]

/-- **`H` is view-independent at a cutoff (post-GST).** The honest support weight of a
    block computed in any honest view past the delivery deadline is the same. -/
theorem H_view_indep {fm : FaultModel n} {τ : Timing} {cm : Committees n}
    {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
    {pb : Weight} {flt : BlockFilter n P} {𝒱 : ViewFamily n P} (C : Anchor n)
    (hSync : Synchrony n P τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm gj boost pb flt 𝒱)
    {b' : Block n} {σ : Slot} (hgst : τ.AfterGST (τ.st σ))
    {w₁ : Validator n} {t₁ : Time} (hw₁ : w₁ ∈ fm.honest) (ht₁ : τ.st (σ + 1) ≤ t₁)
    {w₂ : Validator n} {t₂ : Time} (hw₂ : w₂ ∈ fm.honest) (ht₂ : τ.st (σ + 1) ≤ t₂) :
    H C cm fm (𝒱 w₁ t₁) b' σ = H C cm fm (𝒱 w₂ t₂) b' σ := by
  unfold H totalWeight
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro i hi
  rcases Classical.em (i ∈ fm.honest) with hih | hih
  · rw [supportsLMD_view_indep hSync hNF hHB hih hgst hw₁ ht₁ hw₂ ht₂]
  · simp only [hih, false_and]

end FastConfirmation.LMDGhost
