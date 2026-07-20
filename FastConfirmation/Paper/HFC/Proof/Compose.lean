import FastConfirmation.Paper.LMDGhost.Proof.Rule
import FastConfirmation.Paper.HFC.TheoremStatements
import FastConfirmation.Paper.HFC.Proof.AnchorDischarge

/-!
# HFC / Proof / Compose

The §4 HFC confirmation-rule **safety**, obtained by reusing the filter-generic §3.1
engine at `flt := ffgFilter bal₀ τ`, `gj := gjFFG bal₀` (the constant FFG anchor),
reduced to the FFG never-filtered obligation `ConfirmedNotFFGFiltered`.

Because `gjFFG bal₀` is a *constant* `Stakes`, `AnchorsCoincide` and `StaticBalances`
hold by `rfl`, and the conclusion's per-validator anchor `gjFFG bal₀ 𝒱 w t'` is
*definitionally* `bal₀`, so no anchor reconciliation is needed — the §3.1 Safety proof
transports almost verbatim, with `NeverFiltered_trivial` replaced by the FFG
`ConfirmedNotFFGFiltered` premise (proved in `NeverFiltered.lean` from the local gate).
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- The constant FFG anchor coincides with itself: `AnchorsCoincide` is trivial. -/
theorem anchorsCoincide_gjFFG (bal₀ : Stakes n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) :
    AnchorsCoincide (gjFFG bal₀) 𝒱 fm τ bal₀ := fun _ _ _ => rfl

/-- `gjFFG bal₀` is a constant anchor, so `StaticBalances` holds by `rfl`. -/
theorem staticBalances_gjFFG (bal₀ : Stakes n) (𝒱 : ViewFamily n (FFGVote n)) :
    StaticBalances (gjFFG bal₀) 𝒱 := fun _ _ _ _ _ => rfl

variable {τ : Timing}

/-- **Safe ⇒ canonical at `ffgFilter` (the §4 reuse of the Lemma-7 bridge).** Mirror of
    `safe_canonical_from_engine` at `flt := ffgFilter bal₀ τ`, `gj := gjFFG bal₀`, taking
    the FFG `NeverFiltered` premise instead of `NeverFiltered_trivial`. -/
theorem hfc_canonical_from_engine (bal₀ : Stakes n)
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {boost : ProposerBoost n (FFGVote n)}
    {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {B : Block n} {s : Slot}
    (hv : v ∈ fm.honest) (hBwf : B.WellFormed) (hBslot : B.slot ≤ s) (h1 : 1 ≤ s)
    (hgst : τ.AfterGST (τ.st (s - 1)))
    (hsafe : isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) B (τ.st s))
    (hNFil : NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 B (τ.st s)) :
    ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st s ≤ t' →
      B ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  intro w t' hw ht'
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  have hcmC : CommitteeHonestMajority fm cm bal₀ := hcm (w := v) (t := τ.st s)
  have heng := head_safety_engine (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gjFFG bal₀)
    (boost := boost) (flt := ffgFilter bal₀ τ) (𝒱 := 𝒱) (C := bal₀) (v := v) (b := B)
    (t := τ.st s) hSync hNF hHB hVV hcmC hpb (anchorsCoincide_gjFFG bal₀ fm τ 𝒱) hv hBwf
    (by rw [hslots]; exact hBslot) (by rw [hslots]; exact h1) (by rw [hslots]; exact hgst)
    hsafe hNFil
  have hdeliv : τ.st (τ.slotOf (τ.st s)) ≤ t' := by rw [hslots]; exact ht'
  exact heng (w := w) (t' := t') hw hdeliv

/-- **§4 HFC Safety, modulo the FFG never-filtered obligation.** Given the §3.1 premises
    at `gj := gjFFG bal₀`, `flt := ffgFilter bal₀ τ`, an `isConfirmed` block `b`, and
    `ConfirmedNotFFGFiltered` (its safe descendants are never FFG-filtered — proved from the
    local gate in `NeverFiltered.lean`), `b` is on every honest LMD-GHOST-HFC head from some
    time on. The proof mirrors `proof_Theorem1_Safety`, swapping `NeverFiltered_trivial` for
    `ConfirmedNotFFGFiltered` and using that `gjFFG` is constant. -/
theorem hfc_safety_of_notFiltered (bal₀ : Stakes n)
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {boost : ProposerBoost n (FFGVote n)}
    {𝒱 : ViewFamily n (FFGVote n)}
    (hSync : Synchrony n (FFGVote n) τ fm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hVV : ViewsValid cm 𝒱)
    (hcm : ∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gjFFG bal₀ 𝒱 w t))
    (hpb : 0 ≤ pb)
    {v : Validator n} {b : Block n} {t : Time}
    (hv : v ∈ fm.honest) (hsg : sg τ b t)
    (hAS : FFG_AccountableSafety bal₀ fm 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hSGJ : SafeGreatestJustifiedAnchorInputs τ fm cm pb bal₀ 𝒱)
    (hconf : isConfirmed τ fm cm pb (gjFFG bal₀) 𝒱 v b t)
    (hCNF : ConfirmedNotFFGFiltered τ fm cm pb boost bal₀ 𝒱 v b) :
    ∃ t0 : Time, ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → t0 ≤ t' →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 w t') boost pb (ffgFilter bal₀ τ) (𝒱 w t') t' := by
  set e := τ.epochOf (τ.slotOf t) - 1 with he
  set B := highestConfirmedSinceEpoch τ fm cm pb (gjFFG bal₀) 𝒱 v e t with hB
  have hbB : b ≼ B := hconf
  rcases highestConfirmed_mem (τ := τ) (fm := fm) (cm := cm) (pb := pb) (gj := gjFFG bal₀)
      (𝒱 := 𝒱) v e t with hgen | ⟨s', hs', _hBblk, hBsafe⟩
  · rw [← hB] at hgen
    refine ⟨0, fun w t' _ _ => ?_⟩
    have : b = Block.genesis := by
      have := hbB; rw [hgen] at this; cases this with | refl => rfl
    rw [this]; exact genesis_ancestor _
  · rw [← hB] at hBsafe
    rw [Finset.mem_Icc] at hs'
    have hs'1 : 1 ≤ s' := le_trans (Nat.le_add_left 1 _) hs'.1
    have hslots' : τ.slotOf (τ.st s') = s' := Timing.slotOf_st τ s'
    have hgstS : τ.AfterGST (τ.st (s' - 1)) := by
      have hsg2 : τ.AfterGST (τ.st (τ.fslot e)) := hsg.2
      have hfle : τ.fslot e ≤ s' - 1 := Nat.le_pred_of_lt (Nat.lt_of_succ_le hs'.1)
      exact le_trans hsg2 (by exact_mod_cast Nat.mul_le_mul_right τ.slotDur hfle)
    by_cases hBne : B = Block.genesis
    · refine ⟨0, fun w t' _ _ => ?_⟩
      have : b = Block.genesis := by
        have := hbB; rw [hBne] at this; cases this with | refl => rfl
      rw [this]; exact genesis_ancestor _
    · have hcmC : CommitteeHonestMajority fm cm bal₀ := hcm (w := v) (t := τ.st s')
      obtain ⟨hBwf, hBslot0⟩ := safe_block_wf_slot (C := bal₀) (hVV _ _) hcmC hpb hBsafe hBne
      rw [hslots'] at hBslot0
      have hBslot : B.slot ≤ s' := le_trans hBslot0 (Nat.sub_le _ 1)
      -- gate / epoch-cover / GU-anchor inputs for the safe block `B` at `st s'`; the §4 RECENCY
      -- disjunct is now *proven* structurally in the never-filter (no recency premise).
      -- Gate / AU payload availability / GU-anchor realization inputs for the safe block `B`.
      obtain ⟨hgateB, _hAUB, hAnchorB⟩ :=
        hSGJ (w := v) hv (t' := τ.st s') (X := B) hBsafe
      have hNFB : NeverFilteredFromHead τ fm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱 B
          (τ.st s') :=
        hCNF hAS hnoequiv hByz hs'1 hgstS hbB hBsafe hgateB hAnchorB
      have hcanon := hfc_canonical_from_engine bal₀ hSync hNF hHB hVV hcm hpb hv hBwf hBslot
        hs'1 hgstS hBsafe hNFB
      refine ⟨τ.st s', fun w t' hw ht' => ?_⟩
      exact Block.Ancestor.trans hbB (hcanon hw ht')

end FastConfirmation.HFC
