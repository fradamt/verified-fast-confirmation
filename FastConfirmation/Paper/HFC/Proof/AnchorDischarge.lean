module
public import FastConfirmation.Paper.HFC.Proof.Justification

@[expose] public section

/-!
# HFC / Proof / AnchorDischarge

**Discharging the GU-anchor conjunct of `GreatestJustifiedAnchorInputs`** from the paper's actual
FFG interface, rather than carrying it as a bespoke standalone assumption.

In arXiv:2405.00549 the previous-epoch anchor `gjblock(b)` (epoch `epoch(b)−1`, on `chain(b)`) is
justified in *every* honest view because (i) the confirmation rule re-roots at it as a
**precondition** (Algorithm 1, l.2349: `epoch(gjblock(b)) = epoch(t)−1`), and (ii) its justifying
FFG votes are **on-chain in `b`'s ancestry** (`∈ AU(b)`) and therefore reach every honest view by
*block* delivery (§2.2.1; the paper axiomatizes `AU(b)`'s properties at l.280–281). This is *not*
certificate formation and *not* backward canonicity — the anchor predates `b`'s canonicity, so it is
delivered structurally, not re-derived.

This file proves `GreatestJustifiedAnchorInputs` from the active AU interface:
* `OnChainAnchorInterface` — honest-proposer known-vote inclusion, block availability,
  payload-readability, and AU realization.
* `GreatestJustifiedAnchorPrecondition` — the confirmation rule's GU-anchor check (Algorithm 1).
* `greatestJustifiedAnchorInputs_of_interface` — the GU conjunct follows from AU realization and
  derived visibility applied to the precondition; the greatest-finalized realization stays the
  carried Gasper realization invariant.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **`GreatestJustifiedAnchorInputs` is discharged** from the paper's FFG interface. Its GU-anchor
    conjunct follows by applying `OnChainAnchorInterface.justified` to the confirmation precondition
    (`GreatestJustifiedAnchorPrecondition`): `gjblock(B)` is locally justified, realized as an AU
    fact on `chain(B)`, and then visible in every honest view. The greatest-finalized realization is
    the carried Gasper realization invariant (`hGF`), not derivable in the weight-only model. -/
theorem greatestJustifiedAnchorInputs_of_interface {C : Anchor n} {fm : FaultModel n} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} {B : Block n} {t : Time}
    (hdel : OnChainAnchorInterface C fm τ 𝒱 B t)
    (hpre : GreatestJustifiedAnchorPrecondition C fm τ 𝒱 B t)
    (hGF : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
      (greatestFinalized C (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt C τ (𝒱 w t') t') :
    GreatestJustifiedAnchorInputs C fm τ 𝒱 B t := by
  obtain ⟨GUc, hep, hble, v, hv, hjust⟩ := hpre
  intro w hw t' ht'
  exact ⟨⟨GUc, hdel.justified hble ⟨v, hv, hjust⟩ hw ht', hep, hble⟩, hGF hw ht'⟩

end FastConfirmation.HFC

end
