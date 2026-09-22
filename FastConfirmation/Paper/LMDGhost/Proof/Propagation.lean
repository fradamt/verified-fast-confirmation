module
public import Mathlib.Tactic
public import FastConfirmation.Paper.LMDGhost.Proof.Blocks

@[expose] public section

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

end
