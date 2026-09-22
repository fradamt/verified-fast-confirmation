module
public import FastConfirmation.Paper.LMDGhost.Model.Confirm

@[expose] public section

/-!
# LMDGhost / Model / Rule

Algorithm 4 (the LMD-GHOST confirmation rule) and its security guard.
`highestConfirmedSinceEpoch` takes the highest-slot block that is LMD-GHOST-safe
in `v`'s view at the start of some slot in `[fslot e + 1, slot(t)]` (each block
evaluated at its slot's start, anchored at `gj` there), defaulting to genesis.
`isConfirmed b t` holds when `b` is an ancestor of that block for epoch `t-1`.
`gj` (the greatest-justified balance-anchor provider) is an abstract parameter,
realized with checkpoints by the HFC layer.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

open Classical in
/-- Algorithm 4: highest-slot LMD-GHOST-safe block since the 2nd slot of epoch `e`. -/
noncomputable def highestConfirmedSinceEpoch (τ : Timing) (fm : FaultModel n) (cm : Committees n)
    (pb : Weight) (gj : ViewFamily n P → Validator n → Time → Anchor n)
    (𝒱 : ViewFamily n P) (v : Validator n) (e : Epoch) (t : Time) : Block n :=
  let cand : Finset (Block n) :=
    (Finset.Icc (τ.fslot e + 1) (τ.slotOf t)).biUnion (fun s' =>
      (𝒱 v (τ.st s')).blocks.filter (fun b' =>
        isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s')) (𝒱 v (τ.st s')) b' (τ.st s')))
  match cand.toList.argmax (·.slot) with
  | some b => b
  | none => Block.genesis

/-- Algorithm 4: `b` is confirmed iff it is an ancestor of the highest confirmed
    block of the previous epoch. -/
def isConfirmed (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (gj : ViewFamily n P → Validator n → Time → Anchor n)
    (𝒱 : ViewFamily n P) (v : Validator n) (b : Block n) (t : Time) : Prop :=
  b ≼ highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v (τ.epochOf (τ.slotOf t) - 1) t

/-- Security guard `sg(b,t)`: `b`'s epoch is recent and `gst` precedes the first
    slot of the previous epoch (Theorem 1's guard). -/
def sg (τ : Timing) (b : Block n) (t : Time) : Prop :=
  τ.epochOf (τ.slotOf t) ≤ τ.epochOf b.slot + 1 ∧
    τ.AfterGST (τ.st (τ.fslot (τ.epochOf (τ.slotOf t) - 1)))

end FastConfirmation.LMDGhost

end
