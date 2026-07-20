import Mathlib.Data.Nat.Basic

/-!
# Core / Model / Time

The discrete temporal substrate for the Fast Confirmation Rule. Following
arXiv:2405.00549, time is a single linearly-ordered quantity; slots and epochs
are projections of it. The safety proofs consume *no metric* on time beyond the
slot lattice and the `gst` comparisons, so everything here is `ℕ`.
-/

namespace FastConfirmation

/-- A slot index. -/
abbrev Slot := ℕ
/-- An epoch index. -/
abbrev Epoch := ℕ
/-- Wall-clock time (discrete). -/
abbrev Time := ℕ

/-- Protocol timing parameters: slots-per-epoch `slotsPerEpoch`, slot duration
    `slotDur`, and the (network) global stabilization time `gst`. -/
structure Timing where
  slotsPerEpoch : ℕ
  slotDur : ℕ
  gst : Time
  hSlotsPerEpoch : 0 < slotsPerEpoch
  hSlot : 0 < slotDur

namespace Timing

variable (τ : Timing)

/-- The slot containing instant `t`. -/
def slotOf (t : Time) : Slot := t / τ.slotDur
/-- The start instant of slot `s`. -/
def st (s : Slot) : Time := s * τ.slotDur
/-- The epoch of slot `s`. -/
def epochOf (s : Slot) : Epoch := s / τ.slotsPerEpoch
/-- First slot of epoch `e`. -/
def fslot (e : Epoch) : Slot := e * τ.slotsPerEpoch
/-- Last slot of epoch `e`. -/
def lslot (e : Epoch) : Slot := e * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1)
/-- `t` is at or after the global stabilization time. -/
def AfterGST (t : Time) : Prop := τ.gst ≤ t

end Timing

end FastConfirmation
