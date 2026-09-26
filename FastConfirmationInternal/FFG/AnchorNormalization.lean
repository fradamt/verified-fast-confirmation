module
public import FastConfirmationModel
public import Mathlib.Tactic

@[expose] public section

/-!
Anchor checkpoint normalization identifies checkpoints at or before the trusted anchor.
This is an FFG interpretation helper. Executable handlers and wire attestations
continue to read raw checkpoints. The lemmas below separate epoch comparisons
from checkpoint equality and strict global checkpoint updates.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Interpret an anchor-era checkpoint as the trusted anchor. This operation
must not replace raw state in a fork-choice handler. -/
def normalizeAnchorCheckpoint (anchor c : Checkpoint Root) : Checkpoint Root :=
  if c.epoch ≤ anchor.epoch then anchor else c

namespace normalizeAnchorCheckpoint

@[simp] theorem anchor (a : Checkpoint Root) : normalizeAnchorCheckpoint a a = a := by
  simp [normalizeAnchorCheckpoint]

@[simp] theorem idempotent (a c : Checkpoint Root) :
    normalizeAnchorCheckpoint a (normalizeAnchorCheckpoint a c) =
      normalizeAnchorCheckpoint a c := by
  by_cases h : c.epoch ≤ a.epoch <;> simp [normalizeAnchorCheckpoint, h]

/-- Normalization changes an epoch only below a non-genesis anchor. -/
theorem epoch (a c : Checkpoint Root) :
    (normalizeAnchorCheckpoint a c).epoch = max a.epoch c.epoch := by
  by_cases h : c.epoch ≤ a.epoch
  · simp [normalizeAnchorCheckpoint, h]
  · simp [normalizeAnchorCheckpoint, h, max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

/-- A genesis stub can change its root, but not its epoch. -/
theorem genesis_epoch {a : Checkpoint Root} (ha : a.epoch = GENESIS_EPOCH)
    (c : Checkpoint Root) :
    (normalizeAnchorCheckpoint a c).epoch = c.epoch := by
  rw [epoch, ha]
  simp [GENESIS_EPOCH]

/-- The raw `+2` filter comparison is unchanged for genesis anchors. -/
theorem genesis_source_age {a : Checkpoint Root} (ha : a.epoch = GENESIS_EPOCH)
    (c : Checkpoint Root) (e : Epoch) :
    ((normalizeAnchorCheckpoint a c).epoch + 2 ≥ e) ↔ (c.epoch + 2 ≥ e) := by
  rw [genesis_epoch ha]

/-- All three raw justified-filter alternatives are unchanged at genesis. -/
theorem genesis_justified_filter {a : Checkpoint Root}
    (ha : a.epoch = GENESIS_EPOCH) (source justified : Checkpoint Root) (e : Epoch) :
    (justified.epoch = GENESIS_EPOCH ∨
      (normalizeAnchorCheckpoint a source).epoch = justified.epoch ∨
      (normalizeAnchorCheckpoint a source).epoch + 2 ≥ e) ↔
    (justified.epoch = GENESIS_EPOCH ∨ source.epoch = justified.epoch ∨
      source.epoch + 2 ≥ e) := by
  rw [genesis_epoch ha]

/-- The genesis exemption protects the finalized-root comparison when a stub
root changes. A positive finalized epoch is unchanged by normalization. -/
theorem genesis_finalized_filter {a : Checkpoint Root}
    (ha : a.epoch = GENESIS_EPOCH) (c : Checkpoint Root) (boundaryRoot : Root) :
    ((normalizeAnchorCheckpoint a c).epoch = GENESIS_EPOCH ∨
      (normalizeAnchorCheckpoint a c).root = boundaryRoot) ↔
    (c.epoch = GENESIS_EPOCH ∨ c.root = boundaryRoot) := by
  by_cases h : c.epoch ≤ a.epoch
  · have hc : c.epoch = GENESIS_EPOCH := by
      rw [ha] at h
      exact Nat.eq_zero_of_le_zero h
    simp [normalizeAnchorCheckpoint, ha, hc]
  · simp [normalizeAnchorCheckpoint, h]

/-- Raw equality in the FCR observed-checkpoint guard implies interpreted
equality. The converse is not used. -/
theorem of_raw_eq (a : Checkpoint Root) {c d : Checkpoint Root} (h : c = d) :
    normalizeAnchorCheckpoint a c = normalizeAnchorCheckpoint a d :=
  congrArg (normalizeAnchorCheckpoint a) h

/-- Strict global checkpoint updates in `on_block` and PJF ignore all raw
candidates at or below the anchor, once the global epoch is at least the
anchor epoch. This applies to justified and finalized checkpoint updates. -/
theorem strict_update (a current candidate : Checkpoint Root)
    (hcurrent : a.epoch ≤ current.epoch) :
    (if current.epoch < candidate.epoch then candidate else current) =
      (if current.epoch < (normalizeAnchorCheckpoint a candidate).epoch then
        normalizeAnchorCheckpoint a candidate else current) := by
  by_cases h : candidate.epoch ≤ a.epoch
  · have hraw : ¬ current.epoch < candidate.epoch :=
      Nat.not_lt.mpr (h.trans hcurrent)
    have hanchor : ¬ current.epoch < a.epoch := Nat.not_lt.mpr hcurrent
    simp [normalizeAnchorCheckpoint, h, hraw, hanchor]
  · simp [normalizeAnchorCheckpoint, h]

end normalizeAnchorCheckpoint
end FastConfirmation.Spec

end
