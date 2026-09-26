module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.FFGCertificates
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

namespace CheckpointReadsAs

variable {a b c : Checkpoint Root}

@[simp, refl] theorem refl (c : Checkpoint Root) : CheckpointReadsAs c c := Or.inl rfl

theorem of_eq (h : a = b) : CheckpointReadsAs a b := Or.inl h

theorem symm (h : CheckpointReadsAs a b) : CheckpointReadsAs b a := by
  rcases h with h | ⟨ha, hb⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hb, ha⟩

theorem trans (h₁ : CheckpointReadsAs a b) (h₂ : CheckpointReadsAs b c) :
    CheckpointReadsAs a c := by
  rcases h₁ with rfl | ⟨ha, hb⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨_, hc⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩

/-- The reading never changes the epoch. -/
theorem epoch_eq (h : CheckpointReadsAs a b) : a.epoch = b.epoch := by
  rcases h with rfl | ⟨ha, hb⟩
  · rfl
  · rw [ha, hb]

/-- Away from `GENESIS_EPOCH` the reading is equality. -/
theorem eq_of_epoch_ne (h : CheckpointReadsAs a b)
    (hb : b.epoch ≠ GENESIS_EPOCH) : a = b := by
  rcases h with h | ⟨_, hb'⟩
  · exact h
  · exact absurd hb' hb

theorem eq_of_epoch_pos (h : CheckpointReadsAs a b) (hb : 0 < b.epoch) :
    a = b :=
  h.eq_of_epoch_ne (Nat.pos_iff_ne_zero.mp hb)

/-- A reading whose epoch is above some epoch is equality. -/
theorem eq_of_epoch_gt (h : CheckpointReadsAs a b) {x : ℕ} (hlt : x < a.epoch) :
    a = b := by
  have he : a.epoch = b.epoch := h.epoch_eq
  have hb : 0 < b.epoch := by rw [← he]; exact Nat.lt_of_le_of_lt (Nat.zero_le x) hlt
  exact h.eq_of_epoch_pos hb

/-- Two readings of one checkpoint are readings of each other. -/
theorem of_common (ha : CheckpointReadsAs a c) (hb : CheckpointReadsAs b c) :
    CheckpointReadsAs a b :=
  ha.trans hb.symm

/-- Two readings of each other that are each the anchor or newer than it
are equal: the only `GENESIS_EPOCH` checkpoint of that kind is the anchor. -/
theorem eq_of_anchor_or_after {anchor : Checkpoint Root}
    (h : CheckpointReadsAs a b)
    (ha : a = anchor ∨ anchor.epoch < a.epoch)
    (hb : b = anchor ∨ anchor.epoch < b.epoch) : a = b := by
  rcases h with h | ⟨ha0, hb0⟩
  · exact h
  · have ha0' : a.epoch = 0 := ha0
    have hb0' : b.epoch = 0 := hb0
    have ha' : a = anchor := by
      rcases ha with ha | ha
      · exact ha
      · rw [ha0'] at ha
        exact absurd ha (Nat.not_lt_zero _)
    have hb' : b = anchor := by
      rcases hb with hb | hb
      · exact hb
      · rw [hb0'] at hb
        exact absurd hb (Nat.not_lt_zero _)
    rw [ha', hb']

/-- Normalization maps a raw read to the anchor-or-newer checkpoint that it
reads as. -/
theorem normalize_eq_of_anchor_or_after {anchor : Checkpoint Root}
    (h : CheckpointReadsAs a b)
    (hb : b = anchor ∨ anchor.epoch < b.epoch) :
    normalizeAnchorCheckpoint anchor a = b := by
  rcases h with rfl | ⟨ha0, hb0⟩
  · rcases hb with rfl | hlt
    · exact normalizeAnchorCheckpoint.anchor a
    · simp only [normalizeAnchorCheckpoint, if_neg (Nat.not_le.mpr hlt)]
  · have ha0' : a.epoch = 0 := ha0
    have hb0' : b.epoch = 0 := hb0
    have hb' : b = anchor := by
      rcases hb with hb | hb
      · exact hb
      · rw [hb0'] at hb
        exact absurd hb (Nat.not_lt_zero _)
    have hle : a.epoch ≤ anchor.epoch := by
      rw [ha0']
      exact Nat.zero_le _
    rw [hb']
    simp only [normalizeAnchorCheckpoint, if_pos hle]

/-- A raw read reads as its normalization when it reads as an anchor-or-newer
checkpoint. -/
theorem reads_normalize {anchor : Checkpoint Root}
    (h : CheckpointReadsAs a b)
    (hb : b = anchor ∨ anchor.epoch < b.epoch) :
    CheckpointReadsAs a (normalizeAnchorCheckpoint anchor a) := by
  rw [h.normalize_eq_of_anchor_or_after hb]
  exact h

/-- A strict epoch update, as in `update_checkpoints`, gives the same result
for a raw candidate and for its reading. -/
theorem strict_update (current : Checkpoint Root)
    (h : CheckpointReadsAs a b) :
    (if current.epoch < a.epoch then a else current) =
      (if current.epoch < b.epoch then b else current) := by
  by_cases hlt : current.epoch < a.epoch
  · have hb : current.epoch < b.epoch := h.epoch_eq ▸ hlt
    rw [if_pos hlt, if_pos hb]
    exact h.eq_of_epoch_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
  · have hb : ¬ current.epoch < b.epoch := h.epoch_eq ▸ hlt
    rw [if_neg hlt, if_neg hb]

/-- At a genesis anchor, the reading is equality after anchor
normalization. -/
theorem iff_normalize {anchor : Checkpoint Root}
    (hanchor : anchor.epoch = GENESIS_EPOCH) :
    CheckpointReadsAs a b ↔
      normalizeAnchorCheckpoint anchor a = normalizeAnchorCheckpoint anchor b := by
  constructor
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · simp only [normalizeAnchorCheckpoint, ha, hb, hanchor, le_refl, if_true]
  · intro h
    by_cases ha : a.epoch ≤ anchor.epoch <;> by_cases hb : b.epoch ≤ anchor.epoch
    · rw [hanchor] at ha hb
      exact Or.inr ⟨Nat.le_zero.mp ha, Nat.le_zero.mp hb⟩
    · simp only [normalizeAnchorCheckpoint, ha, hb, if_true, if_false] at h
      exact absurd (le_of_eq (congrArg Checkpoint.epoch h.symm)) hb
    · simp only [normalizeAnchorCheckpoint, ha, hb, if_true, if_false] at h
      exact absurd (le_of_eq (congrArg Checkpoint.epoch h)) ha
    · simp only [normalizeAnchorCheckpoint, ha, hb, if_false] at h
      exact Or.inl h

end CheckpointReadsAs
end FastConfirmation.Spec

end
