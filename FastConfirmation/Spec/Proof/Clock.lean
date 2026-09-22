module
public import FastConfirmation.Spec.Proof.Trajectory

@[expose] public section

/-!
# Spec / Proof / Clock

Layer 0, slot arithmetic: the `slot_start`/`slot_at` algebra the confirmation
layers reason with, made exact under whole-second slots
(`1000 ∣ cfg.slot_duration_ms`, mainnet `12000` ms).

`Execution.slot_at cfg n` reads the wall clock at relative second `n`; the
model definition divides *milliseconds by `slot_duration_ms`*, so under
`hdiv : 1000 ∣ cfg.slot_duration_ms` it collapses to an ordinary
seconds-per-slot division `(time + n - genesis_time) / (slot_duration_ms/1000)`
(`slot_at_eq`), which is monotone in `n` (`slot_at_mono`).

The two truncated subtractions in `slot_start` make the boundary facts —
`slot_at (slot_start s) = s`, the Galois pair `slot_start_le_of_slot_at` /
`slot_at_lt_iff` — hold only at or above the anchor slot; the guards
`E.slot_at cfg 0 ≤ s` and `genesis_time ≤ time` (the genesis store's own
`time_ge_genesis`) are therefore carried explicitly.

No behavioral assumptions enter here; everything is pure `ℕ` arithmetic over
the model definitions, with `GENESIS_SLOT = 0`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Seconds per slot -/

/-- Under `hdiv`, `slot_duration_ms = 1000 * (slot_duration_ms / 1000)`, so the
seconds-per-slot count is positive (`slot_duration_ms` is positive). -/
private theorem seconds_per_slot_pos (cfg : Config)
    (hdiv : 1000 ∣ cfg.slot_duration_ms) : 0 < cfg.slot_duration_ms / 1000 := by
  have h := Nat.mul_div_cancel' hdiv
  have hpos := cfg.slot_duration_ms_pos
  omega

/-- Under `hdiv`, milliseconds-by-`slot_duration_ms` division rewrites to
seconds-by-`(slot_duration_ms/1000)`: `x * slot_duration_ms / 1000
= x * (slot_duration_ms / 1000)` (both equal `x * (slot_duration_ms/1000)`
once `slot_duration_ms = 1000 * (slot_duration_ms/1000)`). -/
private theorem mul_slot_duration_div (cfg : Config)
    (hdiv : 1000 ∣ cfg.slot_duration_ms) (x : ℕ) :
    x * cfg.slot_duration_ms / 1000 = x * (cfg.slot_duration_ms / 1000) := by
  obtain ⟨k, hk⟩ := hdiv
  rw [hk, Nat.mul_div_cancel_left k (by omega : (0 : ℕ) < 1000),
    Nat.mul_left_comm x 1000 k,
    Nat.mul_div_cancel_left (x * k) (by omega : (0 : ℕ) < 1000)]

namespace Execution

variable (E : Execution Root) (cfg : Config)

/-! ## `slot_at` as a seconds division -/

/-- `slot_at` is monotone in the second (no whole-second assumption needed):
the numerator `time + n - genesis_time` grows with `n`, and multiplication and
division preserve `≤`. -/
theorem slot_at_mono {n m : ℕ} (hnm : n ≤ m) :
    E.slot_at cfg n ≤ E.slot_at cfg m := by
  simp only [Execution.slot_at, Execution.time_at, GENESIS_SLOT, Nat.zero_add]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right 1000
    (Nat.sub_le_sub_right (Nat.add_le_add_left hnm _) _))

/-- Absolute execution time is monotone in the relative second. -/
theorem time_at_mono {n m : ℕ} (hnm : n ≤ m) :
    E.time_at n ≤ E.time_at m := by
  simp only [Execution.time_at]
  exact Nat.add_le_add_left hnm _

/-- Verification-window membership is downward closed in time. -/
theorem withinHorizon_mono {n m : ℕ} (hnm : n ≤ m)
    (hm : E.WithinHorizon cfg m) : E.WithinHorizon cfg n := by
  rcases hm with ⟨htime, hslot, hepoch⟩
  exact ⟨(E.time_at_mono hnm).trans htime,
    (E.slot_at_mono cfg hnm).trans hslot,
    lt_of_le_of_lt (Nat.div_le_div_right (E.slot_at_mono cfg hnm)) hepoch⟩

/-- Any earlier slot is representable and below the verification horizon when
the endpoint second is. -/
theorem slotWithinHorizon_of_le {s : Slot} {n : ℕ}
    (hs : s ≤ E.slot_at cfg n) (hn : E.WithinHorizon cfg n) :
    E.SlotWithinHorizon cfg s :=
  ⟨hs.trans hn.2.1,
    lt_of_le_of_lt (Nat.div_le_div_right hs) hn.2.2⟩

/-- Slot-level verification-window membership is downward closed. -/
theorem slotWithinHorizon_mono {a b : Slot} (hab : a ≤ b)
    (hb : E.SlotWithinHorizon cfg b) : E.SlotWithinHorizon cfg a :=
  ⟨hab.trans hb.1,
    lt_of_le_of_lt (Nat.div_le_div_right hab) hb.2⟩

/-- Epoch-only projection of `slotWithinHorizon_of_le`. -/
theorem epoch_lt_horizon_of_slot_le {s : Slot} {n : ℕ}
    (hs : s ≤ E.slot_at cfg n) (hn : E.WithinHorizon cfg n) :
    compute_epoch_at_slot cfg s < E.verification_horizon :=
  (E.slotWithinHorizon_of_le cfg hs hn).2

/-- Under whole-second slots, `slot_at` is the seconds-per-slot division
`(time + n - genesis_time) / (slot_duration_ms / 1000)`: the model's
`* 1000 / slot_duration_ms` collapses because `slot_duration_ms = 1000 * spb`
(`Nat.mul_div_mul_left`). -/
theorem slot_at_eq (hdiv : 1000 ∣ cfg.slot_duration_ms) (n : ℕ) :
    E.slot_at cfg n =
      (E.genesis_store.time + n - E.genesis_store.genesis_time) /
        (cfg.slot_duration_ms / 1000) := by
  obtain ⟨k, hk⟩ := hdiv
  simp only [Execution.slot_at, Execution.time_at, GENESIS_SLOT, Nat.zero_add]
  rw [hk, Nat.mul_div_cancel_left k (by omega : (0 : ℕ) < 1000),
    Nat.mul_comm (E.genesis_store.time + n - E.genesis_store.genesis_time) 1000,
    Nat.mul_div_mul_left _ k (by omega : (0 : ℕ) < 1000)]

/-! ## Boundary seconds -/

/-- The first second of slot `s` lands in slot `s`, for slots at or above the
anchor (`E.slot_at cfg 0 ≤ s`) under `genesis_time ≤ time`. Both truncated
subtractions of `slot_start` are handled: when the boundary second is genuine
the numerator is exactly `s * spb`; when `slot_start s` truncates to `0` the
guard pins `slot_at 0 = s`. -/
theorem slot_at_slot_start (hdiv : 1000 ∣ cfg.slot_duration_ms) {s : Slot}
    (hs : E.slot_at cfg 0 ≤ s)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time) :
    E.slot_at cfg (E.slot_start cfg s) = s := by
  have hspb : 0 < cfg.slot_duration_ms / 1000 := seconds_per_slot_pos cfg hdiv
  have hstart : E.slot_start cfg s = E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000) - E.genesis_store.time := by
    simp only [Execution.slot_start]; rw [mul_slot_duration_div cfg hdiv s]
  have hs' : (E.genesis_store.time - E.genesis_store.genesis_time) /
      (cfg.slot_duration_ms / 1000) ≤ s := by
    have h0 := Execution.slot_at_eq E cfg hdiv 0
    simp only [Nat.add_zero] at h0
    rw [← h0]; exact hs
  rw [Execution.slot_at_eq E cfg hdiv, hstart]
  rcases Nat.lt_or_ge (E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000)) E.genesis_store.time with hc | hc
  · -- `slot_start s` truncated to `0`: numerator is `time - genesis_time`.
    have hnum : E.genesis_store.time + (E.genesis_store.genesis_time +
        s * (cfg.slot_duration_ms / 1000) - E.genesis_store.time) -
          E.genesis_store.genesis_time =
        E.genesis_store.time - E.genesis_store.genesis_time := by omega
    rw [hnum]
    have hle2 : s * (cfg.slot_duration_ms / 1000) ≤
        E.genesis_store.time - E.genesis_store.genesis_time := by
      exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hc.le)
    exact Nat.le_antisymm hs' ((Nat.le_div_iff_mul_le hspb).mpr hle2)
  · -- genuine boundary second: numerator is exactly `s * spb`.
    have hnum : E.genesis_store.time + (E.genesis_store.genesis_time +
        s * (cfg.slot_duration_ms / 1000) - E.genesis_store.time) -
          E.genesis_store.genesis_time = s * (cfg.slot_duration_ms / 1000) := by
      omega
    rw [hnum]; exact Nat.mul_div_cancel s hspb

/-- Galois half: if second `n` is in slot `s`, the start of slot `s` is at or
before `n`. Uses `s * spb ≤ time + n - genesis_time` (from
`slot_at n = (time + n - genesis_time) / spb = s`). -/
theorem slot_start_le_of_slot_at (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time) {n : ℕ} {s : Slot}
    (h : E.slot_at cfg n = s) : E.slot_start cfg s ≤ n := by
  have hstart : E.slot_start cfg s = E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000) - E.genesis_store.time := by
    simp only [Execution.slot_start]; rw [mul_slot_duration_div cfg hdiv s]
  rw [hstart]
  have hle : s * (cfg.slot_duration_ms / 1000) ≤
      E.genesis_store.time + n - E.genesis_store.genesis_time := by
    have hself := Nat.div_mul_le_self
      (E.genesis_store.time + n - E.genesis_store.genesis_time)
      (cfg.slot_duration_ms / 1000)
    rw [← Execution.slot_at_eq E cfg hdiv, h] at hself
    exact hself
  have h2 : s * (cfg.slot_duration_ms / 1000) + E.genesis_store.genesis_time ≤
      E.genesis_store.time + n :=
    Nat.add_le_of_le_sub (hgen.trans (Nat.le_add_right _ _)) hle
  rw [Nat.add_comm] at h2
  exact Nat.sub_le_iff_le_add.mpr (by rw [Nat.add_comm n]; exact h2)

/-- Galois pair: slot `s` strictly exceeds the slot of second `n` exactly when
`n` is strictly before the start of slot `s`. Both directions reduce, via
`Nat.div_lt_iff_lt_mul`, to `time + n - genesis_time < s * spb`, which the two
truncated subtractions of `slot_start` respect under `genesis_time ≤ time`. -/
theorem slot_at_lt_iff (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time) {n : ℕ} {s : Slot} :
    E.slot_at cfg n < s ↔ n < E.slot_start cfg s := by
  have hspb : 0 < cfg.slot_duration_ms / 1000 := seconds_per_slot_pos cfg hdiv
  have hstart : E.slot_start cfg s = E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000) - E.genesis_store.time := by
    simp only [Execution.slot_start]; rw [mul_slot_duration_div cfg hdiv s]
  rw [Execution.slot_at_eq E cfg hdiv, hstart, Nat.div_lt_iff_lt_mul hspb]
  omega

end Execution

end FastConfirmation.Spec

end
