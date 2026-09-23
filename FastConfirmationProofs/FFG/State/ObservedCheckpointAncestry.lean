module
public import FastConfirmationProofs.Execution.Trajectory.ChainWalkClosure

@[expose] public section

/-!
# Spec / Proof / ObservedDom

This module contains `update_fcv_observed_else`, `fcrStep_observed_else`, `fcrStep_observed_eq_fcr_succ` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 0 — the `update_fast_confirmation_variables` observed-field bridge

`update_fast_confirmation_variables` rotates `current_epoch_observed_justified_checkpoint`
**only** inside the `is_start_slot_at_epoch (get_current_slot store)` branch; off that
branch the field passes through unchanged. This is the store-generic fact behind the
`fcrStoreAtCall` → `fcr` observed-checkpoint bridge (mirroring `L4Fold.update_fcv_confirmed_root`). -/

/-- **`update_fast_confirmation_variables` leaves the observed checkpoint unchanged off
an epoch boundary.** When the store's current slot is not an epoch start, none of the
three field-group updates touches `current_epoch_observed_justified_checkpoint`. -/
theorem update_fcv_observed_else (fcr_store : FastConfirmationStore Root)
    (hstart : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) = false) :
    (update_fast_confirmation_variables cfg fcr_store).current_epoch_observed_justified_checkpoint
      = fcr_store.current_epoch_observed_justified_checkpoint := by
  simp only [update_fast_confirmation_variables]
  rw [if_neg (by rw [hstart]; decide)]
  split_ifs <;> rfl

namespace Execution

variable (E : Execution Root)

/-- **`fcrStoreAtCall` carries `fcr`'s observed checkpoint off an epoch boundary.** `fcrStoreAtCall v n`
is `update_fast_confirmation_variables` applied to `fcr v n` re-seated on `store v (n+1)`;
its store is `store v (n+1)`, so off an epoch boundary `update_fcv_observed_else` keeps the
observed checkpoint equal to `(fcr v n)`'s. -/
theorem fcrStep_observed_else (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1)))
      = false) :
    (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint
      = (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStoreAtCall]
  exact update_fcv_observed_else cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) } hstart

/-- **`fcrStoreAtCall`'s observed checkpoint equals the next second's `fcr` observed checkpoint
at a slot advance.** At a slot advance `fcr v (n+1)` runs `on_fast_confirmation`, whose
first half is exactly `fcrStoreAtCall`'s `update_fast_confirmation_variables`, and whose only
extra write (`confirmed_root`) does not touch the observed checkpoint. So even *on* an
epoch boundary the `fcrStoreAtCall`-observed value is a genuine `fcr`-observed value whenever the
slot advances — the interface's `observed_justified` covers it. -/
theorem fcrStep_observed_eq_fcr_succ (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint
      = (E.fcr cfg ext v (n + 1)).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStoreAtCall]
  simp only [Execution.fcr]
  rw [if_pos hadv]
  simp only [on_fast_confirmation]

/-! ## Section 1 — `JustifiedIn` of the `fcrStoreAtCall` observed checkpoint

The interface's `observed_justified` export gives `JustifiedIn (store w m)` for the
`fcr`-observed checkpoint at every honest node from the same slot on. Three cases pin the
`fcrStoreAtCall`-observed checkpoint to an `fcr`-observed one:

* **off an epoch boundary** — equals `(fcr v n)`'s observed checkpoint
  (`fcrStep_observed_else`); `observed_justified v n` closes it.
* **on a boundary, at a slot advance** — equals `(fcr v (n+1))`'s observed checkpoint
  (`fcrStep_observed_eq_fcr_succ`); `observed_justified v (n+1)` closes it.
* **on a boundary, no slot advance** — the re-rotated value (`(fcr v n)`'s greatest
  unrealized), the sole named residual `prev_greatest_justifiedIn`. This is the "stuck a
  second past an epoch-start second" corner, where `fcrStoreAtCall`'s re-application of the
  rotation is discarded by the `fcr` recursion; this is the
  `prev_greatest_justifiedIn` case.

`n + 1 ≤ m` gives both `slot_at n ≤ slot_at m` and `slot_at (n+1) ≤ slot_at m`
(`slot_at_mono`), the export's synchrony hypothesis. -/

/-- **`JustifiedIn (store w m)` of the `fcrStoreAtCall` observed checkpoint.** Off a boundary and
on a boundary at a slot advance from `observed_justified` (via `fcrStep_observed_else` /
`fcrStep_observed_eq_fcr_succ`); the on-boundary no-advance corner from the `hprev` residual
(`prev_greatest_justifiedIn`). -/
theorem fcrStep_observed_justifiedIn (hji : JustificationInterface cfg ext E)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint))
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m) :
    JustifiedIn (E.store cfg ext w m)
      ((E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint) := by
  by_cases hstart :
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true
  · by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)
    · rw [E.fcrStep_observed_eq_fcr_succ cfg ext v n hadv]
      exact hji.observed_justified v hv (n + 1) w hw m
        (E.withinHorizon_mono cfg hm hH) hH (E.slot_at_mono cfg hm)
    · exact hprev v hv n w hw m hm hH hstart hadv
  · rw [Bool.not_eq_true] at hstart
    rw [E.fcrStep_observed_else cfg ext v n hstart]
    have hnm : n ≤ m := Nat.le_trans (Nat.le_succ n) hm
    exact hji.observed_justified v hv n w hw m
      (E.withinHorizon_mono cfg hnm hH) hH (E.slot_at_mono cfg hnm)



/-- **The two residuals `observed_dom` reduces to** (`ObservedDom`). Each in an interface-family
shape:

* `prev_greatest_justifiedIn` — on an epoch boundary **with no slot advance** the
  re-rotated `fcrStoreAtCall`-observed checkpoint (`(fcr v n)`'s
  `previous_epoch_greatest_unrealized_checkpoint`)
  is justified in every honest view from the same slot on. The greatest-unrealized
  propagation. It is required only in the on-boundary/no-advance case; the advancing
  and off-boundary cases follow from `observed_justified`.
* `justified_ancestry_strict` — cross-epoch justified-chain coherence: when the
  observed anchor and the store's own justified checkpoint sit at
  **different** epochs, the anchor is on the justified chain. `justified_unique` closes
  the equal-epoch case. -/
structure ObservedDomResiduals (E : Execution Root) : Prop where
  /-- on an epoch boundary with no slot advance, the re-rotated observed checkpoint is
      justified everywhere later. -/
  prev_greatest_justifiedIn : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
    ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)) →
    JustifiedIn (E.store cfg ext w m)
      ((E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint)
  /-- unequal-epoch justified-chain coherence: the observed anchor is on the justified
      chain when the two checkpoints differ in epoch (the equal-epoch case is discharged
      internally by `justified_unique`). -/
  justified_ancestry_strict : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.epoch ≠
      (E.store cfg ext w m).justified_checkpoint.epoch →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true


end Execution

end FastConfirmation.Spec

end
