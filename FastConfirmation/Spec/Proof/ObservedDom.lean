import FastConfirmation.Spec.Proof.ResidualMechanicalII

/-!
# Spec / Proof / ObservedDom: deriving `observed_dom`

`ResidualMechanicalII.MechanicalResidualsII` includes the `observed_dom` field:

> the rotated observed-justified anchor is on every honest justified chain —
> `is_ancestor (store w m) (jc(w,m)) (obs(v,n)) = true`, i.e. `obs(v,n) ⪯ jc(w,m)`,

where `obs(v,n) := (fcrStep v n).current_epoch_observed_justified_checkpoint` and
`jc(w,m) := (store w m).justified_checkpoint`. This module derives its
mechanical and equal-epoch cases from `JustificationInterface` and represents the
two additional inputs as `ObservedDomResiduals`.

The reduction has two moving parts:

* **the `fcrStep` → `fcr` observed-checkpoint bridge** (mechanical). The interface's
  `observed_justified` export speaks of `(fcr v n).current_epoch_observed_...`; the
  residual speaks of `(fcrStep v n).current_epoch_observed_...`.
  `update_fast_confirmation_variables` (the first half of `on_fast_confirmation`, of
  which `fcrStep` is one application) leaves `current_epoch_observed_...` **unchanged
  off an epoch boundary** and only rotates it at `is_start_slot_at_epoch`.
  `fcrStep_observed_else` proves the off-boundary equality, so
  `JustifiedIn (store w m) (obs v n)` follows from `observed_justified` there. The
  on-boundary rotation (the value becomes `(fcr v n).previous_epoch_greatest_...`)
  is supplied by `prev_greatest_justifiedIn`.

* **the justified-dominance core** (`obs ⪯ jc`). Both `obs(v,n)` and `jc(w,m)` are
  `JustifiedIn (store w m)`, so `justified_unique` closes the **equal-epoch** case
  (equal roots + `is_ancestor_refl`). The **unequal-epoch** case is supplied by
  `justified_ancestry_strict`, the cross-epoch justified-chain-coherence input.

`observed_dom_of_residuals` composes them: `observed_dom` follows from the two
named residuals `prev_greatest_justifiedIn` + `justified_ancestry_strict`, bundled as
`ObservedDomResiduals`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 0 — the `update_fast_confirmation_variables` observed-field bridge

`update_fast_confirmation_variables` rotates `current_epoch_observed_justified_checkpoint`
**only** inside the `is_start_slot_at_epoch (get_current_slot store)` branch; off that
branch the field passes through unchanged. This is the store-generic fact behind the
`fcrStep` → `fcr` observed-checkpoint bridge (mirroring `L4Fold.update_fcv_confirmed_root`). -/

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

/-- **`fcrStep` carries `fcr`'s observed checkpoint off an epoch boundary.** `fcrStep v n`
is `update_fast_confirmation_variables` applied to `fcr v n` re-seated on `store v (n+1)`;
its store is `store v (n+1)`, so off an epoch boundary `update_fcv_observed_else` keeps the
observed checkpoint equal to `(fcr v n)`'s. -/
theorem fcrStep_observed_else (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1)))
      = false) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
      = (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStep]
  exact update_fcv_observed_else cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) } hstart

/-- **`fcrStep`'s observed checkpoint equals the next second's `fcr` observed checkpoint
at a slot advance.** At a slot advance `fcr v (n+1)` runs `on_fast_confirmation`, whose
first half is exactly `fcrStep`'s `update_fast_confirmation_variables`, and whose only
extra write (`confirmed_root`) does not touch the observed checkpoint. So even *on* an
epoch boundary the `fcrStep`-observed value is a genuine `fcr`-observed value whenever the
slot advances — the interface's `observed_justified` covers it. -/
theorem fcrStep_observed_eq_fcr_succ (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
      = (E.fcr cfg ext v (n + 1)).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStep]
  simp only [Execution.fcr]
  rw [if_pos hadv]
  simp only [on_fast_confirmation]

/-! ## Section 1 — `JustifiedIn` of the `fcrStep` observed checkpoint

The interface's `observed_justified` export gives `JustifiedIn (store w m)` for the
`fcr`-observed checkpoint at every honest node from the same slot on. Three cases pin the
`fcrStep`-observed checkpoint to an `fcr`-observed one:

* **off an epoch boundary** — equals `(fcr v n)`'s observed checkpoint
  (`fcrStep_observed_else`); `observed_justified v n` closes it.
* **on a boundary, at a slot advance** — equals `(fcr v (n+1))`'s observed checkpoint
  (`fcrStep_observed_eq_fcr_succ`); `observed_justified v (n+1)` closes it.
* **on a boundary, no slot advance** — the re-rotated value (`(fcr v n)`'s greatest
  unrealized), the sole named residual `prev_greatest_justifiedIn`. This is the "stuck a
  second past an epoch-start second" corner, where `fcrStep`'s re-application of the
  rotation is discarded by the `fcr` recursion; this is the
  `prev_greatest_justifiedIn` case.

`n + 1 ≤ m` gives both `slot_at n ≤ slot_at m` and `slot_at (n+1) ≤ slot_at m`
(`slot_at_mono`), the export's synchrony hypothesis. -/

/-- **`JustifiedIn (store w m)` of the `fcrStep` observed checkpoint.** Off a boundary and
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
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint))
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m) :
    JustifiedIn (E.store cfg ext w m)
      ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint) := by
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

/-! ## Section 2 — the residual bundle and the `observed_dom` reduction

`ObservedDomResiduals` collects two inputs — the
on-boundary greatest-unrealized propagation and the unequal-epoch justified-chain
coherence — each in an existing (interface-family) shape. `observed_dom_of_residuals`
discharges the full `observed_dom` statement (verbatim `MechanicalResidualsII.observed_dom`)
from `JustificationInterface` + this bundle: the equal-epoch case from `justified_unique`
+ `is_ancestor_refl`, the unequal-epoch case from the named core. -/

/-- **The two residuals `observed_dom` reduces to** (`ObservedDom`). Each in an interface-family
shape:

* `prev_greatest_justifiedIn` — on an epoch boundary **with no slot advance** the
  re-rotated `fcrStep`-observed checkpoint (`(fcr v n)`'s
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
      ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
  /-- unequal-epoch justified-chain coherence: the observed anchor is on the justified
      chain when the two checkpoints differ in epoch (the equal-epoch case is discharged
      internally by `justified_unique`). -/
  justified_ancestry_strict : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch ≠
      (E.store cfg ext w m).justified_checkpoint.epoch →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true

/-- **`observed_dom` from `JustificationInterface` + `ObservedDomResiduals`.** The exact
`MechanicalResidualsII.observed_dom` statement. Case split on whether the observed anchor
and the store's justified checkpoint share an epoch: equal — both are `JustifiedIn (store
w m)` (`fcrStep_observed_justifiedIn` / `Or.inl rfl`), so `justified_unique` equates their
roots and `is_ancestor_refl` closes; unequal — the named `justified_ancestry_strict` core.
This is `ObservedDom`'s contract: `observed_dom` reduces to exactly the two `ObservedDomResiduals`
residuals. -/
theorem observed_dom_of_residuals (hji : JustificationInterface cfg ext E)
    (hres : E.ObservedDomResiduals cfg ext) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root
          (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true := by
  intro v hv n w hw m hm hH
  by_cases hep :
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch =
        (E.store cfg ext w m).justified_checkpoint.epoch
  · -- Equal epochs give equal roots by `justified_unique`.
    have hobs_just : JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint) :=
      E.fcrStep_observed_justifiedIn cfg ext hji hres.prev_greatest_justifiedIn
        v hv n w hw m hm hH
    have hjc_just : JustifiedIn (E.store cfg ext w m)
        (E.store cfg ext w m).justified_checkpoint := Or.inl rfl
    have hroot := hji.justified_unique w hw w hw m m hH hH _ _ hobs_just hjc_just hep
    rw [hroot]
    exact is_ancestor_refl _ _
  · exact hres.justified_ancestry_strict v hv n w hw m hm hH hep

end Execution

end FastConfirmation.Spec
