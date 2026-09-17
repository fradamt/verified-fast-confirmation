import FastConfirmation.Spec.Proof.Compose

/-!
# Spec / Proof / Suppliers: wiring the engine-ground advance leg

This module wires the head-safety advance leg of `Spec_Safety` on the **sound
disjunctive route** (`Structural.safeFrom_of_disjunctive`), and reduces the mechanical
knownness / disjunction obligations to their localized residual shapes.

## Why the disjunctive route (and not `Compose.EngineGroundSuppliers.hcase` verbatim)

`Compose.EngineGroundSuppliers` reduces the engine bundle to four per-confirmed-block
fields, one of which — `hcase` — asks, at **every** honest endpoint `(w, m)` past the
confirmation, that the confirmed block `b` **descends from** the store's justified
checkpoint `jc(w, m)` (`get_ancestor_roots b jc ≠ [] ∨ b = jc`, i.e. `b ⪰ jc`). That
statement is **false in general**: once a descendant of `b` has itself been justified,
`jc(w, m)` sits strictly **above** `b` (`jc ⪰ b`, the *advance* regime), and there is no
chain from `jc` down to `b`. So `hcase` — hence `Compose.EngineGroundSuppliers` as a
closed `∀ E, SpecAssumptions → …` — is **not** provable; safety in the advance regime
holds by the FFG takeover (`head ⪰ jc ⪰ b`), not by an LMD chain.

`Compose`'s own field docstring already flags this ("`Structural.disjunction_of_covering`
localizes it to the strict-epoch `hadv_hi` sub-case on the alternative disjunctive
`SafeFrom` route"). This module *takes that alternative route*: it produces the advance leg
`advance_safe` (`= L4Fold.L4Residual.advance_safe`, `SafeFrom b (n+1)` per confirmed `b`)
via `Structural.safeFrom_of_disjunctive`, which discharges the advance branch **outright,
with no engine** (`Structural.head_ge_of_advance`, the FFG takeover) and delegates only the
**chain** branch to the engine supplier `heng`. The result is a *sound* closing whose open
content is exactly:

* `heng` — the chain-branch head-safety engine (`b ⪰ jc → head ⪰ b` at an endpoint): the
  `INVstar`/ground-truth-`Bval` core (`INVstarTrack`,
  `ForkEdgeGroundSupply` per edge, supplied through this interface);
* the disjunction supply `hdisj`, reduced by `hdisj_of_covering` to a per-endpoint
  covering justified checkpoint `jcb` (with `b ⪰ jcb`) plus the strict-epoch engine
  sub-case `hadv_hi` (`jcb.epoch < jc.epoch → jc ⪰ b`, `jc` advanced along `b`'s chain);
* the knownness supply `hbk`, reduced by `hbk_of_confirming` to the confirming-store
  knownness `hbconf` (later-slot, discharged by `block_relay` via
  `FinalWiring.hb_of_confirming`) and the same-slot corner `hb_sameslot` (same-slot availability for
  `b`, past the relay gate);
* `SameSlotFinalizedRootKnown` (the finalized-reset same-slot corner, genesis-start-closable by
  `Structural.sameSlotFinalizedRootKnown_of_genesis_start`).

## What is left here

The `L4Residual` assembly `l4Residual_of_advance` and the two closings
`spec_safety_of_advance_disjunctive` / `spec_safety_of_advance_genesisStart` are **deleted**
(P-6). Their E5 observed-anchor leg ran through
`ExportWiring.observedFilterResiduals_of_interface`, so they carried the ahead-regime premise
`AheadFacade`'s ahead-regime head-tracking premise — which nothing in the development ever produced, and which
no audited witness reached. The whole legacy `SpecAssumptions` observed-anchor cone goes with
them; see the Section 3/4 notes below and `docs/p6-justified-descends-derivation.md` §8.

What survives is Sections 1-2: the advance leg itself (`advance_safe_of_disjunctive`) and the
two mechanical reductions `hbk_of_confirming` / `hdisj_of_covering`. None of them touches the
ahead regime.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the advance leg on the sound disjunctive route -/

/-- **The advance leg from the disjunctive route.** For every
`is_one_confirmed` block `b` at a slot-update store, `SafeFrom b (n+1)` — the engine leg of
`L4Fold.L4Residual` — follows from three per-confirmed-block, per-endpoint supplies:

* `hbk` — `b` is a known block at each honest endpoint `(w, m)` past `n+1`;
* `hdisj` — at each such endpoint, `jc(w, m) ⪰ b` (advance) **or** `b ⪰ jc(w, m)` (chain);
* `heng` — the chain-branch engine: `b ⪰ jc(w, m) → head(w, m) ⪰ b`.

`Structural.safeFrom_of_disjunctive` discharges the advance branch with **no engine**
(`head_ge_of_advance`, the FFG takeover `head ⪰ jc ⪰ b`) and routes the chain branch through
`heng`. This is the sound replacement for the (advance-regime-false) `hcase` field of
`Compose.EngineGroundSuppliers`. -/
theorem advance_safe_of_disjunctive (hSA : SpecAssumptions cfg ext E)
    (hbk : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
        b ∈ (E.store cfg ext w m).block_roots)
    (hdisj : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        is_ancestor (E.store cfg ext w m)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
            (get_node_for_root b) = true ∨
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true)
    (heng : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        is_ancestor (E.store cfg ext w m) (get_node_for_root b)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
        is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
          (get_node_for_root b) = true) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      E.SafeFrom cfg ext b (n + 1) :=
  fun v hv n b hconf =>
    E.safeFrom_of_disjunctive cfg ext hSA (hbk v hv n b hconf) (hdisj v hv n b hconf)
      (heng v hv n b hconf)

/-! ## Section 2 — the two mechanical reductions of `hbk` and `hdisj` -/

/-- **The endpoint knownness `hbk` from the two confirming-store suppliers.**
Splits the per-endpoint knownness of the confirmed `b` on the slot regime, exactly as
`Compose.engineGroundResiduals_of_suppliers` splits `dynamics_struct`'s `hb`:

* later-slot (`slot_at (n+1) + 1 ≤ slot_at (m+1)`): `FinalWiring.hb_of_confirming`
  (`block_relay`) fed the confirming-store knownness `hbconf` (`b` is known at `(v, n+1)`);
* same-slot (the not-later regime, past `block_relay`'s `+1` gate): the carried
  `hb_sameslot` — the same-slot availability corner for `b`.

These are exactly the `hbconf`/`hb_sameslot` fields of `Compose.EngineGroundSuppliers`. -/
theorem hbk_of_confirming (hsync : Synchrony cfg ext E)
    (hbconf : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      E.WithinHorizon cfg (n + 1) →
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      b ∈ (E.store cfg ext v (n + 1)).block_roots)
    (hb_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
        b ∈ (E.store cfg ext w m).block_roots) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
        b ∈ (E.store cfg ext w m).block_roots := by
  intro v hv n b hconf w hw m hm hH
  by_cases hgap : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)
  · exact E.hb_of_confirming cfg ext hsync hv hw
      (hbconf v hv n b (E.withinHorizon_mono cfg hm hH) hconf)
      (E.withinHorizon_mono cfg hm hH) hH hgap
  · exact hb_sameslot v hv n b hconf w hw m hm hH hgap

/-- **The disjunction `hdisj` from a per-endpoint covering checkpoint + `hadv_hi`.**
At each endpoint the covering supply provides a justified checkpoint `jcb` with
`b ⪰ jcb` (the confirming-store balance-source descent transported), and the strict-epoch
engine sub-case `hadv_hi` (`jcb.epoch < jc.epoch → jc ⪰ b`, where `jc` outran `b`'s covering
checkpoint and so advanced *along* `b`'s chain). `Structural.disjunction_of_covering` then
closes the `≤`-epoch side from `justified_ancestry` (`jcb ⪰ jc`, so `b ⪰ jcb ⪰ jc`) and the
strict side from `hadv_hi`. This localizes the disjunction's explicit premise to exactly
`hadv_hi` — the head-safety engine content for the `jc`-advance sub-case. -/
theorem hdisj_of_covering (hSA : SpecAssumptions cfg ext E)
    (hcov : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        ∃ jcb : Checkpoint Root,
          b ∈ (E.store cfg ext w m).block_roots ∧
          JustifiedIn (E.store cfg ext w m) jcb ∧
          jcb.root ∈ (E.store cfg ext w m).block_roots ∧
          is_ancestor (E.store cfg ext w m)
            (get_node_for_root b) (get_node_for_root jcb.root) = true ∧
          (jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
            is_ancestor (E.store cfg ext w m)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
              (get_node_for_root b) = true)) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        is_ancestor (E.store cfg ext w m)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
            (get_node_for_root b) = true ∨
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true := by
  intro v hv n b hconf w hw m hm hH
  obtain ⟨jcb, hb, hjust, hknown, hbge, hadv_hi⟩ :=
    hcov v hv n b hconf w hw m hm hH
  exact E.disjunction_of_covering cfg ext hSA w hw m hH hb hjust hknown hbge hadv_hi

/-! ## Section 3 — deleted: `l4Residual_of_advance`

This assembled an `L4Residual` from `SameSlotFinalizedRootKnown` plus the advance leg, reusing
the three E5 reset legs verbatim. Its observed-anchor leg ran
`AnchorFacade.safeFrom_observed_of_filter_K` on
`ExportWiring.observedFilterResiduals_of_interface`, so it carried the ahead-regime
head-tracking premise `htracks` explicitly. Nothing ever produced that premise, and
the whole legacy `SpecAssumptions` observed-anchor cone is deleted with it (P-6). See
`docs/p6-justified-descends-derivation.md` §8. -/

end Execution

/-! ## Section 4 — deleted: the closing compositions on the sound disjunctive route

`spec_safety_of_advance_disjunctive` and `spec_safety_of_advance_genesisStart` stood here. Both
folded `l4Residual_of_advance` through `L4Fold.spec_safety_of_residual`, and both carried the
unproduced ahead-regime head-tracking premise `htracks` that
`l4Residual_of_advance` needed for its observed-anchor leg. They are unconsumed roots of the
legacy `SpecAssumptions` observed-anchor cone and are deleted with it (P-6). The advance-leg
machinery of Sections 1-2 (`advance_safe_of_disjunctive`, `hbk_of_confirming`,
`hdisj_of_covering`) does not touch the ahead regime and is unaffected. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
