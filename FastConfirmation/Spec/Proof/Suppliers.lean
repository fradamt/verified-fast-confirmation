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

The E5 reset legs (`genesis_safe`/`finalized_safe`/`observed_safe`) are rebuilt verbatim
from the proven interface machinery (`FinalWiring`/`AnchorFacade`/`ExportWiring`), so
`l4Residual_of_advance` needs only `SpecAssumptions` + `SameSlotFinalizedRootKnown` + the advance leg.

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

/-! ## Section 3 — `L4Residual` from the advance leg (E5 legs reused verbatim) -/

/-- **`L4Residual` from `SameSlotFinalizedRootKnown` + the advance leg.** The three
E5 reset legs are rebuilt exactly as `INVstarTrack.l4Residual_of_soundResidualsGround` builds
them from `SoundResidualsGround` — the genesis/finalized reset anchors through
`AnchorFacade.safeFrom_of_justified_dom_K` (`genesis_dom_of_interface` /
`finalized_dom_of_known` with the same-slot corner supplied by `SameSlotFinalizedRootKnown`, later slot
by `finalized_root_relay_known`), the observed anchor through
`AnchorFacade.safeFrom_observed_of_filter_K` fed `ExportWiring.observedFilterResiduals_of_interface`
— so this needs only `SpecAssumptions` + `SameSlotFinalizedRootKnown`. The advance leg `advance_safe` is
taken directly (built by `advance_safe_of_disjunctive` on the sound disjunctive route). No
engine `dynamics_struct` / `fork_edges_ground` appears: the advance case is discharged by the
FFG takeover inside the advance leg, not by an LMD chain. -/
theorem l4Residual_of_advance (hSA : SpecAssumptions cfg ext E)
    (hSameSlot : E.SameSlotFinalizedRootKnown cfg ext)
    (hadvance : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      E.SafeFrom cfg ext b (n + 1)) :
    E.L4Residual cfg ext := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E := ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  have hdomK := E.store_domainK cfg ext hwfE hec hgen hji
  have hobs := E.observedFilterResiduals_of_interface cfg ext hji
    (E.prev_greatest_of_interface cfg ext hji)
  exact {
    genesis_safe := by
      intro v hv
      refine E.safeFrom_of_justified_dom_K cfg ext hdomK ?_
      intro w hw m _ hH
      exact E.genesis_dom_of_interface cfg ext hSA v hv w hw m hH
    finalized_safe := fun v hv n => by
      rw [E.fcrStep_store]
      refine E.safeFrom_of_justified_dom_K cfg ext hdomK ?_
      intro w hw m hm hH
      refine E.finalized_dom_of_known cfg ext hSA v hv n w hw m hm hH ?_
      by_cases hg : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)
      · exact E.finalized_root_relay_known cfg ext hji hsync v hv n w hw m
          (E.withinHorizon_mono cfg hm hH) hH hg
      · exact hSameSlot v hv n w hw m hm hH hg
    observed_safe := fun v hv n =>
      E.safeFrom_observed_of_filter_K cfg ext hji hdomK
        hobs.prev_greatest_justifiedIn hobs.observed_known hobs.observed_head_ahead v hv n
    advance_safe := hadvance
  }

end Execution

/-! ## Section 4 — the closing composition on the sound disjunctive route -/

/-- **`Spec_Safety` from `SameSlotFinalizedRootKnown` + the localized advance supplies**
— the sound closing. FCR safety follows from a proof that every execution's `SpecAssumptions`
supplies (i) the finalized-reset same-slot corner `SameSlotFinalizedRootKnown` and (ii) the three
per-confirmed-block advance supplies `hbk`/`hdisj`/`heng` (the endpoint knownness, the
`jc ⪰ b ∨ b ⪰ jc` disjunction, and the chain-branch engine). `advance_safe_of_disjunctive`
turns the three supplies into the advance leg on the sound disjunctive route (the advance case
off the engine, via the FFG takeover); `l4Residual_of_advance` assembles the `L4Residual`
with the E5 legs reused verbatim; `L4Fold.spec_safety_of_residual` folds the trajectory.

Unlike `Compose.Spec_Safety_proved` — which routes the advance leg through the
advance-regime-false `EngineGroundSuppliers.hcase` — this closing is sound at **every** slot
regime: the explicit premises are `SameSlotFinalizedRootKnown` (derivable for a genesis-start
anchor), the
chain-branch engine `heng`, the disjunction supply `hdisj` (reduced by `hdisj_of_covering`
to the strict-epoch `hadv_hi`), and the same-slot knownness `hb_sameslot` inside `hbk`
(reduced by `hbk_of_confirming`). The declaration uses only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. -/
theorem spec_safety_of_advance_disjunctive
    (hSameSlot : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.SameSlotFinalizedRootKnown cfg ext)
    (hbk : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          b ∈ (E.store cfg ext w m).block_roots)
    (hdisj : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
              (get_node_for_root b) = true ∨
            is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true)
    (heng : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
          is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
            (get_node_for_root b) = true) :
    Spec_Safety cfg ext :=
  spec_safety_of_residual cfg ext (fun E hSA =>
    E.l4Residual_of_advance cfg ext hSA (hSameSlot E hSA)
      (E.advance_safe_of_disjunctive cfg ext hSA (hbk E hSA) (hdisj E hSA) (heng E hSA)))

/-- **`Spec_Safety` from the genesis-start anchor + the advance supplies** —
the genesis-start closing. Specializing `spec_safety_of_advance_disjunctive` to a genesis
start (`hanchor0`, the anchor block at `GENESIS_SLOT`) discharges the finalized-reset
`SameSlotFinalizedRootKnown` corner **outright** via `Structural.sameSlotFinalizedRootKnown_of_genesis_start` (the
reset root sits above the slot-0 anchor, so its cross-store knownness needs no relay). What
requires exactly the advance supplies: the endpoint knownness `hbk` (whose same-slot
`hb_sameslot` leg is the same-slot availability corner for `b`), the disjunction `hdisj` (localized by
`hdisj_of_covering` to the strict-epoch engine sub-case `hadv_hi`), and the chain-branch
engine `heng` (the `INVstar`/ground-truth-`Bval` core). The `hanchor0` modeling hypothesis is
the same one `Compose.Spec_Safety_proved` carries; this route additionally removes the unsound
advance-regime dependence on `EngineGroundSuppliers.hcase`. -/
theorem spec_safety_of_advance_genesisStart
    (hanchor0 : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (hbk : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          b ∈ (E.store cfg ext w m).block_roots)
    (hdisj : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
              (get_node_for_root b) = true ∨
            is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true)
    (heng : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m → E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
          is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
            (get_node_for_root b) = true) :
    Spec_Safety cfg ext :=
  spec_safety_of_advance_disjunctive cfg ext
    (fun E hSA v hv n w hw m hm hH _hgate =>
      E.sameSlotFinalizedRootKnown_of_genesis_start cfg ext hSA (hanchor0 E hSA)
        v hv n w hw m hm hH)
    hbk hdisj heng

end FastConfirmation.Spec
