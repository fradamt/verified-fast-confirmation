import FastConfirmation.Spec.Proof.Structural

/-!
# Spec / Proof / Compose: `EngineGroundResiduals` from the shell

This module wires `EngineGroundResiduals` (the `hBb`-free ground-truth-`Bval` engine,
`INVstarTrack`) down to its transparent per-field suppliers.

It used to close the chain as well, with `Spec_Safety_proved` / `Spec_Monotonicity_proved` on
top of `Shrink.Spec_Safety_shrunk` and `Structural`'s genesis-start discharge of the same-slot
leg. Those two closings belonged to the legacy `SpecAssumptions` observed-anchor cone — they
carried the never-produced ahead-regime premise `AheadFacade`'s ahead-regime head-tracking premise — and are
deleted (P-6; see the Section 2 note and `docs/p6-justified-descends-derivation.md` §8).

## `EngineGroundResiduals` from `EngineGroundSuppliers`

`EngineGroundResiduals` has two fields, `dynamics_struct` (the structural `DynamicsChainStruct`
chain) and `fork_edges_ground` (the per-edge ground supply). The `dynamics_struct` field reduces
(`FinalWiring.dynamics_struct_of_suppliers`, i.e. `IHMechanize.dynamicsChainStruct_of_endpoint`) to
a per-endpoint knownness supplier `hb` and a loop-inversion descent supplier `hcase`. This module
**threads the mechanical part of `hb`**: at the later-slot regime `hb` is
`FinalWiring.hb_of_confirming` (`HeadStack.b_known_of_relay`, `block_relay`) fed the
confirming-store knownness `hbconf`. So
`EngineGroundResiduals` reduces to the four-field `EngineGroundSuppliers`:

* `hbconf` — the confirmed block is a known block at its **own** confirming store `(v, n+1)`
  (a `get_latest_confirmed`/`is_one_confirmed` store-knownness fact, the `hck`/`checkpoint_known`
  family);
* `hb_sameslot` — the confirmed block is known at a **foreign** endpoint `(w, m)` inside the
  confirming slot (past `block_relay`'s `+1` gate) — the same-slot availability corner for `b`;
* `hcase` — the loop-inversion descent `b ⪰ jc(w, m)` (`get_ancestor_roots b jc ≠ [] ∨ b = jc`)
  under the shell's head-safety IH — the cross-store L4 descent, the head-safety engine content
  (`Structural.disjunction_of_covering` restricts it to the strict-epoch `hadv_hi` sub-case
  on the alternative disjunctive `SafeFrom` route; see Section 3);
* `fork_edges_ground` — the per-edge ground supply, carried whole (the `INVstar` base + maintenance,
  the floored-integer arms).

`engineGroundResiduals_of_suppliers` discharges the later-slot `hb` and passes the rest through.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the threaded engine suppliers -/

/-- **The threaded engine-ground suppliers** — `EngineGroundResiduals` with the
`dynamics_struct` field opened to its per-confirmed-block suppliers and the mechanical later-slot
knownness split out. The four fields:

* `hbconf` — the confirmed block is known at its own confirming store `(v, n+1)`;
* `hb_sameslot` — the confirmed block is known at a foreign endpoint `(w, m)` **inside the
  confirming slot** (the not-later regime, past `block_relay`'s `+1` gate) — the same-slot availability corner;
* `hcase` — the loop-inversion descent `b ⪰ jc(w, m)` under the head-safety IH — the engine descent;
* `fork_edges_ground` — the per-edge ground supply provided by the `INVstar` engine.

`engineGroundResiduals_of_suppliers` rebuilds `EngineGroundResiduals` from this, discharging the
later-slot `hb` via `FinalWiring.hb_of_confirming`. -/
structure EngineGroundSuppliers (E : Execution Root) : Prop where
  /-- The confirmed block is a known block at its own confirming store `(v, n+1)`. -/
  hbconf : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    b ∈ (E.store cfg ext v (n + 1)).block_roots
  /-- The confirmed block is known at a foreign endpoint `(w, m)` inside the confirming slot
      (the not-later regime) — the same-slot availability corner for `b`. -/
  hb_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
      b ∈ (E.store cfg ext w m).block_roots
  /-- The loop-inversion descent `b ⪰ jc(w, m)` under the head-safety IH — the engine descent. -/
  hcase : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true) →
      get_ancestor_roots (E.store cfg ext w m) b
          (E.store cfg ext w m).justified_checkpoint.root ≠ [] ∨
        b = (E.store cfg ext w m).justified_checkpoint.root
  /-- The per-edge ground supply provided by the `INVstar` engine core. -/
  fork_edges_ground : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeGroundSupply cfg ext b (n + 1)

/-- **`EngineGroundResiduals` from the threaded suppliers.** Rebuilds the engine
bundle from `EngineGroundSuppliers`, discharging the mechanical part of `dynamics_struct`'s `hb`:
at each endpoint `(w, m)` the confirmed block's knownness is split on the slot regime — the
later-slot case is `FinalWiring.hb_of_confirming` (`block_relay`) fed the confirming-store knownness
`hbconf`, the same-slot case is the carried `hb_sameslot`. The `hcase` descent and the
`fork_edges_ground` supply pass through unchanged. `dynamics_struct` is then assembled by
`FinalWiring.dynamics_struct_of_suppliers`. -/
theorem engineGroundResiduals_of_suppliers (hSA : SpecAssumptions cfg ext E)
    (hsup : E.EngineGroundSuppliers cfg ext) : E.EngineGroundResiduals cfg ext := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E := ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  refine
    { dynamics_struct := ?_
      fork_edges_ground := hsup.fork_edges_ground }
  refine E.dynamics_struct_of_suppliers cfg ext hSA ?_ hsup.hcase
  intro v hv n b hconf w hw m hm hHm _hIH
  have hHn1 : E.WithinHorizon cfg (n + 1) := E.withinHorizon_mono cfg hm hHm
  by_cases hgap : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)
  · exact E.hb_of_confirming cfg ext hsync hv hw
      (hsup.hbconf v hv n b hconf) hHn1 hHm hgap
  · exact hsup.hb_sameslot v hv n b hconf w hw m hm hHm hgap

end Execution

/-! ## Section 2 — deleted: the closing composition

`Spec_Safety_proved` and `Spec_Monotonicity_proved` stood here, composing
`Shrink.Spec_Safety_shrunk` with the genesis-start same-slot discharge and the supplier
threading above. Both carried the unproduced ahead-regime head-tracking premise `htracks` and both were unconsumed roots of the legacy
`SpecAssumptions` observed-anchor cone; they are deleted with it (P-6). See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
