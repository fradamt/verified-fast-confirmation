module
public import FastConfirmation.Spec.Proof.MicroSteps

@[expose] public section

/-!
# Spec / Proof / InterfaceRewire: rewire the residual bundles to the
justification-interface exports

The justification interface supplies three exports:
`checkpoint_known`, `justified_ancestry`, and `finalized_descent`, each shaped
to an input of the mechanical reductions. This module discharges the matching
inputs and proves the safety theorem over `Execution.FinalResiduals`.

## What the exports discharge

* `MechanicalResidualsII.justified_known` / `.finalized_known` ← `checkpoint_known`
  (the two conjuncts, verbatim — Section 1).
* `MechanicalResidualsII.finalized_descent` ← `finalized_descent` (verbatim, wired
  in `mechanicalResidualsII_of_final`).
* `MechanicalResidualsII.walk_closure` ← the **anchor-min guard**, via
  `MicroSteps.walkClosure_of_anchorGuard` fed by the Layer-0
  `store_parentInRootsOr` (Section 3).

## Inputs retained in `FinalResiduals`

* `MechanicalResidualsII.observed_dom` — the E5/E6 observed-anchor dominance.
  `observed_dom` reduces (`ObservedDom.observed_dom_of_residuals`) to
  `ObservedDomResiduals.{prev_greatest_justifiedIn, justified_ancestry_strict}`.
  `justified_ancestry` requires two additional facts that the input bundle does not
  carry and the interface does not otherwise export:
  1. **observed-anchor root knownness**
     `obs.root ∈ (store w m).block_roots` (the export needs `c.root` known;
     `checkpoint_known` covers only the store's *own* justified/finalized roots),
     and
  2. **the confirmation-anchor epoch bound**
     `obs.epoch ≤ (store w m).justified_checkpoint.epoch` (the export orients
     lower-epoch-as-ancestor; the residual carries only `obs.epoch ≠ jc.epoch`,
     and in the `obs.epoch > jc.epoch` regime the export yields the *opposite*
     ancestry).
  `observed_anchor_dom_of_interface` (Section 2) derives the dominance from
  `justified_ancestry` and exactly those two facts.
  `prev_greatest_justifiedIn` is the separate greatest-unrealized cross-store
  propagation (`MicroSteps.prev_greatest_justifiedIn_of_boundarySource` reduces it
  to `JustifiedIn (store w m)` of the boundary rotation source — a fcr
  rotation-idempotence residual, no interface export).
* `dynamics_struct` / `dynamics_edges` — the per-fork engine content (unchanged).

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the verbatim knownness discharges

`checkpoint_known` is the conjunction of justified- and finalized-root knownness;
its two projections are exactly `MechanicalResidualsII.justified_known` and
`.finalized_known`. -/

/-- **`justified_known` from `checkpoint_known`.** The first conjunct. -/
theorem justified_known_of_interface (hji : JustificationInterface cfg ext E) :
    ∀ w ∈ E.honest, ∀ m : ℕ,
      (E.store cfg ext w m).justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots :=
  fun w hw m => (hji.checkpoint_known w hw m).1

/-- **`finalized_known` from `checkpoint_known`.** The second conjunct. -/
theorem finalized_known_of_interface (hji : JustificationInterface cfg ext E) :
    ∀ w ∈ E.honest, ∀ m : ℕ,
      (E.store cfg ext w m).finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots :=
  fun w hw m => (hji.checkpoint_known w hw m).2

/-! ## Section 2 — `justified_ancestry` closes the observed-anchor dominance
modulo the two identified facts

`ObservedDomResiduals.justified_ancestry_strict` asks for the observed anchor
`obs` (any `JustifiedIn (store w m)` checkpoint) to be an ancestor of the store's
justified checkpoint `jc`, from `obs.epoch ≠ jc.epoch` alone. `justified_ancestry`
delivers this **given** `obs.root` known and `obs.epoch ≤ jc.epoch`: with the
ordering the `≠` is irrelevant, and the export's `c.root`/`c'.root`-known
premises are `obs.root` (assumed) and `jc.root` (`checkpoint_known.1`). The two
assumed facts are exactly the two premises stated by the theorem below. -/

/-- **Observed-anchor justified-dominance from `justified_ancestry`.** For any
checkpoint `c` that is `JustifiedIn (store w m)`, with `c.root` a known block and
`c.epoch ≤ (store w m).justified_checkpoint.epoch`, `c` is an ancestor of the
store's justified checkpoint (`c ⪯ jc`). Instantiated at
`c := (fcrStep v n).current_epoch_observed_justified_checkpoint` this is
`observed_dom`'s unequal-epoch core — modulo the observed-anchor knownness and
epoch-bound facts, which are explicit premises below. -/
theorem observed_anchor_dom_of_interface (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (c : Checkpoint Root)
    (hH : E.WithinHorizon cfg m)
    (hc_just : JustifiedIn (E.store cfg ext w m) c)
    (hc_known : c.root ∈ (E.store cfg ext w m).block_roots)
    (hle : c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c.root) = true :=
  hji.justified_ancestry w hw m c _ hH hc_just (Or.inl rfl) hle hc_known
    (hji.checkpoint_known w hw m).1

/-! ## Section 3 — the rewired input bundle

`FinalResiduals` contains the anchor-min guard, E5/E6 observed dominance, and the
per-fork engine inputs. `mechanicalResidualsII_of_final` derives
`justified_known`, `finalized_known`, and `finalized_descent` from the interface,
derives `walk_closure` from the anchor-min guard, and rebuilds the full seven-field
`MechanicalResidualsII` from `SpecAssumptions` and this bundle. -/

/-- **The rewired input bundle** (`InterfaceRewire`). `MechanicalResidualsII`'s three
knownness/descent fields are discharged from the justification-interface exports and
`walk_closure` is reduced to the anchor-min guard; the bundle contains four inputs: the
anchor guard, observed-anchor dominance (which the interface does not imply),
and the two per-fork engine fields. -/
structure FinalResiduals (E : Execution Root) : Prop where
  /-- `[A]`: the anchor-min guard — `walkClosure_of_anchorGuard`'s exact
      consumption. For the Layer-0 dangling parent `P` (any `P` carried by a
      store-wide `ParentInRootsOr`), a known block naming `P` has slot `≤ sl` for
      every target slot `sl` — i.e. only the genesis anchor's own edge, pinned at
      the minimal slot. `walk_closure` derives from this via
      `store_parentInRootsOr` (Section 3). -/
  anchor_guard : ∀ (P : Root),
    (∀ w ∈ E.honest, ∀ m : ℕ, ParentInRootsOr P (E.store cfg ext w m)) →
    ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root = P →
          ((E.store cfg ext w m).blocks r).slot ≤ sl
  /-- `[D]`: E5/E6 observed-justified justified-dominance (verbatim
      `MechanicalResidualsII.observed_dom`; kept as an explicit premise because
      the justification interface does not supply it). -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- `[E]`: the structural confirmed-chain per `is_one_confirmed` block. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E]`: the per-edge `DynamicsResidual` supply (the per-fork engine content). -/
  dynamics_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsEdgeSupply cfg ext b (n + 1)

/-- **`walk_closure` from the anchor-min guard + `SpecAssumptions`.** The Layer-0
`store_parentInRootsOr` produces the dangling-parent `P` and its store-wide
`ParentInRootsOr`; `walkClosure_of_anchorGuard` then closes every `WalkClosure`
obligation from the bundle's anchor guard on that `P`. -/
theorem walkClosure_of_final (hSA : SpecAssumptions cfg ext E)
    (hfinal : E.FinalResiduals cfg ext) :
    ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot, WalkClosure (E.store cfg ext w m) sl := by
  obtain ⟨hgen, hwf, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  obtain ⟨P, hP⟩ := E.store_parentInRootsOr cfg ext hwf hec hgen
    hwf.anchor_parent_unscheduled
  exact E.walkClosure_of_anchorGuard cfg ext (P := P) (fun w _hw m => hP w m)
    (hfinal.anchor_guard P (fun w _hw m => hP w m))

/-- **`MechanicalResidualsII` from `SpecAssumptions` + `FinalResiduals`.** The
seven fields: `walk_closure` from `walkClosure_of_final`; `justified_known` /
`finalized_known` / `finalized_descent` from the justification-interface exports;
`observed_dom` / `dynamics_struct` / `dynamics_edges` verbatim from the bundle. -/
theorem mechanicalResidualsII_of_final (hSA : SpecAssumptions cfg ext E)
    (hfinal : E.FinalResiduals cfg ext) : E.MechanicalResidualsII cfg ext := by
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  exact
    { walk_closure := E.walkClosure_of_final cfg ext hSA hfinal
      justified_known := fun w hw m _ => E.justified_known_of_interface cfg ext hji w hw m
      finalized_known := fun w hw m _ => E.finalized_known_of_interface cfg ext hji w hw m
      finalized_descent := fun v hv k w hw m hkm hH =>
        hji.finalized_descent v hv k w hw m
          (E.withinHorizon_mono cfg hkm hH) hH hkm
      observed_dom := hfinal.observed_dom
      dynamics_struct := hfinal.dynamics_struct
      dynamics_edges := hfinal.dynamics_edges }

end Execution

/-! ## Section 4 — safety theorem

Composing `mechanicalResidualsII_of_final` with
`spec_safety_of_mechanicalII`: FCR safety follows from a proof that every
execution's `SpecAssumptions` supplies the bundle `FinalResiduals`. -/

/-- **`Spec_Safety` from the rewired input bundle.** The knownness/descent
residuals are discharged from `JustificationInterface`, `walk_closure` is the
anchor-min guard, and what remains is `{anchor_guard, observed_dom,
dynamics_struct, dynamics_edges}` — the inputs produced by this reduction. (`observed_dom`
is required because the justification-interface `justified_ancestry` export needs
observed-anchor root knownness and the `obs.epoch ≤ jc.epoch` bound the residual
does not carry.) -/
theorem spec_safety_of_final
    (hfinal : ∀ E : Execution Root,
      SpecAssumptions cfg ext E → E.FinalResiduals cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_mechanicalII cfg ext
    (fun E hSA => E.mechanicalResidualsII_of_final cfg ext hSA (hfinal E hSA))

end FastConfirmation.Spec

end
