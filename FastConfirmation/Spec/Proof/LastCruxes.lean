module
public import FastConfirmation.Spec.Proof.INVstarTrack

@[expose] public section

/-!
# Spec / Proof / LastCruxes: ancestor transport and the residual reduction

`INVstarTrack` supplies the **`hBb`-free** per-edge pipeline, whose open content is
`SameSlotFinalizedRootKnown` and `EngineGroundResiduals`.

## Residual decomposition

The residuals split into **one ancestor-transport fact**, **one
genuine below-anchor obstruction**, and **the deep engine bundle**:

* **Crux 1 — `finalized_dom_sameslot` (= `SameSlotFinalizedRootKnown`).** The intended route is
  `finalized_descent` (`v`-finalized is an ancestor of `w`-finalized at `(w, m)`) +
  `checkpoint_known` (`w`-finalized is a known block at `(w, m)`) + the ancestor walk:
  the `is_ancestor` witness walks `w`'s known chain down to `v`-finalized, and the walk
  lands on a **known** root. `mem_of_is_ancestor_above_anchor` below is the exact,
  fully-proven transport lemma for that step — **on the above-anchor slots**. The
  residual is precisely the boundary condition it needs: that the `v`-finalized block,
  *as looked up in `w`'s store*, sits at or above the anchor slot
  (`hab : anchorSlot ≤ (store w m).blocks (v-fin).slot`). At the **same-slot** regime,
  past `block_relay`'s `+1` gossip gate, that bound is not derivable from the available
  interface: if `v-fin.root ∉ (store w m).block_roots` the totalized lookup is junk
  (slot below the anchor), and the below-anchor walk cannot be re-entered by the
  `WalkKnown` toolkit (which only spans slots `≥ anchorSlot`). It is equivalent to the
  goal — so `finalized_dom_sameslot` remains an explicit hypothesis (the
  interface lacks a "finalized blocks are old, hence already gossiped" export; the
  block relay's later-slot route already discharges every non-same-slot case). See the
  lemma docstring for the exact reduction.

* **Cruxes 2–6 — the engine bundle** (`hPS`, `hcov`, `hsat`, `hcase`, `hrec`). These are
  the economic and store-dynamics hypotheses that the
  head-safety engine's base mechanization consumes: `hPS` the parent-stuck honest-slice
  recorded↔ground bridge (`LastAlgebra.hAsplit_of_bridge`'s input), `hcov` the
  full-epoch coverage floor `total_active ≤ weight (span_committee …)`
  (`LastAlgebra.hcov_of_coverage`'s input, with the tiny-`TAB` max-floor edge), `hsat`
  the post-`T1` saturation store-dynamics fact, `hcase` the L4 loop-inversion cross-store
  descent (`IHMechanize.dynamicsChainStruct_of_endpoint`'s `hcase`), and `hrec` the
  recorded `c`-support at a later endpoint (`IHMechanize.hrec_of_domain`'s domain
  package). They form the explicit content of `EngineGroundResiduals` uniformly across
  slot regimes.

* **Crux 7 — the input facade.** The bundle is `SameSlotFinalizedRootKnown` +
  `EngineGroundResiduals`, the `hBb`-free minimal remainder.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-! ## Crux 1 core — above-anchor ancestor-membership transport

The exact, fully-proven step the `finalized_dom_sameslot` route needs: from a known
descendant `a` whose walk stays known down to the anchor slot, and an ancestor `b` that
sits at or above that anchor slot in this store, the ancestor is itself a known block.
This is `is_ancestor` + `get_ancestor_spec` on the mono-lifted anchor walk — no relay,
no economic content. The **only** hypothesis that is not Layer-0 dischargeable at the
same-slot regime is `hab` (the ancestor sits above the anchor in *this* store); see the
module header for why that is the residual boundary. -/

omit [Inhabited Root] in
/-- **Above-anchor ancestor is a known block.** If `a`'s parent walk stays known down to
`anchorSlot` (`hwa`), the ancestor `b` sits at or above the anchor slot in this store
(`hab`), and `b` is an ancestor of `a` (`hanc`, i.e. `get_ancestor a (blocks b).slot =
b`), then `b ∈ store.block_roots`.

*Proof.* `WalkKnown.mono` lifts `hwa` from `anchorSlot` up to `(blocks b).slot` (`hab`);
`get_ancestor_spec` on that walk gives that the walked ancestor is a known block; and
`hanc` identifies the walked ancestor with `b`.

*Use (crux 1).* Instantiate `a := (store w m).finalized_checkpoint.root` (known by
`JustificationInterface.checkpoint_known`), `b := (store v (n+1)).finalized_checkpoint.root`,
`hanc := JustificationInterface.finalized_descent v … w … m` (`v`-finalized is an ancestor
of `w`-finalized at `(w, m)`), `hwa` the anchor-slot walk from
`AnchorFacade.store_walkKnownK` (via `E5Filter.walkKnown_of_anchorSlot`). The residual is
exactly `hab` at the same-slot regime — see the header. -/
theorem mem_of_is_ancestor_above_anchor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {anchorSlot : Slot} {a b : Root}
    (hwa : WalkKnown store anchorSlot a)
    (hab : anchorSlot ≤ (store.blocks b).slot)
    (hanc : is_ancestor store (ForkChoiceNode.mk a) (ForkChoiceNode.mk b) = true) :
    b ∈ store.block_roots := by
  simp only [is_ancestor, decide_eq_true_eq] at hanc
  have hwalk : WalkKnown store (store.blocks b).slot a := hwa.mono hab
  have hspec := (get_ancestor_spec hwf hwalk).1
  rw [hanc] at hspec
  exact hspec

/-! ## Crux 7 — the minimal `hBb`-free facade

The `hBb`-free track reduces the safety obligation to the **two-bundle** remainder
`SameSlotFinalizedRootKnown` + `EngineGroundResiduals`.

It is strictly tighter than the three-field
`StrongPrefixSafety.StrongPrefixSafetyInputs`: the per-edge economic bundle `fork_edges`
(`ForkEdgeSupply`,
carrying the recorded base-enemy transport `hBb`) is replaced by the store-independent
ground-truth-`Bval` bundle `fork_edges_ground` (`ForkEdgeGroundSupply`), whose per-edge
`ForkEdgeGroundInputs` **drops `hBb` entirely** — the endpoint enemy `Bval` is
`span_fraction`-budgeted at the endpoint directly and transports by the honest legs only
(`GroundBeta`, without the unsound `hBb`-relay route). Thus the same-slot
tax-arm corner the v2 track carried on every `fork_edges` base transport is **gone**; what
remains open is only the E5-reset `SameSlotFinalizedRootKnown` corner (crux 1, the below-anchor
obstruction above) and the engine base mechanization (`EngineGroundResiduals` =
`dynamics_struct` + `fork_edges_ground`, cruxes 2–6). No outright closing follows:
`SameSlotFinalizedRootKnown` does not close (crux 1) and the engine bundle is open.

The monotonicity corollary on that same minimal bundle used to live here; it is deleted with the
legacy `SpecAssumptions` observed-anchor cone (P-6), see the note below. -/

variable (cfg : Config) (ext : Externals Root)

/-! ### Deleted: `Spec_Monotonicity_of_ground`

The monotonicity corollary on the two-bundle remainder stood here, composing
`INVstarTrack.Spec_Safety_of_ground` with `StrongPrefixSafety.spec_monotonicity_of_safety`. It
carried the unproduced ahead-regime head-tracking premise `htracks` and was an
unconsumed root of the legacy `SpecAssumptions` observed-anchor cone; it is deleted with that
cone (P-6). The ancestor-transport cruxes above are unaffected. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec

end
