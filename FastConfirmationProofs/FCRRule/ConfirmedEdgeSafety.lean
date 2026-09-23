module
public import FastConfirmationProofs.FFG.SourceHistory.MarginInvariant
public import FastConfirmationProofs.FFG.SourceHistory.CheckpointSafetyInputs
public import FastConfirmationProofs.Execution.StoreInvariants.CheckpointDomain
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Discount.SupportDiscount
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Handlers.HandlerStepFacts

@[expose] public section

/-!
# Spec / Proof / Closing: the disjunctive safety composition

This module composes the **sound disjunctive route** in `Suppliers` into a safety
headline. The advance supplies `hbk`, `hdisj`, and `heng` are reduced to four explicit
per-confirmed-block fields.

## Why the disjunctive route is needed

A supplier bundle that routes the L4 advance leg through an `hcase` field
(`b ⪰ jc(w, m)` at every endpoint) demands something **false in the advance regime**: once a
descendant of `b` is justified, `jc(w, m)` sits strictly above `b`, so `hcase` is not provable as
`∀ E, SpecAssumptions → …`. (`Compose.EngineGroundSuppliers` did exactly that; it is deleted
with the observed-anchor cone's orphan sweep, P-6.) `Structural.safeFrom_of_disjunctive` instead uses the disjunctive
route (`Structural.safeFrom_of_disjunctive`): the advance branch is discharged **off the engine**
by the FFG takeover (`Structural.head_ge_of_advance`, `head ⪰ jc ⪰ b`), and only the chain branch
runs the LMD margin. Thus no assumption requires the advance-regime-false `hcase`.

## The four localized irreducible cores (`EngineAdvanceCore`)

The sound disjunctive route carries three supplies (`hbk`/`hdisj`/`heng`). Two of them reduce
as follows:

* `hbk` (endpoint knownness of `b`) ⟸ `Suppliers.hbk_of_confirming` from
  * `hbconf` — `b` is known at its **own** confirming store `(v, n+1)`;
  * `hb_sameslot` — `b` is known at a **foreign** endpoint `(w, m)` inside the confirming slot;
  the later-slot leg is `block_relay` (`FinalWiring.hb_of_confirming`), discharged in-composition.
* `hdisj` (`jc ⪰ b ∨ b ⪰ jc`) ⟸ `Suppliers.hdisj_of_covering` from
  * `hcov` — a per-endpoint covering justified checkpoint `jcb` with `b ⪰ jcb`, together with the
    strict-epoch engine sub-case `hadv_hi` (`jcb.epoch < jc.epoch → jc ⪰ b`); the `≤`-epoch side is
    closed inside `disjunction_of_covering` from `justified_ancestry`, so the field's open content
    is exactly `hadv_hi`.
* `heng` (chain-branch engine, `b ⪰ jc → head ⪰ b`) — the
  head-safety engine core (arXiv:2405.00549 §3.1's floored-integer arms on the `INVstar` /
  ground-truth-`Bval` track, `INVstarTrack`; per-edge `ForkEdgeGroundSupply`).

`EngineAdvanceCore` bundles these four fields and `advance_safe_of_core` rebuilds the disjunctive
advance supplies from it.

The safety/monotonicity headlines `Spec_Safety_closed` / `Spec_Monotonicity_closed` that used to
compose these with the genesis-start anchor `hanchor0` are **deleted** (P-6): they inherited
`AheadFacade`'s ahead-regime head-tracking premise from `Suppliers.l4Residual_of_advance`'s
observed-anchor leg, nothing ever produced it, and no audited witness reached them. See the
Section 3 note below and `docs/p6-justified-descends-derivation.md` §8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the four localized irreducible cores -/

/-- **The localized engine cores** — the transparent residual bundle obtained by opening the
`hbk` and `hdisj` advance supplies. Four per-confirmed-block fields:

* `hbconf` — the confirmed block `b` is known at its own confirming store `(v, n+1)` (the `hck`
  store-knownness family);
* `hb_sameslot` — `b` is known at a foreign endpoint `(w, m)` inside the confirming slot,
  before `block_relay`'s next-slot gate applies;
* `hcov` — a per-endpoint covering justified checkpoint `jcb` (`b ⪰ jcb`) plus the strict-epoch
  advance sub-case `hadv_hi` (the disjunction's engine content; the `≤`-epoch side is closed inside
  `disjunction_of_covering` from `justified_ancestry`);
* `heng` — the chain-branch head-safety engine (`b ⪰ jc → head ⪰ b`, the `INVstar` core).

`advance_safe_of_core` rebuilds the advance leg from this: `hbk` via `hbk_of_confirming`
(`hbconf` + `hb_sameslot`, later slot by `block_relay`), `hdisj` via `hdisj_of_covering` (`hcov`),
`heng` verbatim. -/
structure EngineAdvanceCore (E : Execution Root) : Prop where
  /-- The confirmed block is known at its own confirming store `(v, n+1)` (the `hck` family). -/
  hbconf : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    E.WithinHorizon cfg (n + 1) →
    is_one_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n).store
      (get_current_balance_source (E.fcrStoreAtCall cfg ext v n)) b = true →
    b ∈ (E.store cfg ext v (n + 1)).block_roots
  /-- The confirmed block is known at a foreign endpoint `(w, m)` inside the confirming slot
      (the same-slot availability corner for `b`). -/
  hb_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n).store
      (get_current_balance_source (E.fcrStoreAtCall cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
      b ∈ (E.store cfg ext w m).block_roots
  /-- A per-endpoint covering justified checkpoint `jcb` with `b ⪰ jcb`, plus the strict-epoch
      advance sub-case `hadv_hi` — the disjunction's localized engine content. -/
  hcov : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n).store
      (get_current_balance_source (E.fcrStoreAtCall cfg ext v n)) b = true →
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
            (get_node_for_root b) = true)
  /-- The chain-branch head-safety engine (`b ⪰ jc → head ⪰ b`) — the `INVstar` core. -/
  heng : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n).store
      (get_current_balance_source (E.fcrStoreAtCall cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true

/-! ### Deleted: `SelectedEngineAdvanceCore` and `advance_safe_of_selected_core`

The selected-result variant of the localized advance core, and the advance leg built from it.
Its only consumer was `AnchorThread.Spec_Safety_of_selectedCore`.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-! ## Section 2 — the advance leg from the localized cores -/


end Execution

/-! ## Section 3 — deleted: the safety and monotonicity headlines

`Spec_Safety_closed` and `Spec_Monotonicity_closed` stood here, composing
`Suppliers.spec_safety_of_advance_genesisStart` with the core opening
(`hbk_of_confirming` + `hdisj_of_covering`). Both carried the unproduced ahead-regime head-tracking premise `htracks`, inherited from the E5 observed-anchor leg of
`Suppliers.l4Residual_of_advance`, and both were unconsumed roots of the legacy
`SpecAssumptions` observed-anchor cone; they are deleted with it (P-6).

The localized core `EngineAdvanceCore` and its advance-leg builder `advance_safe_of_core`
remain (both are unconsumed roots of long standing); the selected-result variant
`SelectedEngineAdvanceCore` / `advance_safe_of_selected_core` had a single consumer in the cone
and went with it in the orphan sweep. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec

end
