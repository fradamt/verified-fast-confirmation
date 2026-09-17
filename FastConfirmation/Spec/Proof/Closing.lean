import FastConfirmation.Spec.Proof.Suppliers
import FastConfirmation.Spec.Proof.SameSlotProvenance

/-!
# Spec / Proof / Closing: the disjunctive safety composition

This module composes the **sound disjunctive route** in `Suppliers` into a safety
headline. The advance supplies `hbk`, `hdisj`, and `heng` are reduced to four explicit
per-confirmed-block fields.

## Why the disjunctive route is needed

`Compose.EngineGroundSuppliers` routes the L4 advance leg through its `hcase` field
(`b ⪰ jc(w, m)` at every endpoint) — a field that is **false in the advance regime** (once a
descendant of `b` is justified, `jc(w, m)` sits strictly above `b`, so `hcase` is not provable as
`∀ E, SpecAssumptions → …`). `Structural.safeFrom_of_disjunctive` instead uses the disjunctive
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
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    b ∈ (E.store cfg ext v (n + 1)).block_roots
  /-- The confirmed block is known at a foreign endpoint `(w, m)` inside the confirming slot
      (the same-slot availability corner for `b`). -/
  hb_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
      b ∈ (E.store cfg ext w m).block_roots
  /-- A per-endpoint covering justified checkpoint `jcb` with `b ⪰ jcb`, plus the strict-epoch
      advance sub-case `hadv_hi` — the disjunction's localized engine content. -/
  hcov : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
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
            (get_node_for_root b) = true)
  /-- The chain-branch head-safety engine (`b ⪰ jc → head ⪰ b`) — the `INVstar` core. -/
  heng : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true

/-- The executable-selection form of the advance core.  Unlike
`EngineAdvanceCore`, its fields are demanded only for the block actually
returned by `get_latest_confirmed (fcrStep v n)`.  Confirming-store and
same-slot knownness are deliberately absent: `advance_safe_of_selected_core`
derives both from the canonical candidate certificate and validation
provenance. -/
structure SelectedEngineAdvanceCore (E : Execution Root) : Prop where
  /-- A covering checkpoint for the concrete selected result. -/
  hcov : ∀ v ∈ E.honest, ∀ n : ℕ,
    get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n))
      (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ∃ jcb : Checkpoint Root,
        JustifiedIn (E.store cfg ext w m) jcb ∧
        jcb.root ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)))
          (get_node_for_root jcb.root) = true ∧
        (jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
          is_ancestor (E.store cfg ext w m)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
            (get_node_for_root
              (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true)
  /-- The chain-branch head-safety engine for the concrete selected result. -/
  heng : ∀ v ∈ E.honest, ∀ n : ℕ,
    get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n))
      (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)))
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true

/-! ## Section 2 — the advance leg from the localized cores -/

/-- The concrete selected-result bridge.  Reset equalities return through the
three threaded `SafeFrom` witnesses.  A strict executable selection retains
canonical membership and parent membership; the support/vote/relay proof then
establishes current-moment endpoint knownness, after which the selected
covering and engine fields close the disjunctive head argument. -/
theorem advance_safe_of_selected_core (hSA : SpecAssumptions cfg ext E)
    (hcore : E.SelectedEngineAdvanceCore cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hadvslot : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n))
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1))
    (hfin : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hobs : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1))
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n))
      (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) (n + 1) := by
  intro w hw m hm hH
  have hHn1 : E.WithinHorizon cfg (n + 1) := E.withinHorizon_mono cfg hm hH
  obtain ⟨hconfirmed, hfinalized, hobserved⟩ :=
    E.fcrStep_reset_roots_known_selected cfg ext hSA v hv n hHn1
  rcases E.get_latest_confirmed_selected cfg ext hSA v hv (n + 1) hHn1
      (E.fcrStep cfg ext v n) (E.fcrStep_store cfg ext v n)
      hconfirmed hfinalized hobserved with hreset | ⟨hselected, hbSelected, hpSelected⟩
  · rcases hreset with h | h | h
    · rw [h]
      exact hprev w hw m hm hH
    · rw [h]
      exact hfin w hw m hm hH
    · rw [h]
      exact hobs w hw m hm hH
  have hbConfirm : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hbSelected
  have hpConfirm : ((E.store cfg ext v (n + 1)).blocks
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))).parent_root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hpSelected
  have hbEndpoint : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints cfg ext hSA v hv n _ hHn1
      hbConfirm hpConfirm hselected w hw m (E.slot_at_mono cfg hm) hH
  obtain ⟨jcb, hjust, hjcbKnown, hbge, hadvHi⟩ :=
    hcore.hcov v hv n hadvslot hconf w hw m hm hH
  have hdisj := E.disjunction_of_covering cfg ext hSA w hw m hH hbEndpoint
    hjust hjcbKnown hbge hadvHi
  exact E.head_descent_of_disjunction cfg ext hSA w hw m hH hbEndpoint hdisj
    (hcore.heng v hv n hadvslot hconf w hw m hm hH)

/-- **The advance leg from `EngineAdvanceCore`.** For every `is_one_confirmed` block `b` at
a slot-update store, `SafeFrom b (n+1)` — the engine leg of `L4Fold.L4Residual` — follows from the
four localized cores: `hbk` is rebuilt by `Suppliers.hbk_of_confirming` (`hbconf` + `hb_sameslot`,
later slot discharged by `block_relay`), `hdisj` by `Suppliers.hdisj_of_covering` (`hcov`, with the
`≤`-epoch side closed from `justified_ancestry`), and `heng` is carried verbatim;
`Suppliers.advance_safe_of_disjunctive` folds them on the sound disjunctive route (advance branch
off the engine via the FFG takeover). -/
theorem advance_safe_of_core (hSA : SpecAssumptions cfg ext E)
    (hcore : E.EngineAdvanceCore cfg ext) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      E.SafeFrom cfg ext b (n + 1) :=
  E.advance_safe_of_disjunctive cfg ext hSA
    (E.hbk_of_confirming cfg ext hSA.2.2.2.2.1 hcore.hbconf hcore.hb_sameslot)
    (E.hdisj_of_covering cfg ext hSA hcore.hcov)
    hcore.heng

end Execution

/-! ## Section 3 — deleted: the safety and monotonicity headlines

`Spec_Safety_closed` and `Spec_Monotonicity_closed` stood here, composing
`Suppliers.spec_safety_of_advance_genesisStart` with the core opening
(`hbk_of_confirming` + `hdisj_of_covering`). Both carried the unproduced ahead-regime head-tracking premise `htracks`, inherited from the E5 observed-anchor leg of
`Suppliers.l4Residual_of_advance`, and both were unconsumed roots of the legacy
`SpecAssumptions` observed-anchor cone; they are deleted with it (P-6).

The localized cores `EngineAdvanceCore` / `SelectedEngineAdvanceCore` and the advance-leg
builders `advance_safe_of_core` / `advance_safe_of_selected_core` are unaffected. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
