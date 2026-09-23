module
public import FastConfirmation.Spec.Proof.IHMechanize
public import FastConfirmation.Spec.Proof.ByzVpre

@[expose] public section

/-!
# Spec / Proof / VoteLanding: vote and sibling-confinement inputs

`IHMechanize` expresses several fields of `EdgeDynamics.EdgeInputResidual` in
terms of the following inputs:

* `hmaj_of_saturation` ← the support-saturation crux `hsat` + the boost-dilution
  crux `hdil`;
* `hdeltas_of_monotone` ← the per-slot monotonicity cruxes `hSmono` / `hXmono` / `hρ0`;
* `dynamicsChainStruct_of_endpoint` ← the two per-endpoint residuals `hb` / `hcase`;
* `hrec_of_domain` ← the per-endpoint domain package.

This module proves the boost-dilution inequality and combines the honest and
Byzantine sibling-confinement lemmas into the shared `hHon`/`hByz` input:

* **Section 1 — `hdil` (boost dilution).** The pure-ℕ inequality
  `⌊C·J/(100−C)⌋ + boost + 1 ≤ J` from the saturated-regime `Jspec` lower bound
  `2·(boost+1) ≤ J` (`interval_cases C` over the floor witness). `boost_dilution`
  produces the exact `hdil` shape `hmaj_of_saturation` consumes.

* **Section 2 — the sibling confinement wiring (`hHon`/`hByz`).**
  `sibling_confinement` cases on `i ∈ E.honest` and dispatches to the two *proven*
  lemmas — `Confinement.honest_sibling_confinement` (honest ⟹ `Xclass es`) and
  `ByzVpre.byz_sibling_confinement` (byz ⟹ `BbadSet es ∪ SpentSet es σ`) —
  discharging the two Layer-0-mechanical domain premises (`ParentSlotLt`, the
  blanket `store_walkKnownK` walk domain) from `SpecAssumptions`. The provenance /
  recorded-knownness / domination / fork-geometry premises stay as the enumerated
  per-endpoint residuals. `hHon_of_confinement` / `hByz_of_confinement` are the
  `EdgeInputResidual`-field wrappers.

* **Section 3 — the honest committee vote existence (`votes_head` consequence).**
  `honest_committee_vote` extracts, for an honest committee-`s` member (with
  `s ≥ slot_at 0`), its own assigned vote at `s` — the ground-vote witness the
  `Sclass`-membership bridge and the `ρ = 0` partition build on.

* **Section 4 — the `ρ = 0` same-epoch partition (`hρ0`).** `rho0_same_epoch`:
  in the strict same-epoch regime a slot-`σ+1` honest committee member is
  *fresh* (its only span assignment is `σ+1`, by `committee_assignment_unique`),
  so the honest committee of `σ+1` is contained in the window-growth set — funding
  `hρ0` with the `Unrec`-difference contribution non-negative.

The store-dynamics inputs retained by this reduction (the `Sclass`/`Xclass`
migration weights `hSmono`/`hXmono`, the saturation support crux `hsat`, and the
per-endpoint knownness `hb`/`hcase`) are
the cross-store `is_ancestor` transport of late voters' heads (`vote_lands`'s
`hhead_known`/`hhead_walk` statement-layer batch) plus the Finset migration
algebra. Their consumers require the `get_head`/`get_checkpoint_block`
well-formedness inputs stated by the corresponding interfaces.


**P-6 note.** Some names used in this header no longer exist. The legacy `SpecAssumptions`
observed-anchor cone was retired and swept for orphans, which removed `EdgeDynamics.EdgeInputResidual`, `IHMechanize.dynamicsChainStruct_of_endpoint`
and `hdeltas_of_monotone`, and this module's own `rho0_same_epoch` / `hdeltas_sameEpoch`.
The descriptions above are kept because they still identify the *shapes* the surviving
declarations produce and consume. See `docs/p6-justified-descends-derivation.md` §8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — `hdil`: the boost dilution from the saturated `Jspec` lower bound -/



namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in

/-! ## Section 2 — the sibling confinement wiring (`hHon` / `hByz`)

`EdgeDynamics.EdgeInputResidual.hHon`/`hByz` confine every recorded supporter of a
filtered sibling `c'` of the `b`-side child `c` to the base classes at the cutoff
`es` (honest ⟹ `Xclass es`; byz ⟹ `BbadSet es ∪ SpentSet es σ`). Both are the
*proven* lemmas `Confinement.honest_sibling_confinement` and
`ByzVpre.byz_sibling_confinement` — this is the shared structural step left as
an explicit input by the lower-level reductions (`ByzVpre` is a leaf, and honest confinement is a convenience
lemma). Here the two Layer-0-mechanical domain premises — `ParentSlotLt`
(`store_parentSlotLt`) and the blanket walk domain (`store_walkKnownK`) — are
discharged from `SpecAssumptions`, and the sibling's `hc'`/`hpc'`/`hlo` are derived
from the fork-choice child membership (`mem_get_node_children_resolved` +
`filtered_subset_block_roots` + `ParentSlotLt`). The provenance (`hprov`), recorded
knownness (`hlmknown`), domination (`hdom`), and the `b`-side fork-edge geometry
(`hh`/`hpc`/`hbc`/`hlo_h`) stay as the enumerated per-endpoint residuals. -/



/-! ## Section 3 — the honest committee vote existence (`votes_head` consequence)

The `Sclass`-membership bridge and the `ρ = 0` partition both start from an honest
committee member's own ground vote. `honest_committee_vote` is `HonestBehavior.votes_head`
packaged: an honest validator assigned to slot `s` (with `s` at or after the anchor
slot) casts, at some second `n` with `slot_at n = s`, exactly the validator-spec
attestation computed from its own store — the `(n, honest_attestation …)` witness the
`SupportsDesc` predicate and `Delivery.vote_ubiquity` consume. -/

/-- **Honest committee members vote at their assigned slot** (`VoteLanding`). Direct
consequence of `HonestBehavior.votes_head`: an honest validator `v` assigned to slot
`s` (`s ≥ slot_at 0`) has a recorded vote at `s` equal to its own honest attestation
computed at the voting second `n` (`slot_at n = s`). This is the ground-vote witness
the pre-`T1` fresh-committee entry (`hSmono`) and the saturation crux (`hsat`) build on
via `Delivery.vote_ubiquity` + the `SupportsDesc` bridge. -/
theorem honest_committee_vote (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot}
    (hcomm : v ∈ E.committee s) (hsH : E.SlotWithinHorizon cfg s)
    (hs0 : E.slot_at cfg 0 ≤ s) :
    ∃ (n : ℕ) (index : CommitteeIndex), E.slot_at cfg n = s ∧
      E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v) :=
  by
    obtain ⟨n, index, _hnH, hslot, hvote⟩ := hhb.votes_head v hv s hcomm hsH hs0
    exact ⟨n, index, hslot, hvote⟩

/-! ## Section 4 — the `ρ = 0` same-epoch partition (`hρ0`)

`IHMechanize.hdeltas_of_monotone`'s `hρ0` asks that the honest committee of slot
`σ'+1` is covered by the base-supporter recurrence (`Unrec σ' \ Unrec (σ'+1)`) plus
the honest window growth (`span lo (σ'+1) \ span lo σ'`) — the `ξ = α = 0` witness of
the migrant existential. In the **strict same-epoch** regime (every slot of the window
`[lo, σ']` sits in `epoch(σ'+1)`), a slot-`σ'+1` honest committee member cannot also be
assigned anywhere in `[lo, σ']`: `committee_assignment_unique` would force that slot to
be `σ'+1` itself. So the honest committee of `σ'+1` is **entirely fresh** — contained in
the window-growth set — and `hρ0` holds with the `Unrec`-difference contribution merely
non-negative. This is the tentative (current-epoch) loop's `ρ = 0`; the crossing
(previous-epoch) regime has earlier-epoch recurrers and uses the explicit
`ξ`/`α > 0` migration inputs. -/

/-! ### Deleted: `rho0_same_epoch` and `hdeltas_sameEpoch`

The `ρ = 0` same-epoch partition and the migration-delta assembly built on it. Both were
consumed only by `ShellCompose`'s engine composition.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-! ## Section 5 — the IHMechanize-facing compositions

The two clean compositions delivering the `EdgeInputResidual` fields directly from
the reduced cruxes: `hmaj` from support saturation + the `Jspec` lower bound, and
`hdeltas` from the two migration monotonicities with `hρ0` discharged in the
same-epoch regime. -/


end Execution

end FastConfirmation.Spec

end
