module
public import FastConfirmation.Spec.Proof.AheadFacade
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.HeadStack
public import FastConfirmation.Spec.Proof.IHMechanize

@[expose] public section

/-!
# Spec / Proof / FinalWiring: residual wiring (mostly retired)

This module wired the former `JustificationInterface.unrealized_justified` export and the two
mechanical E5-reset anchor obligations into the conditional `Spec_Safety` input records. Those
records went with the legacy `SpecAssumptions` observed-anchor cone (P-6), and six of this
module's seven declarations —
`prev_greatest_of_interface`, `justified_dom_of_descent`, `genesis_dom_of_interface`,
`finalized_dom_of_known`, `finalized_root_relay_known` and `dynamics_struct_of_suppliers` — went
with them in the orphan sweep. See the section note below and
`docs/p6-justified-descends-derivation.md` §8.

What is delivered now is `hb_of_confirming`: the later-slot half of the confirmed block's
endpoint knownness, from `Synchrony.block_relay` via `HeadStack.b_known_of_relay`. The
**same-slot cross-node** membership stays outside the block-relay guarantee, because
`block_relay` has a `+1`-slot gate.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the deleted `prev_greatest` leg -/

/-! ### Deleted: the E5 reset-anchor wiring and the `dynamics_struct` assembly

`prev_greatest_of_interface`, `justified_dom_of_descent`, `genesis_dom_of_interface`,
`finalized_dom_of_known`, `finalized_root_relay_known` and `dynamics_struct_of_suppliers`
stood here: they built the three E5 reset legs and the structural confirmed chain for the
conditional `Spec_Safety` routes. `hb_of_confirming` below is unaffected.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8.

`prev_greatest_of_interface` was the **only** projection site in the development of
`JustificationInterface.unrealized_justified`; with it gone the field was unmentioned
anywhere, and it has since been deleted too (P-4, 13 → 12 fields). See
`docs/p4-unrealized-justified-derivation.md`. -/

/-! ## Section 2 — the E5 reset anchors: `genesis_dom` and `finalized_dom`

Both reset fields carry two conjuncts: the anchor root is known at `(w, m)`, and the store's
justified checkpoint dominates it (`jc(w,m) ⪰ r₀`). The dominance is the same composition for
both: `finalized_justified_ancestry` puts the store's own finalized block on its justified
chain (`finalized(w,m) ⪯ jc(w,m)`), and `finalized_descent` puts the reset anchor below the
store's finalized (`r₀ ⪯ finalized(w,m)`); `is_ancestor_trans` on the target-known walk domain
(`store_walkKnownK`, `r₀` the known target) composes them. -/

/-! ## Section 3 — `dynamics_struct` from the two per-endpoint suppliers

`IHMechanize.dynamicsChainStruct_of_endpoint` reduces `DynamicsChainStruct b (n+1)` to `hb`
(the confirmed `b` is relay-known at each honest endpoint under the shell IH) and `hcase` (the
L4 loop-inversion descent). `dynamics_struct_of_suppliers` lifts that to the field shape of
`StrongPrefixSafetyInputs.dynamics_struct` — per `is_one_confirmed` block, apply the endpoint lemma
to the two supplied families. `hb_of_confirming` discharges `hb` at the later-slot regime from
the confirming-store knownness via `HeadStack.b_known_of_relay`; the same-slot cross-node case
and `hcase` are supplied explicitly as cross-store inputs. -/

/-- **`hb`, later-slot, from confirming-store knownness.** Given the confirmed
`b` is a known block at its confirming store `(v, n+1)` (`hbconf`), `HeadStack.b_known_of_relay`
lands it at every honest endpoint `(w, m)` at the later-slot regime `slot_at (n+1) + 1 ≤
slot_at (m+1)`. This discharges `dynamics_struct_of_suppliers`' `hb` off the same-slot corner;
the same-slot cross-node case is the documented block-relay reach limit. -/
theorem hb_of_confirming (hsyn : Synchrony cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {n m : ℕ} {b : Root} (hbconf : b ∈ (E.store cfg ext v (n + 1)).block_roots)
    (hHn1 : E.WithinHorizon cfg (n + 1)) (hHm : E.WithinHorizon cfg m)
    (hgap : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) :
    b ∈ (E.store cfg ext w m).block_roots :=
  E.b_known_of_relay cfg ext hsyn hv hw hbconf hHn1 hHm hgap

/-! ## Section 4 — ground-truth base-enemy bounds

The base transport routes through `FastConfirmation/Spec/Proof/GroundBeta.lean`:
`bval_endpoint_strip_of_transport` / `ledger_descendStep_groundBeta` bound the endpoint enemy
by the **store-independent** ground-truth window weight `Bval(es)` (`span_fraction`-budgeted at
the endpoint directly — no relay, no subset, no `hBb`), closing the per-fork descent at every
slot regime with only the honest transports. -/

end Execution

end FastConfirmation.Spec

end
