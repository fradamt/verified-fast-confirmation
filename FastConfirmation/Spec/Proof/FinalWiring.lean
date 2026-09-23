module
public import FastConfirmation.Spec.Proof.AheadFacade
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.HeadStack
public import FastConfirmation.Spec.Proof.IHMechanize

@[expose] public section

/-!
# Spec / Proof / FinalWiring

This module contains `hb_of_confirming` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `prev_greatest` from `unrealized_justified` -/


/-! ## Section 2 — the E5 reset anchors: `genesis_dom` and `finalized_dom`

Both reset fields carry two conjuncts: the anchor root is known at `(w, m)`, and the store's
justified checkpoint dominates it (`jc(w,m) ⪰ r₀`). The dominance is the same composition for
both: `finalized_justified_ancestry` puts the store's own finalized block on its justified
chain (`finalized(w,m) ⪯ jc(w,m)`), and `finalized_descent` puts the reset anchor below the
store's finalized (`r₀ ⪯ finalized(w,m)`); `is_ancestor_trans` on the target-known walk domain
(`store_walkKnownK`, `r₀` the known target) composes them. -/








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



end Execution

end FastConfirmation.Spec

end
