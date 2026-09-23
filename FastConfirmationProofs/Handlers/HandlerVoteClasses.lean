module
public import FastConfirmationProofs.Discount.ByzantineBudgetLedger

@[expose] public section

/-! Proves vote class facts across handler steps. -/

/-!
# Spec / Proof / StepDischargeII

This module contains `classes_base_transport_honest` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — class base transport (§10-A)

At the cutoff `es`, every relevant vote is pre-`es`, its block known at both the
confirming store `(v₀, n₀)` and the endpoint store `(w, m)`. The forward
`is_ancestor` transport (`EngineTransport.is_ancestor_transport`, whose per-witness
instances the shell discharges from `block_relay` known-ness) makes the descent
predicates `SupportsDesc` / `AncestorOrVoteless` monotone `(v₀, n₀) → (w, m)`, hence:
`Sclass`/`Aclass` **grow** and `Xclass` **shrinks** across anchors. The base enemy
`BbadSet` shrinks too, given the equivocator containment `equivocating@(v₀,n₀) ⊆
equivocating@(w,m)` (`attester_slashing_relay`'s forward-evidence shape). The
transport implications are taken as the ∀-quantified `is_ancestor_transport`-shaped
hypotheses `hSt`/`hAt`; the shell instantiates them per supporter. -/



/-! ### Note (`recorded-base reduction`): the recorded base enemy does **not** transport across anchors.

With `LedgerV2.BbadSet` in its **recorded** form, its sibling-ward guard reads the
store's recorded latest message. A byzantine validator has no `no_forgery`, so its
recorded message at the endpoint `(w, m)` is unrelated to the one at the confirming
anchor `(v₀, n₀)` (targeted-gossip: a sibling-ward vote at a window slot `≤ es` may be
delivered to `w` but withheld from `v₀`). Hence `BbadVal@(w,m) ≤ BbadVal@(v₀,n₀)` is
**not derivable** from the ground descent transports `hSt`/`hAt` (which constrain
honest votes only) nor from the equivocator relay `hequiv`. The enemy-weight movement
is therefore carried as an explicit residual `hBb` on the base transport below (it
replaces the equivocator-relay slot the old ground-vote `BbadSet` consumed); only the
honest legs (`Sclass` grows, `Xclass` shrinks) transport from `hSt`/`hAt`. -/

/-! ## Section 2 — the `INV2` base transport (§10-A headline) -/





/-- Honest-window form of `classes_base_transport`.  `Sclass`/`Xclass`
already filter to `E.honest ∩ span_committee lo es`, so no transport statement
about Byzantine ground votes is needed (or implied by synchrony). -/
theorem classes_base_transport_honest
    (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root) (lo es : Slot)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v₀ n₀ b' es i →
        E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
        E.AncestorOrVoteless cfg ext w m b' es i) :
    E.Sval cfg ext v₀ n₀ b' lo es ≤ E.Sval cfg ext w m b' lo es ∧
      E.Xval cfg ext w m b' lo es ≤ E.Xval cfg ext v₀ n₀ b' lo es := by
  classical
  constructor
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hS => hi.2.1 (hSt i hi.1.2 hi.1.1 hS),
      fun hA => hi.2.2 (hAt i hi.1.2 hi.1.1 hA)⟩









end Execution

end FastConfirmation.Spec

end
