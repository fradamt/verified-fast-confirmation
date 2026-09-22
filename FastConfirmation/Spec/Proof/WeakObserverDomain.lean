module
public import FastConfirmation.Spec.Proof.WeakOneShotSafety

@[expose] public section

/-!
# Spec / Proof / WeakObserverDomain

Scaffolding for the `hfilter`-discharge wave (stage S0): the observer-side
twins of the two `MinimalSelectedDomain` store-domain helpers which the
accepted filter-supply stack consumes at the *query* node.

Across the accepted stack the query node's honesty binder `hv : v ∈ E.honest`
is only ever consumed in three ways: a synchrony relay, committee readback
(`ExternalsCoherence.committees_agree`), and justified-root knownness
(`SelectedMarginDomain.justified_root_known`, reached either directly or
through `store_domainK_of_selectedMarginDomain` /
`head_root_known_of_selectedMarginDomain`). The last two are exactly the two
fields of `Execution.ObserverCoherence` (`WeakOneShotSafety.lean`), so the
`store_domainK` / `head_root_known` hubs can be re-derived at an arbitrary
(not necessarily honest) observer with no relay and no honesty.

Three declarations:

* `Execution.storeDomainParentWalk` — the honesty-free `ParentSlotLt` plus
  target-known `WalkKnown` pair, factored out of
  `Execution.store_domainK_of_selectedMarginDomain`
  (`MinimalSelectedDomain.lean:142`). Both components are `store_parentSlotLt`
  and `store_walkKnownK`, which are already proved for an arbitrary node and
  second; only the third component of `StoreDomainK` (justified-root
  knownness) ever needed the honest-store domain fact.
* `Execution.head_root_known_at_observer` — the honesty-free half of
  `Execution.head_root_known_of_selectedMarginDomain`
  (`MinimalSelectedDomain.lean:157`), via the `get_head_root_mem_or` idiom
  already used at `WeakOneShotSafety.lean:1012` and
  `WeakSelectedEdgeGeometry.lean:200`, with
  `ObserverCoherence.justified_root_known` in place of
  `SelectedMarginDomain.justified_root_known`.
* `Execution.observerStoreDomainK` — the observer-side `StoreDomainK` twin,
  assembled from the two above. Its conclusion is the body of
  `Execution.StoreDomainK` (`AnchorFacade.lean:376`) specialized to the
  single pair `(obs, m)`, so it destructures exactly like the
  `⟨hparent, hwalk, hjustified⟩` results of
  `store_domainK_of_selectedMarginDomain` at accepted call sites.

Nothing here depends on the weak selector rule; the file sits on
`WeakOneShotSafety` purely for `ObserverCoherence`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The honesty-free pair inside `store_domainK_of_selectedMarginDomain`:
parent-slot order and the target-known walk domain, at an arbitrary node and
second. Neither component consults `E.honest`. -/
theorem storeDomainParentWalk
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (w : ValidatorIndex) (m : ℕ) :
    ParentSlotLt (E.store cfg ext w m) ∧
      (∀ t ∈ (E.store cfg ext w m).block_roots,
        ∀ r ∈ (E.store cfg ext w m).block_roots,
          WalkKnown (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks t).slot r) :=
  ⟨E.store_parentSlotLt cfg ext hwf hec hgen
      hwf.anchor_parent_unscheduled w m,
    E.store_walkKnownK cfg ext hwf hec hgen w m⟩

/-- `get_head`'s root is known at an arbitrary observer's own store: either
the executable head is a genuine block, or it is the justified-root fallback,
which `ObserverCoherence.justified_root_known` keeps in the block map. This is
`head_root_known_of_selectedMarginDomain` with the honest-store domain fact
replaced by the observer's own coherence field. -/
theorem head_root_known_at_observer
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    (m : ℕ) (hH : E.WithinHorizon cfg m) :
    (get_head cfg (E.store cfg ext obs m)).root ∈
      (E.store cfg ext obs m).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext obs m) with h | h
  · exact h
  · rw [h]
    exact hcoh.justified_root_known m hH

/-- The observer-side `StoreDomainK` twin: the `StoreDomainK` body at the
single pair `(obs, m)`, with the honest-node quantifier dropped. The first two
components are `storeDomainParentWalk`, the third is
`ObserverCoherence.justified_root_known`. -/
theorem observerStoreDomainK
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    (m : ℕ) (hH : E.WithinHorizon cfg m) :
    ParentSlotLt (E.store cfg ext obs m) ∧
      (∀ t ∈ (E.store cfg ext obs m).block_roots,
        ∀ r ∈ (E.store cfg ext obs m).block_roots,
          WalkKnown (E.store cfg ext obs m)
            ((E.store cfg ext obs m).blocks t).slot r) ∧
      (E.store cfg ext obs m).justified_checkpoint.root ∈
        (E.store cfg ext obs m).block_roots :=
  ⟨(E.storeDomainParentWalk cfg ext hwf hec hgen obs m).1,
    (E.storeDomainParentWalk cfg ext hwf hec hgen obs m).2,
    hcoh.justified_root_known m hH⟩

end Execution

end FastConfirmation.Spec

end
