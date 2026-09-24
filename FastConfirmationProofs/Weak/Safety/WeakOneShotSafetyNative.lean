module
public import FastConfirmationProofs.Weak.Discount.WeakCoveredMarginConstruction
public import FastConfirmationProofs.Weak.Safety.WeakFinalizedInput

@[expose] public section

/-!
# Spec / Proof / WeakOneShotSafetyNative

Margin-discharge wave, Stage J-f (design §2/J5): the weak-native chain-supply
and `SafeFrom` sections, and the headline discharged corollary.

These are line-for-line clones of `WeakOneShotSafety.lean`'s existing
Sections 4–6 (`coveredDescendStepChainSupply_of_selectedMarginsAt_weak`,
`safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak`,
`weak_safeFrom_find_latest_confirmed_descendant`), over
`Weak.SelectedCoveredMarginSupplyAt` (Stage J-a,
`WeakSelectedMarginInputs.lean`) instead of the strong
`SelectedCoveredMarginSupplyAt`, and over the three weak `DescendStep`
producers instead of the strong/`_at_observer` ones.

This content cannot live inside `WeakOneShotSafety.lean` itself: that file is
imported (for `WeakObserverMarginPremises`/`ObserverCoherence`) by
`WeakSelectedEdgeGeometry.lean`, which `WeakCoveredMarginConstruction.lean`
(the weak supplier, Stage J-e) imports in turn, and the headline theorem below
needs that supplier — adding the reverse edge would make the import graph
cyclic. Placing this content in a new file downstream of the whole weak
margin-input/supplier stack (importing `WeakCoveredMarginConstruction.lean`)
keeps the acyclic import discipline while landing exactly the theorems Stage
J-f calls for, and its docstrings continue to reference `WeakOneShotSafety.lean`
Sections 4–6 as the pattern being cloned. The slot-start bridge
(`safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak`) is
margin-supply-agnostic — its own statement never mentions
`SelectedCoveredMarginSupplyAt` — so its "native" twin below is a thin,
zero-cost alias of the existing theorem rather than a fresh proof.

**Headline: `weak_safeFrom_find_latest_confirmed_descendant_discharged`.**
Composed with `Weak.selectedCoveredMarginSupplyAt_of_filterSupply_at_observer`
(Stage J-e), this discharges the `hmargin` premise entirely: the only
premises left are `hwalkDomain` (endpoint-side only, `F4`), `hfilter` (the
FFG-realization filter supply — S10, the next wave), and
`ObserverCoherence`/`WeakObserverMarginPremises` (the observer's own store
coherence, honesty-free).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 4′ — the weak-native covered chain-supply

Clone of `coveredDescendStepChainSupply_of_selectedMarginsAt_weak`, over
`Weak.SelectedCoveredMarginSupplyAt`. The `sameEpoch` and `directWindow`
branches route through the Stage J-a producers
(`Weak.sameEpoch_descendStep_of_selectedInputsAt` /
`Weak.directWindow_descendStep_of_selectedInputsAt`); the merged crossing
branch (`F3`: three constructors, not four) routes through
`Weak.crossing_descendStep_of_selectedInputs_at_observer`. -/

theorem coveredDescendStepChainSupply_of_selectedMarginsAt_weak_native
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginPremises cfg ext obs)
    {glc r₀ : Root} {q : ℕ}
    (hqH : E.WithinHorizon cfg q) (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext obs q)
    (hglc : glc ∈ (E.store cfg ext obs q).block_roots)
    (hparent : ((E.store cfg ext obs q).blocks glc).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true)
    (hsupply : Weak.SelectedCoveredMarginSupplyAt cfg ext E glc r₀ obs q query) :
    E.CoveredDescendStepChainSupply cfg ext glc r₀
      (E.slot_start cfg (E.slot_at cfg q)) := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  obtain ⟨_hsq, _hsH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  intro w hw m hm hHm hIH a c ha hc hlink hscope hscopeR₀ hcne
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotStart]
    exact E.slot_at_mono cfg hm
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hHm'
    have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m' := by
      rw [← hslotStart]
      exact E.slot_at_mono cfg hm'
    exact E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hW.validity hcomm query hstore glc hqH hglc hparent hconf
      w' hw' m' hslotQM' hHm'
  rcases hsupply w hw m hslotQM hHm hIH
      a c ha hc hlink hscope hscopeR₀ hcne with hcovered | hmargin
  · exact Or.inl hcovered
  · right
    rcases hmargin with
      ⟨lo, es, σ, hsame⟩ | ⟨es, σ, querySlot, hcrossing⟩ | ⟨lo, es, hdirect⟩
    · exact Weak.sameEpoch_descendStep_of_selectedInputsAt cfg ext hA
        hw hHm hc hscope hglcKnown hIH hsame
    · exact Weak.crossing_descendStep_of_selectedInputs_at_observer cfg ext hW
        hqH hw hHm hcrossing
    · exact Weak.directWindow_descendStep_of_selectedInputsAt cfg ext hdirect

/-! ## Section 5′ — the weak-native slot-start bridge

The slot-start bridge is margin-supply-agnostic (its own statement never
mentions `SelectedCoveredMarginSupplyAt`, only the already-built
`CoveredDescendStepChainSupply`), so the "native" form is a zero-cost alias of
`safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak`. -/

theorem safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak_native
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginPremises cfg ext obs)
    (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ query.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr
      (E.slot_start cfg (E.slot_at cfg q)))
    (hchain :
      Weak.find_latest_confirmed_descendant cfg ext query lcr ≠ lcr →
        E.CoveredDescendStepChainSupply cfg ext
          (Weak.find_latest_confirmed_descendant cfg ext query lcr) lcr
          (E.slot_start cfg (E.slot_at cfg q))) :
    E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext query lcr)
      (E.slot_start cfg (E.slot_at cfg q)) :=
  E.safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak cfg ext hW
    q hqH query hstore lcr hlcr hbase hchain

/-! ## Section 6′ — the one-shot weak-native safety theorem

Clone of `weak_safeFrom_find_latest_confirmed_descendant`, with `hmargin`
stated over `Weak.SelectedCoveredMarginSupplyAt` instead of the strong
`SelectedCoveredMarginSupplyAt`. -/

theorem weak_safeFrom_find_latest_confirmed_descendant_native
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginPremises cfg ext obs)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hmargin : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
        Weak.SelectedCoveredMarginSupplyAt cfg ext E
          (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
          fcr_store) :
    E.SafeFrom cfg ext (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) q := by
  have hA := hW.base
  have hjrk : (E.store cfg ext obs q).justified_checkpoint.root ∈
      (E.store cfg ext obs q).block_roots :=
    hW.coherence.justified_root_known q hqH
  have hslotSafety : E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)
      (E.slot_start cfg (E.slot_at cfg q)) :=
    E.safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak_native
      cfg ext hW q hqH fcr_store hstore lcr hlcr hbase (by
        intro hne
        have hkey : is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store)
            (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) = true ∧
          Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
            fcr_store.store.block_roots ∧
          (fcr_store.store.blocks
              (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)).parent_root ∈
            fcr_store.store.block_roots := by
          rcases E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext hA
              obs q hqH hjrk fcr_store hstore lcr hlcr with
            heq | ⟨hc, _hwc, hb, hp, _hguard⟩
          · exact absurd heq hne
          · exact ⟨hc, hb, hp⟩
        obtain ⟨hconf, hb, hp⟩ := hkey
        have hb' : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
            (E.store cfg ext obs q).block_roots := by
          simpa only [hstore] using hb
        have hp' : ((E.store cfg ext obs q).blocks
              (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)).parent_root ∈
            (E.store cfg ext obs q).block_roots := by
          simpa only [hstore] using hp
        exact E.coveredDescendStepChainSupply_of_selectedMarginsAt_weak_native
          cfg ext hW hqH fcr_store hstore hb' hp' hconf (hmargin hne))
  obtain ⟨hstart, _hstartH, _hslot, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  exact hslotSafety.mono cfg ext E hstart

/-! ## Section 7′ — the headline: `hmargin` discharged

Composed with the Stage J-e supplier
(`Weak.selectedCoveredMarginSupplyAt_of_filterSupply_at_observer`), nothing in
the weak one-shot path assumes delivery of votes TO the observer. The only
premises left are `hwalkDomain` (endpoint-side, `F4`), the observer's own
store coherence (`hW`), and `hfilter` — the FFG-realization filter supply,
S10's target. -/

theorem weak_safeFrom_find_latest_confirmed_descendant_discharged
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginPremises cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hfilter : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
      Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
        fcr_store) :
    E.SafeFrom cfg ext (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) q :=
  E.weak_safeFrom_find_latest_confirmed_descendant_native cfg ext hW q hqH fcr_store hstore
    lcr hlcr hbase (fun hne =>
      Weak.selectedCoveredMarginSupplyAt_of_filterSupply_at_observer cfg ext hW.base
        hwalkDomain hW q hqH fcr_store hstore lcr hlcr
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) rfl hne (hfilter hne))

/-- Endpoint form of the discharged headline: the weak selector's output,
read at an arbitrary (not necessarily honest) observer's store, is canonical
at every honest endpoint at or after the query second — with `hmargin`
discharged into `hfilter`. -/
theorem weak_confirmed_head_discharged
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginPremises cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hfilter : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
      Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
        fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : q ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr))
      = true :=
  weak_safeFrom_find_latest_confirmed_descendant_discharged cfg ext hW hwalkDomain q hqH
    fcr_store hstore lcr hlcr hbase hfilter w hw m hqm hHm

/-! ## Section 8′ — the finalized-base composition, discharged

Cheap plumbing composition of `WeakFinalizedInput.weak_safeFrom_find_latest_
confirmed_descendant_from_finalized` with the Section 7′ headline: identical
derivation of `hlcr`/`hbase` from the accepted FFG semantics bundle, with the
final call to `weak_safeFrom_find_latest_confirmed_descendant` replaced by
`weak_safeFrom_find_latest_confirmed_descendant_discharged`, so `hmargin`
becomes `hfilter`. -/

/-- Finalized-base corollary of the discharged headline: the weak selector's
output, seeded at the observer's own finalized checkpoint, is `SafeFrom` at
the actual query second, with `hmargin` discharged into `hfilter`.

Observer-wise the premise surface is `hW : WeakObserverPremises` — the
floor, `obs ∉ E.honest`, and committee readback at the observer's own store.
Since `B`/`hanchor`/`hboundary` are carried here anyway (and `hT` is derived
from `hW.base`), `ObserverCoherence.justified_root_known` is *derived* via
`WeakObserverPremises.toMarginAssumptions`, not assumed. -/
theorem weak_safeFrom_find_latest_confirmed_descendant_discharged_from_finalized
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (hfilter :
      Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root ≠
        fcr_store.store.finalized_checkpoint.root →
      Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)
        fcr_store.store.finalized_checkpoint.root obs q fcr_store) :
    E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store
        fcr_store.store.finalized_checkpoint.root) q := by
  have hT := ScheduledPrefixPremises.of_selectedMarginAssumptions
    cfg ext E hW.base hW.genesis
  have hacc := SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    cfg ext E hW.base
  have hlcr : fcr_store.store.finalized_checkpoint.root ∈
      fcr_store.store.block_roots := by
    rw [hstore]
    exact (E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) q).root_known
  have hbase : E.SafeFrom cfg ext fcr_store.store.finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)) := by
    rw [hstore]
    exact E.weak_finalizedReset_safeFrom_of_synchrony cfg ext B hT hacc hphase
      hboundaryPhase hanchor hboundary hW.base.synchrony hqH
  -- the observer's `justified_root_known` is derived from `B`/`hT`/`hanchor`/
  -- `hboundary`, all already carried here, rather than assumed
  have hWM := hW.toMarginAssumptions cfg ext E B hT hanchor hboundary
  exact weak_safeFrom_find_latest_confirmed_descendant_discharged cfg ext hWM hwalkDomain q hqH
    fcr_store hstore fcr_store.store.finalized_checkpoint.root hlcr hbase
    hfilter

/-- Endpoint form of the discharged finalized-base corollary. -/
theorem weak_confirmed_head_discharged_from_finalized
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (hfilter :
      Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root ≠
        fcr_store.store.finalized_checkpoint.root →
      Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)
        fcr_store.store.finalized_checkpoint.root obs q fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : q ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)) = true :=
  weak_safeFrom_find_latest_confirmed_descendant_discharged_from_finalized cfg ext hW
    hwalkDomain B hanchor hboundary hphase hboundaryPhase q hqH fcr_store hstore hfilter
    w hw m hqm hHm

end Execution

end FastConfirmation.Spec

end
