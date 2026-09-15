import FastConfirmation.Spec.Proof.SelectedPreQueryHistoricalSIR
import FastConfirmation.Spec.Proof.WeakSelectedStrictEdgeFilterSupply

/-!
# Spec / Proof / WeakPreQuerySIR

Stage S8 of the `hfilter`-discharge wave: observer twins of the *pre-query
selected-input-region* (SIR) bracket layer
(`SelectedPreQuerySIR.lean` → `SelectedPreQueryAnchor.lean` →
`SelectedPreQueryHistoricalSIR.lean`), re-proved at a possibly-Byzantine
observer `obs` carrying only `E.ObserverCoherence cfg ext obs`
(`WeakOneShotSafety.lean`) and running the weak selector
(`Weak.find_latest_confirmed_descendant`).

This is the chain `WeakSelectedStrictEdgeFilterSupply.lean`'s module docstring
names as the source of its carried fields `result_descends_endpoint_justified`
and `endpoint_justified_epoch_le_result`.

## Reused verbatim from the strong modules (no twin needed)

* `Execution.known_descends_trustedAnchor` (`SelectedPreQueryAnchor.lean:38`)
  and `Execution.selectedSIRThreeRegionBracket_of_trustedAnchor_known` (`:125`)
  — neither mentions `E.honest` at all; both are indexed at a bare `(w, m)`.
* `Execution.PreQueryVoteSelectedSIRBracketAt` (`:267`),
  `Execution.PreQuerySelectedSIRBracketAt`,
  `Execution.PreQueryTargetOriginAt`,
  `Execution.PreQuerySelectedJustifiedCompatibilityAt` — all four are
  honesty-free `Prop` definitions over the endpoint `(w, m)` and an abstract
  `selected : Root`, so the weak selector's output is simply plugged in.
* `Execution.postAnchorHonestTargetGeometryAt_of_vote` (`:157`),
  `Execution.preQueryVote_belowInput_of_safeInput` (`:577`),
  `Execution.postAnchorPreQueryTarget_epoch_le_query`,
  `Execution.preQueryTarget_epoch_lt_query_of_epochStart`,
  `Execution.middleRegion_forces_current`,
  `Execution.aboveSelectedRegion_forces_previous`,
  `Execution.currentEpochBlock_descends_currentTarget`,
  `Execution.currentTarget_descends_previousEpochBlock` — every honesty binder these
  consume is at the *honest voter* `i` or the *honest endpoint* `(w, m)`,
  which the weak development keeps honest.
* `Weak.strictSelectedResultMechanicalFacts` (`WeakSelectedTrace.lean:818`) —
  the observer twin of `SelectedPreQuerySIR.strictSelectedResultMechanicalFacts`
  already landed at stage S2; this module consumes it rather than re-proving it.

## The substitutions

Per the wave's stage-S0 audit the query node's honesty resolves to three
substitutable uses plus two receiver-side relays and one honest-quantified
premise instantiated at the query node:

* `store_domainK_of_selectedMarginDomain … v hv q hqH` →
  `Execution.observerStoreDomainK` and
  `head_root_known_of_selectedMarginDomain … hv` →
  `Execution.head_root_known_at_observer` (`WeakObserverDomain.lean`), both
  driven by `hcoh`;
* `find_latest_confirmed_descendant_selected_minimal` /
  `find_latest_confirmed_descendant_ge` → the weak selector inversions
  `Execution.find_latest_confirmed_descendant_selected_minimal_weak` /
  `weak_find_latest_confirmed_descendant_ge` (`WeakSelectorInversion.lean`);
* `confirmed_ancestry_at_all_honest_endpoints_minimal … hv` →
  `Execution.confirmed_ancestry_at_all_honest_endpoints_at_observer`
  (`WeakConfirmedDissemination.lean`), fed `hcoh.committees_agree q hqH`;
* the two **receiver-side** relays are deleted rather than substituted. A
  Byzantine observer has no delivery, so
  `SelectedPreQueryHistoricalSIR.preQueryHonestTarget_sourceWitnessAtQuery`
  (`:427`, `E.blockRoots_subset_of_relay`) and
  `MinimalSelectedDomain.ancestry_of_known_honest_past_descendant_minimal`
  (`:484`, `hA.synchrony.block_relay`) are both dropped. Their only joint
  consumer, `preQueryTarget_descends_queryBlock_at_endpoint`, is re-proved
  below as a single containment-free `Execution.is_ancestor_replay_closed`
  (`WeakAncestryEndpoint.lean:43`) once the witness root's endpoint knownness
  is made an explicit hypothesis — which every call site already has in hand.
* `findLatestSelectedResult_below_head cfg ext query … hheadInputQ` (which the
  strong proof feeds from `hbase v hv q hstartQ hqH`, an instantiation of the
  honest-quantified input safety **at the query node**) →
  `Weak.strictSelectedResult_below_head`
  (`WeakEarlyPhaseSourceWiring.lean:147`), which needs no input-safety
  premise at all. `hheadInputQ` itself is then recovered downstream by
  composing that with `Weak.StrictSelectedResultMechanicalFacts.descends_input`.

## Deviation from the stage brief

The brief's audit says `hbase` is used *only* to produce `hheadInputQ`, and
asks for the binder to be deleted. That is not the case: it is used a second
time, at `SelectedPreQueryHistoricalSIR.lean:1164`, as
`preQueryVote_belowInput_of_safeInput cfg ext hA hbase hw hslotQM hHm …`,
where it is instantiated at the **honest endpoint** `w`, not at the query
node. The binder is therefore *kept* in
`Weak.selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning`: `SafeFrom`
quantifies over honest nodes, `w` is honest in both developments, and nothing
about a Byzantine observer weakens that use. Only the query-node
instantiation is removed. Without `hbase` the below-input region of the
bracket is not provable at all — it is exactly the statement that the
selector input sits on the honest endpoint's fork-choice head.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-! ## The trusted-anchor disjunct -/

/-- Observer twin of
`Execution.trustedAnchor_below_strictSelected_at_endpoint`
(`SelectedPreQueryAnchor.lean:161`): a strict **weak** selected call at a
possibly-Byzantine observer still puts both the selector input and its result
above the trusted anchor at every later honest endpoint.

Substitutions: the two query-node domain hubs become
`Execution.observerStoreDomainK` / `Execution.head_root_known_at_observer`,
the selector inversion becomes
`Execution.find_latest_confirmed_descendant_selected_minimal_weak` /
`weak_find_latest_confirmed_descendant_ge`, and the endpoint transport becomes
`Execution.confirmed_ancestry_at_all_honest_endpoints_at_observer` fed
`hcoh.committees_agree`. `Execution.known_descends_trustedAnchor` is reused
verbatim — it carries no honesty at all. -/
theorem trustedAnchor_below_strictSelected_at_endpoint
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    input ∈ (E.store cfg ext w m).block_roots ∧
      Weak.find_latest_confirmed_descendant cfg ext query input ∈
        (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root input) (get_node_for_root anchor.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (Weak.find_latest_confirmed_descendant cfg ext query input))
        (get_node_for_root anchor.root) = true ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m) input ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m)
        (Weak.find_latest_confirmed_descendant cfg ext query input) := by
  let result := Weak.find_latest_confirmed_descendant cfg ext query input
  obtain ⟨hwfQ, hwalkQ, hjustQ⟩ :=
    E.observerStoreDomainK cfg ext hA.wellFormed hA.externals_coherence
      hA.genesis hcoh q hqH
  have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
    have hhead := E.head_root_known_at_observer cfg ext hcoh q hqH
    simpa only [hquery] using hhead
  have hselected := E.find_latest_confirmed_descendant_selected_minimal_weak
    cfg ext hA obs q hqH hjustQ query hquery input hinput
  have hright :
      Spec.is_one_confirmed cfg ext query.store
          (get_current_balance_source query) result = true ∧
        result ∈ query.store.block_roots ∧
        (query.store.blocks result).parent_root ∈
          query.store.block_roots := by
    rcases hselected with heq | hright
    · exact False.elim (hstrict (by simpa only [result] using heq))
    · exact ⟨hright.1, hright.2.2.1, hright.2.2.2.1⟩
  have hresultKnownE : result ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hright.2.1
  have hparentKnownE : ((E.store cfg ext obs q).blocks result).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hright.2.2
  have hinputKnownE : input ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hinput
  have hresultInputQ : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root result) (get_node_for_root input) = true := by
    have hge := weak_find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hquery] using hwfQ)
      (by simpa only [hquery] using hwalkQ)
      hheadQ input hinput
    simpa only [result, hquery] using hge.1
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hcoh.committees_agree q hqH
  obtain ⟨hinputM, hresultM, _hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hquery result input hqH hresultKnownE hparentKnownE
      hinputKnownE hresultInputQ hright.1 w hw m hslotQM hHm
  have hinputAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hinputM
  have hresultAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hresultM
  simpa only [result] using
    ⟨hinputM, hresultM, hinputAnchor.1, hresultAnchor.1,
      hinputAnchor.2, hresultAnchor.2⟩

/-- Observer twin of
`Execution.selectedSIRThreeRegionBracket_of_trustedAnchor_strict`
(`SelectedPreQueryAnchor.lean:235`). The endpoint-local anchor case
`selectedSIRThreeRegionBracket_of_trustedAnchor_known` is reused verbatim: it
is stated at a bare `(w, m)` and consumes no honesty. -/
theorem selectedSIRThreeRegionBracket_of_trustedAnchor_strict
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hjustifiedAnchor :
      (E.store cfg ext w m).justified_checkpoint = anchor) :
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m) input
      (Weak.find_latest_confirmed_descendant cfg ext query input)
      (E.store cfg ext w m).justified_checkpoint := by
  obtain ⟨hinputM, hresultM, _hinputAnchor, _hresultAnchor,
      _hinputEpoch, _hresultEpoch⟩ :=
    Weak.trustedAnchor_below_strictSelected_at_endpoint cfg ext hA hanchor
      hcoh hqH query hquery input hinput hstrict hw hslotQM hHm
  exact E.selectedSIRThreeRegionBracket_of_trustedAnchor_known cfg ext hA
    hanchor hinputM hresultM hjustifiedAnchor

/-- Observer twin of
`Execution.preQuerySelectedSIRBracketAt_of_voteBracket_strict`
(`SelectedPreQueryAnchor.lean:282`): assemble the full
`Execution.PreQuerySelectedSIRBracketAt` from the anchor branch above and the
unchanged pre-query honest-vote remainder. Both
`PreQuerySelectedSIRBracketAt` and `PreQueryVoteSelectedSIRBracketAt` are
honesty-free definitions over `(w, m)`, so they are reused with the weak
selector's output substituted for the strong one. -/
theorem preQuerySelectedSIRBracketAt_of_voteBracket_strict
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvoteBracket : E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m) :
    E.PreQuerySelectedSIRBracketAt cfg ext anchor q input
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m := by
  intro horigin
  rcases horigin with hjustifiedAnchor | hvote
  · exact Weak.selectedSIRThreeRegionBracket_of_trustedAnchor_strict cfg ext
      hA hanchor hcoh hqH query hquery input hinput hstrict hw hslotQM hHm
      hjustifiedAnchor
  · obtain ⟨i, hi, s, k, a, hs0, hsq, hsm, hsH, hvote, htarget⟩ := hvote
    exact hvoteBracket i hi s k a hs0 hsq hsm hsH hvote htarget

/-! ## The exact weak call-site classification -/

/-- Weak twin of `mem_findLatestSelectedTrace_tentative`
(`SelectedFilterBridge.lean:141`), projected to the gate conjunct only.
Needed because `WeakSelectedTrace.lean` landed `mem_tentativeLoopTrace` but no
wrapper-level reader for `Weak.findLatestSelectedTrace`'s tentative edge
list. Every wrapper branch stores either `[]` or a `tentativeLoopTrace`
segment, so the split is discharged uniformly. -/
theorem findLatestSelectedTrace_crossing_currentTargetGate
    (fcrStore : FastConfirmationStore Root) (latestConfirmedRoot a c : Root)
    (h : (a, c) ∈
      (Weak.findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2)
    (hlt : get_block_epoch cfg fcrStore.store a <
      get_block_epoch cfg fcrStore.store c) :
    Weak.will_current_target_be_justified cfg ext fcrStore.store = true := by
  simp only [Weak.findLatestSelectedTrace] at h
  split_ifs at h <;> try simp at h
  all_goals
    exact (mem_tentativeLoopTrace cfg ext fcrStore _ _ a c h).2 hlt

/-- Weak twin of `Execution.StrictSelectedHistoricalSIRCallSite`
(`SelectedPreQueryHistoricalSIR.lean:62`).

Two shape changes, both forced by the weak rule rather than by the observer:
the strong `CurrentTargetAcceptedEdge` abbreviation has no weak twin (stage
S2 landed none), so its two conjuncts are inlined exactly as
`Weak.SelectedHelperProvisosAt` already inlines them; and the executable
gates are the weak-rule booleans
`Weak.will_current_target_be_justified` /
`Weak.will_no_conflicting_checkpoint_be_justified` (the latter taking the
call's balance source, per rule delta 4). No honesty occurs anywhere in the
inductive. -/
inductive StrictSelectedHistoricalSIRCallSite (E : Execution Root)
    (q : ℕ) (query : FastConfirmationStore Root) (input result : Root) : Prop
  | currentCrossing
      (result_current : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store)
      (a c : Root)
      (edge_mem : (a, c) ∈
        (Weak.findLatestSelectedTrace cfg ext query input).2.2)
      (edge_crossing : get_block_epoch cfg query.store a <
        get_block_epoch cfg query.store c)
      (gate : Weak.will_current_target_be_justified cfg ext query.store = true)
      (support : HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q)
  | currentHistorical
      (result_current : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store)
      (no_crossing : ¬ ∃ a c : Root,
        (a, c) ∈ (Weak.findLatestSelectedTrace cfg ext query input).2.2 ∧
          get_block_epoch cfg query.store a <
            get_block_epoch cfg query.store c)
  | previousEpochStart
      (result_previous : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store)
      (at_start : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) = true)
  | previousNoConflict
      (result_previous : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store)
      (not_start : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) ≠ true)
      (gate : Weak.will_no_conflicting_checkpoint_be_justified cfg ext
        query.store (get_current_balance_source query) = true)
      (support : HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q)

/-- Observer twin of
`Execution.strictSelectedHistoricalSIRCallSite`
(`SelectedPreQueryHistoricalSIR.lean:98`).

The whole query-node honesty content of the strong proof lives inside
`strictSelectedResultMechanicalFacts`, which is replaced wholesale by the
stage-S2 `Weak.strictSelectedResultMechanicalFacts`. The two gate/support
extractions become: the crossing gate from
`findLatestSelectedTrace_crossing_currentTargetGate` above, and the
no-conflict gate from the weak mechanical facts' own
`previous_result_outer_guard` field (the weak twin of
`selected_previous_result_no_conflict_gate`); both supports come from
`Weak.SelectedHelperProvisosAt`, the observer-quantified proviso record
landed at stage S7. -/
theorem strictSelectedHistoricalSIRCallSite
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs q query input) :
    StrictSelectedHistoricalSIRCallSite cfg ext E q query input
      (Weak.find_latest_confirmed_descendant cfg ext query input) := by
  let result := Weak.find_latest_confirmed_descendant cfg ext query input
  have hfacts := Weak.strictSelectedResultMechanicalFacts cfg ext hA hcoh hqH
    query hquery input hinput hinputEpoch hstrict
  rcases hfacts.current_or_previous_epoch with hcurrent | hprevious
  · by_cases hcross : ∃ a c : Root,
        (a, c) ∈ (Weak.findLatestSelectedTrace cfg ext query input).2.2 ∧
          get_block_epoch cfg query.store a <
            get_block_epoch cfg query.store c
    · obtain ⟨a, c, hmem, hlt⟩ := hcross
      exact .currentCrossing hcurrent a c hmem hlt
        (Weak.findLatestSelectedTrace_crossing_currentTargetGate cfg ext
          query input a c hmem hlt)
        (hprovisos.current_target a c hmem hlt)
    · exact .currentHistorical hcurrent hcross
  · have hnotCurrent : get_block_epoch cfg query.store result ≠
        get_current_store_epoch cfg query.store := by
      intro heq
      rw [heq] at hprevious
      exact Nat.succ_ne_self _ hprevious
    by_cases hstart : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) = true
    · exact .previousEpochStart hprevious hstart
    · have hgate : Weak.will_no_conflicting_checkpoint_be_justified cfg ext
          query.store (get_current_balance_source query) = true := by
        rcases hfacts.previous_result_outer_guard hnotCurrent with
          hstart' | hgate'
        · exact absurd hstart' hstart
        · exact hgate'
      exact .previousNoConflict hprevious hstart hgate
        (hprovisos.selected_previous_result_no_conflict result rfl
          (by simpa only [result] using hstrict) hnotCurrent hstart)

/-! ## The relay-free endpoint ancestry transport -/

/-- Observer twin of
`Execution.preQueryTarget_descends_queryBlock_at_endpoint`
(`SelectedPreQueryHistoricalSIR.lean:539`).

The strong proof routes the query-store ancestry `target.root ⩾c b` to the
endpoint through two receiver-side synchrony relays
(`preQueryHonestTarget_sourceWitnessAtQuery`'s
`E.blockRoots_subset_of_relay` and
`ancestry_of_known_honest_past_descendant_minimal`'s
`hA.synchrony.block_relay`), both of which deliver *into* the query node's
store and therefore have no weak-model counterpart at a Byzantine observer.

They are not needed. `Execution.is_ancestor_replay_closed`
(`WeakAncestryEndpoint.lean:43`) replays the very same `is_ancestor` fact into
any foreign store assuming no containment in either direction — only that the
descendant witness (here `target.root` itself) is known at both stores. That
is `hTQ` at the observer and the new explicit `hTM` at the endpoint, which at
both call sites inside
`selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning` is
`hA.domain.justified_root_known w hw m hHm` rewritten along the already-derived
`hroot : J.root = T.root`.

Consequently the whole vote witness (`hwalkDomain`, `hi`, `hs0`, `hsq`,
`hsH`, `hvote₀`, `htarget₀`), the endpoint honesty `hw`, the horizon bounds
and the slot ordering `hslotQM` all leave the signature: none of them is used
once the relays are gone. -/
theorem preQueryTarget_descends_queryBlock_at_endpoint
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ}
    {target : Checkpoint Root} {b : Root}
    (hTQ : target.root ∈ (E.store cfg ext obs q).block_roots)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hTbQ : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root target.root) (get_node_for_root b) = true)
    {w : ValidatorIndex} {m : ℕ}
    (hTM : target.root ∈ (E.store cfg ext w m).block_roots) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root target.root) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hanchorMin : ablk.message.slot ≤
      ((E.store cfg ext obs q).blocks b).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorParent obs q b hbQ
  exact E.is_ancestor_replay_closed cfg ext hA.wellFormed
    hA.externals_coherence hgenEq hanchorSlot hanchorParent hanchorMin
    hTQ hTM hbQ hTbQ

/-! ## Query-local current-epoch boundary walk -/

/-- Observer twin of
`Execution.currentEpochBoundaryWalk_of_knownEarlierEpochBlock`
(`SelectedPreQueryHistoricalSIR.lean:979`). Its single honesty use is
`head_root_known_of_selectedMarginDomain … hv q hqH`, replaced by
`Execution.head_root_known_at_observer`; everything else (the anchor
knownness, `known_descends_trustedAnchor`, and `store_walkKnownK`) is already
proved at an arbitrary node. -/
theorem currentEpochBoundaryWalk_of_knownEarlierEpochBlock
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    {b : Root} (hb : b ∈ query.store.block_roots)
    (hbEarlier : get_block_epoch cfg query.store b <
      get_current_store_epoch cfg query.store) :
    WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hanchor0 : ablk.root ∈ (E.store cfg ext obs 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgenEq]
    simp [get_forkchoice_store]
  have hanchorE : ablk.root ∈ (E.store cfg ext obs q).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le q)).1 hanchor0
  have hanchorQ : ablk.root ∈ query.store.block_roots := by
    simpa only [hquery] using hanchorE
  have hanchorRecord : query.store.blocks ablk.root = ablk.message := by
    simpa only [hquery] using
      E.store_anchor_block cfg ext hA.wellFormed hgenEq obs q hanchorE
  have hanchorEpoch : get_block_epoch cfg query.store ablk.root =
      get_current_epoch cfg ast := by
    simp only [get_block_epoch, get_current_epoch, hanchorRecord, hanchorSlot]
  have hanchorBelow := E.known_descends_trustedAnchor cfg ext hA
    (anchor := E.genesis_store.justified_checkpoint) rfl obs q
      (by simpa only [hquery] using hb)
  have hanchorCheckpointEpoch :
      E.genesis_store.justified_checkpoint.epoch =
        get_current_epoch cfg ast := by
    rw [hgenEq]
    rfl
  have hbEarlierE : get_block_epoch cfg (E.store cfg ext obs q) b <
      get_current_store_epoch cfg (E.store cfg ext obs q) := by
    simpa only [← hquery] using hbEarlier
  have hanchorEpochLt : get_block_epoch cfg query.store ablk.root <
      get_current_store_epoch cfg query.store := by
    rw [hanchorEpoch, ← hanchorCheckpointEpoch]
    simpa only [← hquery] using hanchorBelow.2.trans_lt hbEarlierE
  have hanchorSlotLt : (query.store.blocks ablk.root).slot <
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) := by
    simp only [get_block_epoch, compute_epoch_at_slot,
      compute_start_slot_at_epoch] at hanchorEpochLt ⊢
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp hanchorEpochLt
  have hheadE : (get_head cfg (E.store cfg ext obs q)).root ∈
      (E.store cfg ext obs q).block_roots :=
    E.head_root_known_at_observer cfg ext hcoh q hqH
  have hwalkAnchorE := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen obs q ablk.root hanchorE
      (get_head cfg (E.store cfg ext obs q)).root hheadE
  have hwalkAnchorQ : WalkKnown query.store
      (query.store.blocks ablk.root).slot (get_head cfg query.store).root := by
    simpa only [hquery] using hwalkAnchorE
  exact hwalkAnchorQ.mono (Nat.le_of_lt hanchorSlotLt)

/-! ## The crux: all three regions at a Byzantine observer -/

/-- Observer twin of
`Execution.selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning`
(`SelectedPreQueryHistoricalSIR.lean:1057`), the crux of stage S8.

Substitutions relative to the strong proof:

* the two query-node domain hubs become `Execution.observerStoreDomainK` /
  `Execution.head_root_known_at_observer`;
* `strictSelectedResultMechanicalFacts` becomes stage S2's
  `Weak.strictSelectedResultMechanicalFacts`;
* both `confirmed_ancestry_at_all_honest_endpoints_minimal` applications
  become `Execution.confirmed_ancestry_at_all_honest_endpoints_at_observer`,
  fed `hcoh.committees_agree q hqH`;
* the query head/result ancestry `hheadResultQ`, which the strong proof
  obtains from `findLatestSelectedResult_below_head` applied to
  `hheadInputQ := hbase v hv q hstartQ hqH` (an instantiation of the
  honest-quantified input safety at the query node), becomes
  `Weak.strictSelectedResult_below_head`, which assumes no input safety at
  all. `hheadInputQ` is then recovered by composing it with the mechanical
  facts' `descends_input` through `is_ancestor_trans`;
* `preQueryTarget_descends_queryBlock_at_endpoint` becomes this module's
  relay-free twin, whose new `hTM` premise is discharged at both call sites
  from `hA.domain.justified_root_known w hw m hHm` rewritten along the
  locally derived `hroot : J.root = T.root`. Because that twin needs no vote
  witness, the binders `hi`, `hs0`, `hvote₀` and `hwalkDomain` survive here
  only for `postAnchorHonestTargetGeometryAt_of_vote`, which is reused
  verbatim (its honesty is at the honest voter `i` and the honest endpoint).

`hbase` is deliberately **retained** — see the module docstring's "Deviation"
section: its second use, `preQueryVote_belowInput_of_safeInput`, instantiates
it at the honest endpoint `w`, which is legitimate in the weak model and
without which the below-input region is not provable. -/
theorem selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsq : s < E.slot_at cfg q)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    (htarget₀ : a₀.data.target =
      (E.store cfg ext w m).justified_checkpoint)
    (hstartOrPin :
      is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
        ((E.store cfg ext w m).justified_checkpoint.epoch =
            (get_current_target cfg query.store).epoch →
          (E.store cfg ext w m).justified_checkpoint.root =
            (get_current_target cfg query.store).root)) :
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m) input
      (Weak.find_latest_confirmed_descendant cfg ext query input)
      (E.store cfg ext w m).justified_checkpoint := by
  let result := Weak.find_latest_confirmed_descendant cfg ext query input
  let store := E.store cfg ext w m
  let J := store.justified_checkpoint
  let T := get_current_target cfg query.store
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.observerStoreDomainK cfg ext hA.wellFormed hA.externals_coherence
      hA.genesis hcoh q hqH
  have hheadQ : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    have hhead := E.head_root_known_at_observer cfg ext hcoh q hqH
    simpa only [hquery] using hhead
  have hwfQuery : ParentSlotLt query.store := by
    simpa only [hquery] using hwfQ
  have hwalkQuery : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [hquery] using hwalkQ
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hcoh.committees_agree q hqH
  have hfacts := Weak.strictSelectedResultMechanicalFacts cfg ext hA hcoh hqH
    query hquery input hinput hinputEpoch hstrict
  have hresultQ : result ∈ query.store.block_roots := by
    simpa only [result] using hfacts.result_known
  have hparentQ : (query.store.blocks result).parent_root ∈
      query.store.block_roots := by
    simpa only [result] using hfacts.parent_known
  have hresultInputQ : is_ancestor query.store
      (get_node_for_root result) (get_node_for_root input) = true := by
    simpa only [result] using hfacts.descends_input
  have hheadResultQ : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root result) = true := by
    simpa only [result] using
      Weak.strictSelectedResult_below_head cfg ext hwfQuery hwalkQuery
        hheadQ hinput hstrict
  have hheadInputQ : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root input) = true := by
    have htrans := is_ancestor_trans hwfQuery
      (hwalkQuery input hinput (get_head cfg query.store).root hheadQ)
      (hwalkQuery input hinput result hresultQ)
      hheadResultQ hresultInputQ
    simpa only [get_node_for_root] using htrans
  have hresultE : result ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hresultQ
  have hparentE : ((E.store cfg ext obs q).blocks result).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hparentQ
  have hinputE : input ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hinput
  have hresultInputE : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root result) (get_node_for_root input) = true := by
    simpa only [← hquery] using hresultInputQ
  obtain ⟨hinputM, hresultM, _hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hquery result input hqH hresultE hparentE hinputE
      hresultInputE (by simpa only [result] using hfacts.confirmed)
      w hw m hslotQM hHm
  have hgeom := E.postAnchorHonestTargetGeometryAt_of_vote cfg ext hA
    hwalkDomain hi hs0 hsH hvote₀ hw hHm htarget₀
  have htargetUpper : J.epoch ≤
      get_current_store_epoch cfg query.store := by
    simpa only [store, J] using
      E.postAnchorPreQueryTarget_epoch_le_query cfg ext query hquery hgeom hsq
  have hJM : J.root ∈ store.block_roots := by
    simpa only [store, J] using hA.domain.justified_root_known w hw m hHm
  have hinputAgree : query.store.blocks input = store.blocks input := by
    rw [hquery]
    exact hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs q) (E.blockProvenance cfg ext w m)
      hinputE (by simpa only [store] using hinputM)
  have hresultAgree : query.store.blocks result = store.blocks result := by
    rw [hquery]
    exact hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs q) (E.blockProvenance cfg ext w m)
      hresultE (by simpa only [store] using hresultM)
  constructor
  · intro hbelow
    simpa only [result, store, J] using
      E.preQueryVote_belowInput_of_safeInput cfg ext hA hbase hw hslotQM
        hHm hinputM hgeom hbelow
  · intro haboveInputM hbelowResultM
    have haboveInputQ : get_block_epoch cfg query.store input < J.epoch := by
      simpa only [get_block_epoch, hinputAgree] using haboveInputM
    have hbelowResultQ : J.epoch ≤
        get_block_epoch cfg query.store result := by
      simpa only [get_block_epoch, hresultAgree] using hbelowResultM
    have hforce := Execution.middleRegion_forces_current cfg hinputEpoch
      (by simpa only [result] using hfacts.current_or_previous_epoch)
      htargetUpper haboveInputQ hbelowResultQ
    have hresultCurrent : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store := hforce.1
    have hJEpoch : J.epoch = get_current_store_epoch cfg query.store :=
      hforce.2
    have hpin : store.justified_checkpoint.epoch = T.epoch →
        store.justified_checkpoint.root = T.root := by
      rcases hstartOrPin with hstart | hpin
      · have htargetLt := E.preQueryTarget_epoch_lt_query_of_epochStart
          cfg ext query hquery hgeom hsq hstart
        have hbad : J.epoch < J.epoch := by
          calc
            J.epoch < get_current_store_epoch cfg query.store := by
              simpa only [store, J] using htargetLt
            _ = J.epoch := hJEpoch.symm
        exact False.elim (Nat.lt_irrefl _ hbad)
      · simpa only [store, T] using hpin
    have hsameEpoch : J.epoch = T.epoch := by
      simpa only [T, get_current_target] using hJEpoch
    have hroot : J.root = T.root := by
      simpa only [store, J, T] using hpin (by
        simpa only [store, J, T] using hsameEpoch)
    have hinputPrevious : get_block_epoch cfg query.store input + 1 =
        get_current_store_epoch cfg query.store := by
      rcases hinputEpoch with hcurrent | hprevious
      · have hbad : get_current_store_epoch cfg query.store < J.epoch := by
          simpa only [hcurrent] using haboveInputQ
        exact False.elim ((Nat.not_lt_of_ge htargetUpper) hbad)
      · exact hprevious
    have hinputEarlier : get_block_epoch cfg query.store input <
        get_current_store_epoch cfg query.store := by
      rw [← hinputPrevious]
      exact Nat.lt_succ_self _
    have hboundaryWalk :=
      Weak.currentEpochBoundaryWalk_of_knownEarlierEpochBlock cfg ext hA
        hcoh hqH query hquery hinput hinputEarlier
    obtain ⟨hTQ, hresultTQ⟩ :=
      Execution.currentEpochBlock_descends_currentTarget cfg hwfQuery hwalkQuery
        hheadQ hresultQ hheadResultQ hboundaryWalk hresultCurrent
    obtain ⟨_hTQ', hTinputQ⟩ :=
      Execution.currentTarget_descends_previousEpochBlock cfg hwfQuery hwalkQuery
        hheadQ hinput hheadInputQ hboundaryWalk hinputPrevious
    have hTE : T.root ∈ (E.store cfg ext obs q).block_roots := by
      simpa only [← hquery] using hTQ
    have hresultTE : is_ancestor (E.store cfg ext obs q)
        (get_node_for_root result) (get_node_for_root T.root) = true := by
      simpa only [← hquery] using hresultTQ
    obtain ⟨_hTM', _hresultM', hresultTM⟩ :=
      E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
        obs q hcomm query hquery result T.root hqH hresultE hparentE hTE
        hresultTE (by simpa only [result] using hfacts.confirmed)
        w hw m hslotQM hHm
    have hTinputE : is_ancestor (E.store cfg ext obs q)
        (get_node_for_root T.root) (get_node_for_root input) = true := by
      simpa only [← hquery] using hTinputQ
    have hTM : T.root ∈ (E.store cfg ext w m).block_roots := by
      simpa only [store, hroot] using hJM
    have hTinputM := Weak.preQueryTarget_descends_queryBlock_at_endpoint
      cfg ext hA (target := T) hTE hinputE hTinputE hTM
    constructor
    · simpa only [result, store, J, T, hroot] using hresultTM
    · simpa only [store, J, T, hroot] using hTinputM
  · intro haboveResultM
    have haboveResultQ : get_block_epoch cfg query.store result < J.epoch := by
      simpa only [get_block_epoch, hresultAgree] using haboveResultM
    have hforce := Execution.aboveSelectedRegion_forces_previous cfg
      (by simpa only [result] using hfacts.current_or_previous_epoch)
      htargetUpper haboveResultQ
    have hresultPrevious : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store := hforce.1
    have hJEpoch : J.epoch = get_current_store_epoch cfg query.store :=
      hforce.2
    have hpin : store.justified_checkpoint.epoch = T.epoch →
        store.justified_checkpoint.root = T.root := by
      rcases hstartOrPin with hstart | hpin
      · have htargetLt := E.preQueryTarget_epoch_lt_query_of_epochStart
          cfg ext query hquery hgeom hsq hstart
        have hbad : J.epoch < J.epoch := by
          calc
            J.epoch < get_current_store_epoch cfg query.store := by
              simpa only [store, J] using htargetLt
            _ = J.epoch := hJEpoch.symm
        exact False.elim (Nat.lt_irrefl _ hbad)
      · simpa only [store, T] using hpin
    have hsameEpoch : J.epoch = T.epoch := by
      simpa only [T, get_current_target] using hJEpoch
    have hroot : J.root = T.root := by
      simpa only [store, J, T] using hpin (by
        simpa only [store, J, T] using hsameEpoch)
    have hresultEarlier : get_block_epoch cfg query.store result <
        get_current_store_epoch cfg query.store := by
      rw [← hresultPrevious]
      exact Nat.lt_succ_self _
    have hboundaryWalk :=
      Weak.currentEpochBoundaryWalk_of_knownEarlierEpochBlock cfg ext hA
        hcoh hqH query hquery hresultQ hresultEarlier
    obtain ⟨hTQ, hTresultQ⟩ :=
      Execution.currentTarget_descends_previousEpochBlock cfg hwfQuery hwalkQuery
        hheadQ hresultQ hheadResultQ hboundaryWalk hresultPrevious
    have hTE : T.root ∈ (E.store cfg ext obs q).block_roots := by
      simpa only [← hquery] using hTQ
    have hTresultE : is_ancestor (E.store cfg ext obs q)
        (get_node_for_root T.root) (get_node_for_root result) = true := by
      simpa only [← hquery] using hTresultQ
    have hTM : T.root ∈ (E.store cfg ext w m).block_roots := by
      simpa only [store, hroot] using hJM
    have hTresultM := Weak.preQueryTarget_descends_queryBlock_at_endpoint
      cfg ext hA (target := T) hTE hresultE hTresultE hTM
    simpa only [result, store, J, T, hroot] using hTresultM

/-! ## Discharging the old compatibility boundary -/

/-- Observer twin of
`Execution.preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket`
(`SelectedPreQuerySIR.lean:323`): the three-region bracket still suffices for
the existing pre-query compatibility interface at a Byzantine observer.

Substitutions: the two query-node domain hubs, the weak selector inversion for
the query-store result/input ancestry, and
`Execution.confirmed_ancestry_at_all_honest_endpoints_at_observer` for the
endpoint transport. The endpoint-side `store_domainK_of_selectedMarginDomain`
is unchanged — `(w, m)` is honest in both developments — and
`SelectedSIRThreeRegionBracket.compatible_of_selected_descends_input` is pure
tree geometry. -/
theorem preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hbracket : E.PreQuerySelectedSIRBracketAt cfg ext anchor q input
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m) :
    E.PreQuerySelectedJustifiedCompatibilityAt cfg ext anchor q
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m := by
  let result := Weak.find_latest_confirmed_descendant cfg ext query input
  obtain ⟨hwfQ, hwalkQ, hjustQ⟩ :=
    E.observerStoreDomainK cfg ext hA.wellFormed hA.externals_coherence
      hA.genesis hcoh q hqH
  have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
    have hhead := E.head_root_known_at_observer cfg ext hcoh q hqH
    simpa only [hquery] using hhead
  have hselected := E.find_latest_confirmed_descendant_selected_minimal_weak
    cfg ext hA obs q hqH hjustQ query hquery input hinput
  have hright :
      Spec.is_one_confirmed cfg ext query.store
          (get_current_balance_source query) result = true ∧
        result ∈ query.store.block_roots ∧
        (query.store.blocks result).parent_root ∈
          query.store.block_roots := by
    rcases hselected with heq | hright
    · exact False.elim (hstrict (by simpa only [result] using heq))
    · exact ⟨hright.1, hright.2.2.1, hright.2.2.2.1⟩
  have hresultKnownE : result ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hright.2.1
  have hparentKnownE : ((E.store cfg ext obs q).blocks result).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hright.2.2
  have hinputKnownE : input ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [← hquery] using hinput
  have hresultInputQ : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root result) (get_node_for_root input) = true := by
    have hge := weak_find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hquery] using hwfQ)
      (by simpa only [hquery] using hwalkQ)
      hheadQ input hinput
    simpa only [result, hquery] using hge.1
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hcoh.committees_agree q hqH
  obtain ⟨hinputM, hresultM, hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hquery result input hqH hresultKnownE hparentKnownE
      hinputKnownE hresultInputQ hright.1 w hw m hslotQM hHm
  obtain ⟨hwfM, hwalkM, hjustifiedM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  intro horigin
  have hregions : SelectedSIRThreeRegionBracket cfg
      (E.store cfg ext w m) input result
      (E.store cfg ext w m).justified_checkpoint := by
    simpa only [result] using hbracket horigin
  have hcomp := hregions.compatible_of_selected_descends_input cfg
    hwfM hwalkM hinputM hresultM hjustifiedM hresultInputM
  simpa only [result] using hcomp

end Weak

end FastConfirmation.Spec
