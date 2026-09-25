module
public import FastConfirmationProofs.FCRRule.SelectedInitialRecency
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedCompatibility
public import FastConfirmationInternal.FCRRule.SelectedTraceEdges

@[expose] public section

/-!
# Mechanical pre-query SIR bracket

`PreQuerySelectedJustifiedCompatibilityAt` is intentionally a narrow semantic
boundary, but its conclusion does not show which part of the selected chain an
older justification must occupy.  This module factors that boundary into the
three epoch regions used by the paper's SIR argument:

* at or below the selector input's block epoch;
* strictly above the input and at or below the selected result's block epoch;
* strictly above the selected result's block epoch.

The first and middle regions put the justified root below the selected result;
the last puts it above the selected result.  The theorem below derives the
ordinary compatibility proposition from those three clauses.  In particular,
the selected-result/input ancestry at every slot-ordered endpoint is not a
field of the bracket: it is reconstructed from the strict executable
confirmation and the existing same-slot provenance transport.

The three region clauses are still semantic SIR obligations.  This file does
not turn an opaque FFG state or a helper prediction into any one of them.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The three-region semantic boundary -/

/-- The exact three-region SIR bracket at one endpoint store.

The interval predicates use the checkpoint's *declared checkpoint epoch* and
the input/result block epochs.  The ancestry conclusions spell out the chain
position required in each interval.  The middle clause includes both sides of
the bracket even though only `selected ⩾c justified` is needed by the immediate
compatibility consumer. -/
structure SelectedSIRThreeRegionBracket (store : Store Root)
    (input selected : Root) (justified : Checkpoint Root) : Prop where
  below_input :
    justified.epoch ≤ get_block_epoch cfg store input →
      is_ancestor store
        (get_node_for_root input)
        (get_node_for_root justified.root) = true
  inside_selected_segment :
    get_block_epoch cfg store input < justified.epoch →
    justified.epoch ≤ get_block_epoch cfg store selected →
      is_ancestor store
          (get_node_for_root selected)
          (get_node_for_root justified.root) = true ∧
        is_ancestor store
          (get_node_for_root justified.root)
          (get_node_for_root input) = true
  above_selected :
    get_block_epoch cfg store selected < justified.epoch →
      is_ancestor store
        (get_node_for_root justified.root)
        (get_node_for_root selected) = true

namespace SelectedSIRThreeRegionBracket

/-- Pure tree geometry: once the selected result is known to descend from the
input, the three epoch regions imply selected/justified comparability.

Only the below-input branch needs transitivity through the input.  The other
two branches expose the required orientation directly. -/
theorem compatible_of_selected_descends_input
    {store : Store Root} {input selected : Root}
    {justified : Checkpoint Root}
    (hbracket : SelectedSIRThreeRegionBracket cfg store input selected justified)
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hinput : input ∈ store.block_roots)
    (hselected : selected ∈ store.block_roots)
    (hjustified : justified.root ∈ store.block_roots)
    (hselectedInput : is_ancestor store
      (get_node_for_root selected) (get_node_for_root input) = true) :
    is_ancestor store
        (get_node_for_root selected)
        (get_node_for_root justified.root) = true ∨
      is_ancestor store
        (get_node_for_root justified.root)
        (get_node_for_root selected) = true := by
  by_cases hbelow : justified.epoch ≤ get_block_epoch cfg store input
  · left
    exact is_ancestor_trans (a := get_node_for_root selected) (b := get_node_for_root input)
        (c := get_node_for_root justified.root) hwf
      (hwalk justified.root hjustified selected hselected)
      (hwalk justified.root hjustified input hinput)
      hselectedInput (hbracket.below_input hbelow)
  · have haboveInput : get_block_epoch cfg store input < justified.epoch :=
      Nat.lt_of_not_ge hbelow
    by_cases hinside : justified.epoch ≤ get_block_epoch cfg store selected
    · left
      exact (hbracket.inside_selected_segment haboveInput hinside).1
    · right
      exact hbracket.above_selected (Nat.lt_of_not_ge hinside)

end SelectedSIRThreeRegionBracket

namespace Execution

variable (E : Execution Root)

/-- The three-region bracket restricted to the origins which really predate
the selected query (or are the trusted anchor).  Unlike
`PreQuerySelectedJustifiedCompatibilityAt`, this exposes the exact epoch
region producer obligations instead of directly postulating comparability. -/
def PreQuerySelectedSIRBracketAt
    (anchor : Checkpoint Root) (q : ℕ)
    (input selected : Root) (w : ValidatorIndex) (m : ℕ) : Prop :=
  E.PreQueryTargetOriginAt cfg ext anchor q w m →
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m)
      input selected (E.store cfg ext w m).justified_checkpoint

/-! ## Exact executable facts for a strict selector result -/

/-- Query-local facts which are mechanically available for a strict result.

`current_or_previous_epoch` uses the selector's normative input-domain
premise.  `trace_origin` retains the actual producing trace: a previous-loop
result carries the full previous-entry guard and a tentative-loop result
carries both its entry guard and the final result acceptance guard. -/
structure StrictSelectedResultMechanicalFacts
    (query : FastConfirmationStore Root) (input result : Root) : Prop where
  confirmed : is_one_confirmed cfg ext query.store
    (get_current_balance_source query) result = true
  result_known : result ∈ query.store.block_roots
  parent_known : (query.store.blocks result).parent_root ∈
    query.store.block_roots
  descends_input : is_ancestor query.store
    (get_node_for_root result) (get_node_for_root input) = true
  current_or_previous_epoch :
    get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store
  trace_origin :
    (∃ a,
      PreviousEpochSelectedEdge cfg ext query input a result ∧
        PreviousSelectedEntryWitness cfg ext query input ∧
        ((get_voting_source cfg query.store
            query.previous_slot_head).epoch + 2 ≥
            get_current_store_epoch cfg query.store ∧
          is_ancestor query.store
            (get_node_for_root query.previous_slot_head)
            (get_node_for_root result) = true)) ∨
      (∃ a,
        (a, result) ∈
            (findLatestSelectedTrace cfg ext query input).2.2 ∧
          TentativeSelectedEntryWitness cfg query ∧
          TentativeSelectedResultWitness cfg ext query result)
  previous_result_outer_guard :
    get_block_epoch cfg query.store result ≠
        get_current_store_epoch cfg query.store →
      is_start_slot_at_epoch cfg
          (get_current_slot cfg query.store) = true ∨
        will_no_conflicting_checkpoint_be_justified cfg ext
          query.store = true

/-- A strict executable result supplies all of
`StrictSelectedResultMechanicalFacts` without an FFG/SIR premise.

The only extra epoch hypothesis is the pinned selector precondition saying
that its carried input is from the current or previous block epoch. -/
theorem strictSelectedResultMechanicalFacts
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input) :
    StrictSelectedResultMechanicalFacts cfg ext query input
      (find_latest_confirmed_descendant cfg ext query input) := by
  let result := find_latest_confirmed_descendant cfg ext query input
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
    have hhead := E.head_root_known_of_selectedMarginDomain cfg ext
      hA.domain hv q hqH
    simpa only [hquery] using hhead
  have hselected := E.find_latest_confirmed_descendant_selected_minimal
    cfg ext hA v hv q hqH query hquery input hinput
  have hright :
      is_one_confirmed cfg ext query.store
          (get_current_balance_source query) result = true ∧
        result ∈ query.store.block_roots ∧
        (query.store.blocks result).parent_root ∈
          query.store.block_roots := by
    rcases hselected with heq | hright
    · exact False.elim (hstrict (by simpa only [result] using heq))
    · simpa only [result] using hright
  have hge := find_latest_confirmed_descendant_ge cfg ext query
    (by simpa only [hquery] using hwfQ)
    (by simpa only [hquery] using hwalkQ)
    hheadQ input hinput
  have hdesc : is_ancestor query.store
      (get_node_for_root result) (get_node_for_root input) = true := by
    simpa only [result] using hge.1
  have hresultKnown : result ∈ query.store.block_roots := hright.2.1
  have hwfQuery : ParentSlotLt query.store := by
    simpa only [hquery] using hwfQ
  have hwalkQuery : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [hquery] using hwalkQ
  have hslotLower : (query.store.blocks input).slot ≤
      (query.store.blocks result).slot := by
    exact ancestor_slot_le hwfQuery
      (hwalkQuery input hinput result hresultKnown) hdesc
  have hepochLower : get_block_epoch cfg query.store input ≤
      get_block_epoch cfg query.store result := by
    exact ce_mono cfg hslotLower
  have hresultKnownE : result ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hresultKnown
  have hslotUpperE := E.store_blocks_slot_le_current cfg ext
    hA.whole_seconds
    (by
      obtain ⟨ast, ablk, hgeq, hslot, _⟩ := hA.genesis
      exact ⟨ast, ablk, hgeq, hslot⟩)
    v q result hresultKnownE
  have hslotUpper : (query.store.blocks result).slot ≤
      get_current_slot cfg query.store := by
    simpa only [hquery] using hslotUpperE
  have hepochUpper : get_block_epoch cfg query.store result ≤
      get_current_store_epoch cfg query.store := by
    exact ce_mono cfg hslotUpper
  have hepoch :
      get_block_epoch cfg query.store result =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store result + 1 =
          get_current_store_epoch cfg query.store := by
    let inputEpoch := get_block_epoch cfg query.store input
    let resultEpoch := get_block_epoch cfg query.store result
    let currentEpoch := get_current_store_epoch cfg query.store
    have hinputEpoch' : inputEpoch = currentEpoch ∨
        inputEpoch + 1 = currentEpoch := by
      simpa only [inputEpoch, resultEpoch, currentEpoch] using hinputEpoch
    have hepochLower' : inputEpoch ≤ resultEpoch := by
      simpa only [inputEpoch, resultEpoch, currentEpoch] using hepochLower
    have hepochUpper' : resultEpoch ≤ currentEpoch := by
      simpa only [inputEpoch, resultEpoch, currentEpoch] using hepochUpper
    change resultEpoch = currentEpoch ∨ resultEpoch + 1 = currentEpoch
    rcases hinputEpoch' with hcurrent | hprevious
    · left
      apply Nat.le_antisymm hepochUpper'
      exact hcurrent ▸ hepochLower'
    · rcases le_or_gt resultEpoch inputEpoch with hresultLe | hinputLt
      · right
        have heq : resultEpoch = inputEpoch :=
          Nat.le_antisymm hresultLe hepochLower'
        simpa only [heq] using hprevious
      · left
        apply Nat.le_antisymm hepochUpper'
        calc
          currentEpoch = inputEpoch + 1 := hprevious.symm
          _ ≤ resultEpoch := Nat.succ_le_of_lt hinputLt
  have horiginRaw := selected_strict_result_origin_recency_classification
    cfg ext query
    (by simpa only [hquery] using hwfQ)
    (by simpa only [hquery] using hwalkQ)
    hheadQ input hinput result rfl (by simpa only [result] using hstrict)
  have horigin :
      (∃ a,
        PreviousEpochSelectedEdge cfg ext query input a result ∧
          PreviousSelectedEntryWitness cfg ext query input ∧
          ((get_voting_source cfg query.store
              query.previous_slot_head).epoch + 2 ≥
              get_current_store_epoch cfg query.store ∧
            is_ancestor query.store
              (get_node_for_root query.previous_slot_head)
              (get_node_for_root result) = true)) ∨
        (∃ a,
          (a, result) ∈
              (findLatestSelectedTrace cfg ext query input).2.2 ∧
            TentativeSelectedEntryWitness cfg query ∧
            TentativeSelectedResultWitness cfg ext query result) := by
    rcases horiginRaw with hprevious | htentative
    · left
      obtain ⟨a, hedge, hrecency⟩ := hprevious
      exact ⟨a, hedge, hedge.entry_witness cfg ext, hrecency⟩
    · exact Or.inr htentative
  have houter : get_block_epoch cfg query.store result ≠
        get_current_store_epoch cfg query.store →
      is_start_slot_at_epoch cfg
          (get_current_slot cfg query.store) = true ∨
        will_no_conflicting_checkpoint_be_justified cfg ext
          query.store = true := by
    intro hprevious
    exact selected_previous_result_outer_gate cfg ext query input result
      rfl (by simpa only [result] using hstrict) hprevious
  exact {
    confirmed := hright.1
    result_known := hresultKnown
    parent_known := hright.2.2
    descends_input := hdesc
    current_or_previous_epoch := hepoch
    trace_origin := horigin
    previous_result_outer_guard := houter
  }

/-! ## Discharging the old compatibility boundary -/

/-- The three-region SIR bracket is sufficient for the existing pre-query
compatibility interface.

The selected result and input are transported together to the endpoint by the
strict confirmation's honest past-supporter witness.  Thus the bracket does
not assume selected/input ancestry, endpoint knownness, or any cross-store
agreement fact.  Those are all consequences of the executable query and the
lower selected-margin assumptions. -/
theorem preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hbracket : E.PreQuerySelectedSIRBracketAt cfg ext anchor q input
      (find_latest_confirmed_descendant cfg ext query input) w m) :
    E.PreQuerySelectedJustifiedCompatibilityAt cfg ext anchor q
      (find_latest_confirmed_descendant cfg ext query input) w m := by
  let result := find_latest_confirmed_descendant cfg ext query input
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
    have hhead := E.head_root_known_of_selectedMarginDomain cfg ext
      hA.domain hv q hqH
    simpa only [hquery] using hhead
  have hselected := E.find_latest_confirmed_descendant_selected_minimal
    cfg ext hA v hv q hqH query hquery input hinput
  have hright :
      is_one_confirmed cfg ext query.store
          (get_current_balance_source query) result = true ∧
        result ∈ query.store.block_roots ∧
        (query.store.blocks result).parent_root ∈
          query.store.block_roots := by
    rcases hselected with heq | hright
    · exact False.elim (hstrict (by simpa only [result] using heq))
    · simpa only [result] using hright
  have hresultKnownE : result ∈ (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hright.2.1
  have hparentKnownE : ((E.store cfg ext v q).blocks result).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hright.2.2
  have hinputKnownE : input ∈ (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hinput
  have hresultInputQ : is_ancestor (E.store cfg ext v q)
      (get_node_for_root result) (get_node_for_root input) = true := by
    have hge := find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hquery] using hwfQ)
      (by simpa only [hquery] using hwalkQ)
      hheadQ input hinput
    simpa only [result, hquery] using hge.1
  obtain ⟨hinputM, hresultM, hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery result input hqH hresultKnownE hparentKnownE
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

end Execution

end FastConfirmation.Spec

end
