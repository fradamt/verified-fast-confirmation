import FastConfirmation.Spec.Proof.SelectedPreQuerySIR

/-!
# Trusted-anchor part of the pre-query SIR bracket

The certificate and SIR pipelines are parameterized by an abstract checkpoint
`anchor`.  `SelectedMarginAssumptions` identifies the execution's concrete
trusted initialization, but does not by itself identify that abstract
parameter.  The exact faithful bridge is therefore the equality

`anchor = E.genesis_store.justified_checkpoint`.

Under that equality, the executable store trajectory proves something
stronger than the anchor branch immediately needs: at every store, every known
block descends from the trusted anchor root, and its block epoch is at least
the anchor epoch.  Strict confirmation transports both the selector input and
result to every later honest endpoint, so the anchor-origin instance of the
three-region SIR bracket follows mechanically.  The non-anchor, pre-query-vote
origin remains a separate SIR obligation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Every known block in every execution store descends from the concrete
trusted anchor, and has block epoch at least the anchor checkpoint epoch.

The equality premise is intentionally exact.  An arbitrary certificate-layer
`anchor` is not pinned by `SelectedMarginAssumptions`; equating it with the
genesis store's justified checkpoint is the minimal bridge to the executable
`get_forkchoice_store` initialization. -/
theorem known_descends_trustedAnchor
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : ℕ) {r : Root}
    (hr : r ∈ (E.store cfg ext w m).block_roots) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root r) (get_node_for_root anchor.root) = true ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m) r := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hanchorRoot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgenEq]
    rfl
  have hanchorKnown0 : ablk.root ∈
      (E.store cfg ext w 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgenEq]
    simp [get_forkchoice_store]
  have hanchorKnown : ablk.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorKnown0
  have hwfM : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      hgen hA.wellFormed.anchor_parent_unscheduled w m
  have hnonAnchor := E.store_nonAnchorParentKnown cfg ext hgenEq w m
  have hminimum := E.store_anchor_min_slot cfg ext hA.wellFormed
    hA.externals_coherence hgenEq hanchorSlot hanchorParent w m
  have hanchorBlock :
      (E.store cfg ext w m).blocks ablk.root = ablk.message :=
    E.store_anchor_block cfg ext hA.wellFormed hgenEq w m hanchorKnown
  have hanchorBlockSlot :
      ((E.store cfg ext w m).blocks ablk.root).slot = ablk.message.slot := by
    rw [hanchorBlock]
  have hwalk : WalkKnown (E.store cfg ext w m) ablk.message.slot r := by
    have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
      hA.externals_coherence hgen w m ablk.root hanchorKnown r hr
    rwa [hanchorBlockSlot] at hwalkK
  have hlands_of_walk : ∀ {x : Root},
      WalkKnown (E.store cfg ext w m) ablk.message.slot x →
        get_ancestor (E.store cfg ext w m)
          (ForkChoiceNode.mk x) ablk.message.slot =
            ForkChoiceNode.mk ablk.root := by
    intro x hx
    induction hx with
    | @stop x hr' hle =>
        have hre : x = ablk.root := by
          rcases hnonAnchor x hr' with hre | hparentKnown
          · exact hre
          · have hparentLt := hwfM x hr' hparentKnown
            have hparentGe := hminimum _ hparentKnown
            exact False.elim
              ((Nat.not_lt_of_ge hparentGe) (hparentLt.trans_le hle))
        subst x
        exact get_ancestor_stop hle
    | @step x hr' hgt hp ih =>
        rw [get_ancestor_step hwfM hr' hgt hp]
        exact ih
  have hlands : get_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk r) ablk.message.slot =
        ForkChoiceNode.mk ablk.root := hlands_of_walk hwalk
  have hdescends : is_ancestor (E.store cfg ext w m)
      (get_node_for_root r) (get_node_for_root ablk.root) = true := by
    simp only [is_ancestor, get_node_for_root, decide_eq_true_eq,
      hanchorBlockSlot]
    exact hlands
  have hanchorBlockEpoch : get_current_epoch cfg ast =
      get_block_epoch cfg (E.store cfg ext w m) ablk.root := by
    simp only [get_current_epoch, get_block_epoch, hanchorBlockSlot,
      hanchorSlot]
  refine ⟨?_, ?_⟩
  · simpa only [hanchorRoot] using hdescends
  · rw [hanchorEpoch, hanchorBlockEpoch]
    exact ce_mono cfg (by
      simpa only [hanchorBlockSlot] using hminimum r hr)

/-- Endpoint-local anchor case of the three-region SIR bracket.  Knownness of
the input and selected result is the only selector-specific data needed here;
the impossible middle/upper regions are ruled out by the trusted anchor's
minimal epoch. -/
theorem selectedSIRThreeRegionBracket_of_trustedAnchor_known
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {input selected : Root} {w : ValidatorIndex} {m : ℕ}
    (hinput : input ∈ (E.store cfg ext w m).block_roots)
    (hselected : selected ∈ (E.store cfg ext w m).block_roots)
    (hjustifiedAnchor :
      (E.store cfg ext w m).justified_checkpoint = anchor) :
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m)
      input selected (E.store cfg ext w m).justified_checkpoint := by
  have hinputAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hinput
  have hselectedAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hselected
  constructor
  · intro _hbelow
    simpa only [hjustifiedAnchor] using hinputAnchor.1
  · intro haboveInput _hbelowSelected
    have haboveInput' : get_block_epoch cfg (E.store cfg ext w m) input <
        anchor.epoch := by
      simpa only [hjustifiedAnchor] using haboveInput
    exact False.elim ((Nat.not_lt_of_ge hinputAnchor.2) haboveInput')
  · intro haboveSelected
    have haboveSelected' : get_block_epoch cfg (E.store cfg ext w m) selected <
        anchor.epoch := by
      simpa only [hjustifiedAnchor] using haboveSelected
    exact False.elim ((Nat.not_lt_of_ge hselectedAnchor.2) haboveSelected')

/-- A strict selected call puts both the selector input and its strict result
above the trusted anchor at every later honest endpoint.  This is the strongest
anchor-specific fact consumed by the SIR bracket: it also returns endpoint
knownness and the corresponding epoch lower bounds.

No input-epoch/SIR assumption is used.  Endpoint transport comes from the
strict confirmation's actual honest past-supporter witness. -/
theorem trustedAnchor_below_strictSelected_at_endpoint
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    input ∈ (E.store cfg ext w m).block_roots ∧
      find_latest_confirmed_descendant cfg ext query input ∈
        (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root input) (get_node_for_root anchor.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query input))
        (get_node_for_root anchor.root) = true ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m) input ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m)
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
  have hresultKnownE : result ∈
      (E.store cfg ext v q).block_roots := by
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
  obtain ⟨hinputM, hresultM, _hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery result input hqH hresultKnownE hparentKnownE
      hinputKnownE hresultInputQ hright.1 w hw m hslotQM hHm
  have hinputAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hinputM
  have hresultAnchor := E.known_descends_trustedAnchor cfg ext hA
    hanchor w m hresultM
  simpa only [result] using
    ⟨hinputM, hresultM, hinputAnchor.1, hresultAnchor.1,
      hinputAnchor.2, hresultAnchor.2⟩

/-- The trusted-anchor disjunct of `PreQueryTargetOriginAt` supplies the full
three-region bracket for a strict selected result.  The sibling disjunct, an
honest target vote cast before the query, is deliberately not hidden here. -/
theorem selectedSIRThreeRegionBracket_of_trustedAnchor_strict
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hjustifiedAnchor :
      (E.store cfg ext w m).justified_checkpoint = anchor) :
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m) input
      (find_latest_confirmed_descendant cfg ext query input)
      (E.store cfg ext w m).justified_checkpoint := by
  obtain ⟨hinputM, hresultM, _hinputAnchor, _hresultAnchor,
      _hinputEpoch, _hresultEpoch⟩ :=
    E.trustedAnchor_below_strictSelected_at_endpoint cfg ext hA hanchor
      hv hqH query hquery input hinput hstrict hw hslotQM hHm
  exact E.selectedSIRThreeRegionBracket_of_trustedAnchor_known cfg ext hA
    hanchor hinputM hresultM hjustifiedAnchor

/-- The exact remainder after discharging the trusted-anchor disjunct of
`PreQueryTargetOriginAt`: a non-anchor endpoint justification exposes an honest
target vote strictly before the selected query, and that causal checkpoint
must satisfy the three SIR regions.

Keeping the causal witness in this interface prevents the remainder from
silently expanding back into arbitrary endpoint-checkpoint compatibility. -/
def PreQueryVoteSelectedSIRBracketAt
    (q : ℕ) (input selected : Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  ∀ i ∈ E.honest, ∀ (s : Slot) (k : ℕ) (a : Attestation Root),
    E.slot_at cfg 0 ≤ s →
    s < E.slot_at cfg q →
    s < E.slot_at cfg m →
    E.SlotWithinHorizon cfg s →
    E.vote i s = some (k, a) →
    a.data.target = (E.store cfg ext w m).justified_checkpoint →
      SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m)
        input selected (E.store cfg ext w m).justified_checkpoint

/-- Assemble the complete `PreQuerySelectedSIRBracketAt` from the now-proved
trusted-anchor branch and the exact remaining pre-query honest-vote branch. -/
theorem preQuerySelectedSIRBracketAt_of_voteBracket_strict
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvoteBracket : E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
      (find_latest_confirmed_descendant cfg ext query input) w m) :
    E.PreQuerySelectedSIRBracketAt cfg ext anchor q input
      (find_latest_confirmed_descendant cfg ext query input) w m := by
  intro horigin
  rcases horigin with hjustifiedAnchor | hvote
  · exact E.selectedSIRThreeRegionBracket_of_trustedAnchor_strict cfg ext
      hA hanchor hv hqH query hquery input hinput hstrict hw hslotQM hHm
      hjustifiedAnchor
  · obtain ⟨i, hi, s, k, a, hs0, hsq, hsm, hsH, hvote, htarget⟩ := hvote
    exact hvoteBracket i hi s k a hs0 hsq hsm hsH hvote htarget

end Execution

end FastConfirmation.Spec
