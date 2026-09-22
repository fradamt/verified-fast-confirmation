module
public import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline
public import FastConfirmation.Spec.Proof.SelectedJustifiedCompatibility
public import FastConfirmation.Spec.Proof.SelectedPreQueryAnchor
public import FastConfirmation.Spec.Proof.CausalCheckpointEpochBound
public import FastConfirmation.Spec.Proof.SelectedFFGRealization
public import FastConfirmation.Spec.Proof.PaperA32Projection

@[expose] public section

/-!
# Non-circular selected-trace FFG realization

This module replaces the legacy `SelectedTraceFFGPipeline` boundary with the
causal/state-facing pieces actually used by the coupled proof.  The contract is
indexed by the exact selected call.  It does not contain filter membership,
`TipSourceFresh`, a leaf, a common-descendant placement, or a future head/safety
conclusion.

The remaining semantic fields have deliberately different roles:

* endpoint certificate, selector, finalized-boundary, and source-persistence
  realization describe concrete values read from honest endpoint stores;
* pre-query result/checkpoint comparability is the initial SIR / helper-gate
  soundness boundary;
* every non-anchor endpoint justification exposes a causal honest target vote;
  votes at or after the query are discharged by the actual head induction; and
* source availability exposes the paper's early-recency / later-inclusion
  alternative at a **seed** below an already-compatible selected result.
  Finite leaf selection, availability propagation, filter placement, and
  filtered membership are then proved mechanically.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The exact earlier-slot canonicality window available at one endpoint of
the coupled selected-result induction. -/
def SelectedCanonicalBeforeEndpointAt (q : ℕ) (glc : Root) (m : ℕ) : Prop :=
  ∀ w' ∈ E.honest, ∀ m' : ℕ,
    E.slot_start cfg (E.slot_at cfg q) ≤ m' →
    E.slot_at cfg m' < E.slot_at cfg m →
    E.WithinHorizon cfg m' →
    is_ancestor (E.store cfg ext w' m')
      (get_head cfg (E.store cfg ext w' m'))
      (get_node_for_root glc) = true

/-- An already-available query carrier for the selected checkpoint.  Keeping
the carrier explicit avoids the invalid backward inference from AU at a later
head to AU at `selected`.  The carrier is relayed to later endpoints before
its AU fact is projected into the executable unrealized map. -/
def SelectedEarlyA32CarrierAt
    (anchor : Checkpoint Root) (state : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ) (selected : Root)
    (baseEpoch : Epoch) : Prop :=
  ∃ carrier : Root,
    carrier ∈ (E.store cfg ext v q).block_roots ∧
    E.RootDescends carrier selected ∧
    get_block_epoch cfg (E.store cfg ext v q) carrier < baseEpoch + 2 ∧
    state.AU cfg carrier (state.C selected baseEpoch)

/-- Exact semantic split for the late selected-carrier argument.

If the target is already AU on a concrete query carrier above `selected`, it
is propagated directly and paper A3.2 is not invoked.  Otherwise the paper's
full canonicality and fixed-source support antecedents are supplied together.
The executable `A32IncludedAtTip` projection is not a field in either branch. -/
def SelectedA32SemanticRealizationAt
    (anchor : Checkpoint Root) (state : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ) (selected : Root)
    (baseEpoch : Epoch) : Prop :=
  E.SelectedEarlyA32CarrierAt cfg ext anchor state v q selected baseEpoch ∨
    (E.CanonicalThroughoutEpoch cfg ext selected (baseEpoch + 1) ∧
      PaperA32SupportThroughoutEpoch cfg ext state selected baseEpoch)

/-- The selected-margin bundle already contains every premise used by
concrete Casper accountability; the FFG realization must not ask for a
duplicate economic assumption. -/
def SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    (hA : SelectedMarginAssumptions cfg ext E) :
    FFGAccountabilityAssumptions cfg ext E where
  genesis_store := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hA.genesis
    exact ⟨ast, ablk, hgen⟩
  whole_seconds := hA.whole_seconds
  honest_behavior := hA.honest_behavior
  externals_coherence := hA.externals_coherence
  static_validator_set := hA.static_validators
  byzantine_bound := hA.byzantine_bound

/-- State/certificate realization for one exact strict selected call.

`pre_query_compatibility` and `selected_source_seed` are conditional on the
normative helper provisos attached to this call.  Neither conclusion names a
filter or asserts canonicality.  `selected_source_seed` is additionally
conditional on the selected result already descending from the endpoint
justified checkpoint; that compatibility is derived by the coupled induction,
not supplied by this field. -/
structure SelectedTraceFFGStateRealizationFor
    (anchor : Checkpoint Root)
    (ffg_state : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  query_store_eq : query.store = E.store cfg ext v q
  /-- The certificate-layer anchor is the execution's actual trusted
  initialization, rather than an unrelated abstract checkpoint. -/
  trusted_anchor : anchor = E.genesis_store.justified_checkpoint
  /-- One common block-local FFG interpretation for the entire selected call.
  Endpoint certificates, selector facts, and every A3.2 use must be realized
  against this state rather than choosing a fresh existential state per use. -/
  transition_coherence : FFGTransitionCoherence cfg ext ffg_state
  paper_a32 : PaperA32Inclusion cfg ext ffg_state
  endpoint : ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    EndpointFFGPipeline cfg E anchor (E.store cfg ext w m)
  selector : ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    EndpointSelectorRealization cfg E anchor (E.store cfg ext w m)
  finalized_boundary : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
      FinalizedBoundaryRealization cfg (E.store cfg ext w m)
  source_epoch_persistence : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
      VotingSourceEpochChainPersistence cfg (E.store cfg ext w m)
  /-- Exact historical remainder of the selected-input SIR argument.  The
  trusted-anchor origin is a theorem of the executable store trajectory; only
  a non-anchor justification caused by an honest vote before the query remains
  here. -/
  pre_query_vote_sir_bracket :
    SelectedHelperProvisosAt cfg ext E v q query latestConfirmedRoot →
    latestConfirmedRoot ∈ query.store.block_roots →
    find_latest_confirmed_descendant cfg ext query latestConfirmedRoot ≠
      latestConfirmedRoot →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      E.PreQueryVoteSelectedSIRBracketAt cfg ext q latestConfirmedRoot
        (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) w m
  endpoint_origin : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.slot_at cfg q ≤ E.slot_at cfg m →
    E.WithinHorizon cfg m →
      E.EndpointJustificationOriginAt cfg ext anchor w m
  initial_source_recency :
    SelectedHelperProvisosAt cfg ext E v q query latestConfirmedRoot →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      get_current_store_epoch cfg (E.store cfg ext w m) <
        get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) + 2 →
      ∃ seed : Root,
        seed ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root seed)
          (get_node_for_root
            (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)) = true ∧
        (get_voting_source cfg (E.store cfg ext w m) seed).epoch + 2 ≥
          get_current_store_epoch cfg (E.store cfg ext w m)
  a32_semantics :
    SelectedHelperProvisosAt cfg ext E v q query latestConfirmedRoot →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext q
        (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) m →
      E.SelectedA32SemanticRealizationAt cfg ext anchor ffg_state
        v q
        (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)
        (get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot))
  /-- The remaining late-epoch bound is needed only for a justification whose
  causal origin predates the selected query (including the trusted anchor).
  Post-query origins are a theorem of honest-vote checkpoint geometry and the
  earlier-slot head IH; see `query_justified_epoch_le_of_causal_honest_target_minimal`. -/
  pre_query_later_justified_epoch_bound :
    SelectedHelperProvisosAt cfg ext E v q query latestConfirmedRoot →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext q
        (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot) m →
      E.SelectedA32SemanticRealizationAt cfg ext anchor ffg_state
        v q
        (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)
        (get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)) →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot))
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)) ≠ true →
      E.PreQueryTargetOriginAt cfg ext anchor q w m →
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query latestConfirmedRoot)

/-- One existential chooses the semantic state once for the whole selected
call.  The inner record is indexed by that state, so endpoint/A3.2 consumers
cannot silently choose unrelated witnesses at different calls. -/
def SelectedTraceFFGStateRealizationAt
    (anchor : Checkpoint Root)
    (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop :=
  ∃ ffg_state : ChainFFGState cfg E anchor,
    E.SelectedTraceFFGStateRealizationFor cfg ext anchor ffg_state
      v q query latestConfirmedRoot

/-- The decomposed state realization produces a concrete filter certificate
for a strict selected edge.  Branch compatibility uses the actual earlier-
slot induction hypothesis.  The visible leaf, its placement, source freshness,
and filter skeleton are all derived after that step. -/
theorem filterTipCertificate_of_selectedTraceFFGStateRealization_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {r₀ glc c : Root}
    (hresult : find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hr₀ : r₀ ∈ query.store.block_roots)
    (hr₀Epoch :
      get_block_epoch cfg query.store r₀ =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store r₀ + 1 =
          get_current_store_epoch cfg query.store)
    (hstrict : glc ≠ r₀)
    (hrealization : E.SelectedTraceFFGStateRealizationAt cfg ext anchor
      v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    Nonempty (FilterTipCertificate cfg (E.store cfg ext w m) c) := by
  obtain ⟨ffg_state, hrealization⟩ := hrealization
  have hstrict' : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ := by
    simpa only [hresult] using hstrict
  have hmechanical := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
    query hrealization.query_store_eq r₀ hr₀ hr₀Epoch hstrict'
  have hvoteBracket : E.PreQueryVoteSelectedSIRBracketAt cfg ext q r₀
      (find_latest_confirmed_descendant cfg ext query r₀) w m :=
    hrealization.pre_query_vote_sir_bracket hprovisos hr₀ hstrict'
      w hw m hslotQM hHm
  have hbracket : E.PreQuerySelectedSIRBracketAt cfg ext anchor q r₀
      (find_latest_confirmed_descendant cfg ext query r₀) w m :=
    E.preQuerySelectedSIRBracketAt_of_voteBracket_strict cfg ext hA
      hrealization.trusted_anchor hv hqH query
      hrealization.query_store_eq r₀ hr₀ hstrict' hw hslotQM hHm
      hvoteBracket
  have hpre : E.PreQuerySelectedJustifiedCompatibilityAt cfg ext
      anchor q glc w m := by
    simpa only [hresult] using
      E.preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
        cfg ext hA hv hqH query hrealization.query_store_eq r₀ hr₀
        hstrict' hw hslotQM hHm hbracket
  have horigin : E.EndpointJustificationOriginAt cfg ext anchor w m :=
    hrealization.endpoint_origin w hw m hslotQM hHm
  obtain ⟨hcJ, hglcJ⟩ :=
    E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
      cfg ext hA hwalkDomain hw hHm hslotQM hcM hglcC_M
      hglcKnown hIH hpre horigin hnotCovered
  obtain ⟨hwfM, hwalkM, _hjustM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have hnotGlc : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root glc) ≠ true := by
    intro hJGlc
    apply hnotCovered
    exact is_ancestor_trans hwfM
      (hwalkM c hcM _
        (hrealization.endpoint w hw m hHm).justified_root_known)
      (hwalkM c hcM glc
        (hglcKnown w hw m
          (E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM) hHm))
      hJGlc hglcC_M
  have hglcQ : glc ∈ query.store.block_roots := by
    have hstartQ : E.slot_start cfg (E.slot_at cfg q) ≤ q :=
      E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (Nat.le_refl _)
    have hknown := hglcKnown v hv q hstartQ hqH
    simpa only [hrealization.query_store_eq] using hknown
  let eb := get_block_epoch cfg query.store glc
  have hqueryCurrentLe : get_current_store_epoch cfg query.store ≤ eb + 1 := by
    rcases hmechanical.current_or_previous_epoch with hcurrent | hprevious
    · have heq : eb = get_current_store_epoch cfg query.store := by
        simpa only [eb, hresult] using hcurrent
      rw [← heq]
      exact Nat.le_succ eb
    · have heq : eb + 1 = get_current_store_epoch cfg query.store := by
        simpa only [eb, hresult] using hprevious
      exact heq.ge
  obtain ⟨seed, hseed, hseedGlc', havailable⟩ :
      ∃ seed : Root,
        seed ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root seed) (get_node_for_root glc) = true ∧
        SourceAvailableAtTip cfg (E.store cfg ext w m) seed := by
    by_cases hearly : get_current_store_epoch cfg (E.store cfg ext w m) < eb + 2
    · obtain ⟨seed, hseed, hseedGlc, hrecent⟩ :=
        hrealization.initial_source_recency hprovisos
          w hw m hslotQM hHm (by simpa only [eb, hresult] using hearly)
      exact ⟨seed, hseed, by simpa only [hresult] using hseedGlc,
        Or.inr hrecent⟩
    · have hlate : eb + 2 ≤
          get_current_store_epoch cfg (E.store cfg ext w m) :=
        Nat.le_of_not_gt hearly
      have hcanon : E.SelectedCanonicalBeforeEndpointAt cfg ext q glc m := hIH
      have hsem : E.SelectedA32SemanticRealizationAt cfg ext anchor
          ffg_state v q glc eb := by
        simpa only [eb, hresult] using
          hrealization.a32_semantics hprovisos
            w hw m hslotQM hHm
              (by simpa only [eb, hresult] using hlate)
              (by simpa only [hresult] using hcanon)
      have hboundary : compute_start_slot_at_epoch cfg (eb + 2) ≤
          E.slot_at cfg m := by
        have hepoch : eb + 2 ≤
            compute_epoch_at_slot cfg (E.slot_at cfg m) := by
          simpa only [get_current_store_epoch,
            E.store_current_slot cfg ext w m] using hlate
        simpa only [compute_start_slot_at_epoch] using
          (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hepoch
      have hglcExec : glc ∈ (E.store cfg ext v q).block_roots := by
        simpa only [hrealization.query_store_eq] using hglcQ
      have hbe : get_block_epoch cfg (E.store cfg ext v q) glc ≤ eb := by
        simpa only [eb, ← hrealization.query_store_eq] using
          (Nat.le_refl eb)
      have hsemBound := hsem
      obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
      obtain ⟨seed, hincluded⟩ : ∃ seed : Root,
          A32IncludedAtTip cfg (E.store cfg ext w m) eb glc seed := by
        rcases hsem with hearlyAU | ⟨hpaperCanonical, hpaperSupport⟩
        · obtain ⟨carrier, hcarrierKnown, hcarrierGlc,
              hcarrierEpoch, hcarrierAU⟩ := hearlyAU
          let seed := carrier
          have hqEpoch : compute_epoch_at_slot cfg (E.slot_at cfg q) =
              get_current_store_epoch cfg query.store := by
            simp only [get_current_store_epoch,
              hrealization.query_store_eq, E.store_current_slot cfg ext v q]
          have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
              get_current_store_epoch cfg (E.store cfg ext w m) := by
            simp only [get_current_store_epoch,
              E.store_current_slot cfg ext w m]
          have hepochQM : compute_epoch_at_slot cfg (E.slot_at cfg q) <
              compute_epoch_at_slot cfg (E.slot_at cfg m) := by
            rw [hqEpoch, hmEpoch]
            exact (hqueryCurrentLe.trans_lt
              (Nat.lt_succ_self (eb + 1))).trans_le hlate
          have hslotQMStrict : E.slot_at cfg q < E.slot_at cfg m := by
            by_contra hnot
            have hslotLe : E.slot_at cfg m ≤ E.slot_at cfg q :=
              Nat.le_of_not_gt hnot
            have hmono : compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
                compute_epoch_at_slot cfg (E.slot_at cfg q) := by
              simp only [compute_epoch_at_slot]
              exact Nat.div_le_div_right hslotLe
            exact (Nat.not_lt_of_ge hmono) hepochQM
          have hrelayGate : E.slot_at cfg q + 1 ≤
              E.slot_at cfg (m + 1) :=
            (Nat.succ_le_of_lt hslotQMStrict).trans
              (E.slot_at_mono cfg (Nat.le_succ m))
          have hseed : seed ∈ (E.store cfg ext w m).block_roots :=
            hA.synchrony.block_relay v hv q seed hqH
              hcarrierKnown w hw m hHm hrelayGate
          have hglcM : glc ∈ (E.store cfg ext w m).block_roots :=
            hglcKnown w hw m
              (E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM)
              hHm
          have hseedGlc : is_ancestor (E.store cfg ext w m)
              (get_node_for_root seed) (get_node_for_root glc) = true := by
            exact E.store_ancestor_of_rootDescends_for_storeReflection
              cfg ext hA.wellFormed
              hA.externals_coherence hgenEq hanchorSlot hanchorParent
              hseed hglcM
              hcarrierGlc
          have hseedBlocks :
              (E.store cfg ext v q).blocks seed =
                (E.store cfg ext w m).blocks seed :=
            hA.wellFormed.blocks_agree
              (E.blockProvenance cfg ext v q)
              (E.blockProvenance cfg ext w m)
              hcarrierKnown hseed
          have hseedEpoch : get_block_epoch cfg (E.store cfg ext w m) seed <
              eb + 2 := by
            simp only [get_block_epoch]
            rw [← hseedBlocks]
            exact hcarrierEpoch
          exact ⟨seed, E.a32IncludedAtTip_of_existing_AU cfg ext
            hrealization.transition_coherence hseed hseedGlc hseedEpoch
            hcarrierAU⟩
        · obtain ⟨seed, hincluded⟩ :=
            E.a32IncludedAtTip_of_paper_at_known cfg ext
              hrealization.transition_coherence hrealization.paper_a32
              hglcExec hbe hpaperCanonical hpaperSupport hw hHm hboundary
          exact ⟨seed, hincluded⟩
      have hJBound : (E.store cfg ext w m).justified_checkpoint.epoch ≤ eb := by
        have hpreBound :
            E.PreQueryTargetOriginAt cfg ext anchor q w m →
              (E.store cfg ext w m).justified_checkpoint.epoch ≤ eb := by
          intro hpreOrigin
          simpa only [eb, hresult] using
            hrealization.pre_query_later_justified_epoch_bound hprovisos
              w hw m hslotQM hHm
              (by simpa only [eb, hresult] using hlate)
              (by simpa only [hresult] using hcanon)
              (by simpa only [eb, hresult] using hsemBound)
              (by simpa only [hresult] using hglcJ)
              (by simpa only [hresult] using hnotGlc)
              hpreOrigin
        rcases horigin with hanchor | htargetOrigin
        · exact hpreBound (Or.inl hanchor)
        · obtain ⟨i, hi, s, k, a, hs0, hsm, hsH, hvote, htarget⟩ :=
            htargetOrigin
          by_cases hqs : E.slot_at cfg q ≤ s
          · exact E.query_justified_epoch_le_of_causal_honest_target_minimal
              cfg ext hA hwalkDomain hrealization.query_store_eq hw hHm
              hglcQ hglcKnown hIH hi hqs hsm hsH hvote htarget hnotGlc
          · exact hpreBound (Or.inr
              ⟨i, hi, s, k, a, hs0, Nat.lt_of_not_ge hqs, hsm, hsH,
                hvote, htarget⟩)
      have hincluded' : A32IncludedAtTip cfg (E.store cfg ext w m)
          eb glc seed := by
        simpa only [eb, hresult] using hincluded
      exact ⟨seed, hincluded'.seed_known,
        hincluded'.seed_descends_selected,
        Or.inl (hincluded'.sourceVisible cfg hlate hJBound)⟩
  have hseedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed) (get_node_for_root c) = true :=
    is_ancestor_trans hwfM
      (hwalkM c hcM seed hseed)
      (hwalkM c hcM glc (hglcKnown w hw m
        (E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM) hHm))
      hseedGlc' hglcC_M
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hknownNonfuture : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).slot ≤
        get_current_slot cfg (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hanchorSlot⟩ w m
  have hacc : CertificateAccountability cfg E anchor :=
    CertificateAccountability.of_assumptions cfg ext
      (SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA)
  obtain ⟨hplace, hfresh⟩ :=
    retainedFilterTipPlacement_of_available_seed cfg hacc
      (hrealization.endpoint w hw m hHm)
      (hrealization.selector w hw m hHm)
      (hrealization.finalized_boundary w hw m hHm)
      (hrealization.source_epoch_persistence w hw m hHm)
      hwfM hwalkM hknownNonfuture hcM hseed hseedC hcJ havailable
  obtain ⟨hskel, htip⟩ :=
    SelectedFilterChainGeometry.exists_filterTipSkeleton_of_placement cfg
      hwfM hwalkM
      (hrealization.endpoint w hw m hHm).justified_root_known
      hcM hnotCovered hplace
  have hfresh' : TipSourceFresh cfg (E.store cfg ext w m) hskel.tip := by
    rw [htip]
    exact hfresh
  exact ⟨filterTipCertificate_of_pipeline cfg hacc
    (hrealization.endpoint w hw m hHm) hskel hfresh'⟩

/-- Direct executable filter membership for the child of a strict selected
edge, obtained from the non-circular state realization. -/
theorem child_filtered_of_selectedTraceFFGStateRealization_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {r₀ glc a c : Root}
    (hresult : find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hr₀ : r₀ ∈ query.store.block_roots)
    (hr₀Epoch :
      get_block_epoch cfg query.store r₀ =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store r₀ + 1 =
          get_current_store_epoch cfg query.store)
    (hstrict : glc ≠ r₀)
    (hrealization : E.SelectedTraceFFGStateRealizationAt cfg ext anchor
      v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    ForkChoiceNode.mk c ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) := by
  exact child_filtered_of_filterTipCertificate_nonempty cfg
    (E.filterTipCertificate_of_selectedTraceFFGStateRealization_minimal
      cfg ext hA hwalkDomain hv hqH hresult hr₀ hr₀Epoch hstrict
      hrealization hprovisos
      hw hslotQM hHm hcM hglcC_M hglcKnown hIH hnotCovered)
    hparentM

end Execution

end FastConfirmation.Spec

end
